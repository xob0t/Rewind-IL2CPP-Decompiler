// Modified by xob0t (2026): float arguments of native calls, slot-specialized invokers, offset-0 field addresses, gaps always marked, small structs as numbers, floating-point negation, inlined compare-exchange on references, one virtual method through nested merges, objects copied into a merge before their constructor runs. See FORK.md.
using Rewind.Analysis.Abi;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Runtime;
using Rewind.Analysis.X64;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    // ---- argument access ---------------------------------------------------------------------------------------

    private static Node? Input(Node call, ArgSlotKind kind, int index)
    {
        var info = (CallInfo)call.Aux!;
        for (int i = 0; i < info.Slots.Count && i < call.In.Length; i++)
            if (info.Slots[i].Kind == kind && info.Slots[i].Index == index)
                return call.In[i];
        return null;
    }

    /// <summary>The value passed in argument position <paramref name="position"/> when it is an integer/pointer.</summary>
    private Node? IntAt(Node call, int position) =>
        _fn.Regs.IsStackPosition(position) ? Input(call, ArgSlotKind.Stack, _fn.Regs.StackSlotOf(position))
        : _fn.Regs.IntRegisterOf(position) is int r and >= 0 ? Input(call, ArgSlotKind.IntReg, r) : null;

    private static readonly bool NoDoubleHalves = Environment.GetEnvironmentVariable("REWIND_NO_DOUBLE_HALVES") != null;

    private HExpr FloatAt(Node call, int position, bool isDouble)
    {
        TypeSig type = isDouble ? _double : _float;
        if (_fn.Regs.IsStackPosition(position))
        {
            Node? slot = Input(call, ArgSlotKind.Stack, _fn.Regs.StackSlotOf(position));
            if (slot == null) return Missing(type);
            // A float occupies the low half of its stack slot. What fills the rest - what the slot held before,
            // or the widening of a value read as 32 bits - is not part of it and is not looked at.
            if (!isDouble && !NoUnreadHalves)
            {
                if (slot.Op == Op.Concat) slot = slot.In[1];
                else if (slot.Op is Op.ZExt or Op.SExt && slot.In[0].Type == VT.I32 && !_materialize.Contains(slot) && !_sem.ContainsKey(slot)) slot = slot.In[0];
            }
            Sem s = Eval(slot);
            if (s is SPair pair)
            {
                // A float occupies the low half of its stack slot; a double, both halves.
                if (!isDouble || NoDoubleHalves) return AsFloat(pair.Low, type);
                return ValueFromBits(CombineParts([new Part(0, 4, pair.Low), new Part(4, 4, pair.High)], 8), _double, 8);
            }
            if (s is SVal v) return AsFloat(v.Expr, type);
            return AsFloat(Value(slot), type);
        }
        int register = _fn.Regs.FloatRegisterOf(position);
        if (!_fn.Regs.SharedPositions)
            return FloatFromLanes(Input(call, ArgSlotKind.FloatReg, register * 4), isDouble ? Input(call, ArgSlotKind.FloatReg, register * 4 + 1) : null, isDouble);
        Node? lo = Input(call, ArgSlotKind.FloatReg, register * 4);
        if (lo == null) return Missing(type);
        if (!isDouble) return AsFloat(FloatValue(lo), type);
        Node? hi = Input(call, ArgSlotKind.FloatReg, register * 4 + 1);
        if (Eval(lo) is SHalf { High: false } l && hi != null && Eval(hi) is SHalf { High: true } h && ReferenceEquals(l.Whole, h.Whole))
            return l.Whole;
        if (hi != null && SignedLanes(lo, hi) is { } signed) return signed;
        if (Eval(lo) is SVal { Expr: HConst { Value: int low } } && hi != null && Eval(hi) is SVal { Expr: HConst { Value: int high } })
            return new HConst(BitConverter.Int64BitsToDouble((long)(uint)high << 32 | (uint)low), _double);
        HExpr bits = CombineParts([new Part(0, 4, HalfBits(lo)), new Part(4, 4, hi != null ? HalfBits(hi) : new HConst(0, _int))], 8);
        return ValueFromBits(bits, _double, 8);
    }

    /// <summary>
    /// A float argument is a float whatever register its bits travelled through: a value the recovery knows only
    /// as an integer (a constant moved into the vector register, a merged general register) is its bit pattern.
    /// </summary>
    private HExpr AsFloat(HExpr e, TypeSig type)
    {
        TypeSig? have = e.Type ?? (e as HLocal)?.Variable.Type;
        if (have == null || IsFloat(have)) return e;
        // A float in a 64-bit slot is the bit pattern in the slot's low half, not a number to convert.
        if (ReferenceEquals(type, _float) && (ReferenceEquals(have, _long) || ReferenceEquals(have, _ulong)) && e is not HConst && !NoUnreadHalves)
            return ValueFromBits(new HConv(HConvKind.I4, e) { Type = _int }, _float, 4);
        return Coerce(e, type);
    }

    private HExpr Missing(TypeSig type)
    {
        Problem("call argument was not captured");
        return Site(new HOpaque("missing_argument") { Type = type }, "call argument was not captured");
    }

    private Dictionary<int, Node> Projections(Node call)
    {
        var result = new Dictionary<int, Node>();
        List<Node> nodes = call.Block!.Nodes;
        for (int i = _position[call] + 1; i < nodes.Count && nodes[i].Op == Op.Proj && ReferenceEquals(nodes[i].In[0], call); i++)
            result[(int)nodes[i].Imm] = nodes[i];
        return result;
    }

    private bool IsUsed(Node n) => _uses.TryGetValue(n, out List<Node>? uses) && uses.Count != 0;

    // ---- frame object types ------------------------------------------------------------------------------------

    private bool IsFrameAddress(Node n, out int offset)
    {
        offset = 0;
        if (!_fn.Params.TryGetValue(_fn.Regs.StackPointer, out Node? sp0)) return false;
        if (ReferenceEquals(n, sp0)) return true;
        if (n.Op == Op.Add && ReferenceEquals(n.In[0], sp0) && n.In[1].IsConst)
        {
            offset = (int)IrBuilder.SImm(n.In[1]);
            return true;
        }
        return false;
    }

    private static readonly bool NoWiderPointees = Environment.GetEnvironmentVariable("REWIND_NO_WIDER_POINTEES") != null;

    /// <summary>Whether the method called takes an unmanaged pointer (not a reference) at this position.</summary>
    private bool PointerParameterAt(CallInfo info, int position)
    {
        if (info.Indirect) return false;
        static bool At(MethodAbi abi, int position) => abi.Params.Any(p => p.Position == position && p.Role == ParamRole.Argument && p.Type is PointerSig);
        CallTarget target = _p.Resolve(info.Target);
        foreach (MethodDef m in target.Methods.Take(8))
            if (At(_p.Abi.For(m, [], []), position)) return true;
        foreach (MethodInst inst in target.Insts.Take(8))
            if (At(_p.Abi.For(inst), position)) return true;
        return false;
    }

    /// <summary>Whether the code reads or writes the stack at <paramref name="offset"/> itself, in more than <paramref name="size"/> bytes at once.</summary>
    private bool WiderAccessAt(int offset, int size) => DirectAccessSize(offset) > size;

    /// <summary>The widest read or write of the stack at exactly <paramref name="offset"/> (-1: none).</summary>
    private int DirectAccessSize(int offset)
    {
        int widest = -1;
        foreach (Block b in _fn.Blocks)
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op is not (Op.Load or Op.Store)) continue;
                int bytes = n.Op == Op.Load ? n.Type.Bytes() : n.In[1].Type.Bytes();
                if (bytes > widest && IsFrameAddress(n.In[0], out int at) && at == offset) widest = bytes;
            }
        return widest;
    }

    private static TypeSig? PointeeOf(MethodAbi abi, int position)
    {
        foreach (AbiParam p in abi.Params)
        {
            if (p.Position != position) continue;
            if (p.Role == ParamRole.ReturnBuffer) return abi.ReturnType;
            if (p.Pass == PassKind.Indirect) return p.Type;
            if (p.Type is ByRefSig byRef) return byRef.ElementType;
            if (p.Type is PointerSig pointer && !pointer.ElementType.IsVoid) return pointer.ElementType;
            if (p.Role == ParamRole.This && p.Type?.Definition is { IsValueType: true }) return p.Type;
        }
        return null;
    }

    /// <summary>
    /// To call a method of Object, ValueType or Enum on a value (rule.ToString() on an enum, say), generated
    /// code does not allocate a box: it writes an object header - the class and a mark meaning "not a real
    /// object" - right in front of a copy of the value on the stack, and passes the address of that. In
    /// managed terms the address is the boxed value.
    /// </summary>
    private void FindFakeBoxes()
    {
        Dictionary<int, TypeSig>? classes = null;
        HashSet<int>? marks = null;
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op != Op.Store || !IsFrameAddress(n.In[0], out int offset)) continue;
                Node value = n.In[1];
                if (value.Op == Op.SlotValue)
                {
                    if (EvalKlass(value) is { IsValueType: true } type) (classes ??= [])[offset] = type;
                }
                else if (value.IsConst && value.Type == VT.I64 && value.Imm == -1) (marks ??= []).Add(offset);
            }
        }
        // The same, done by the runtime's constructor: Il2CppFakeBox<T>(box, klass, &value).
        foreach (Block b in _fn.Blocks)
            foreach (Node n in b.Nodes)
                if (!n.Dead && n.Op == Op.Call && n.Aux is CallInfo { Indirect: false, Intrinsic: null } ci &&
                    _p.Helpers.KindAt(ci.Target) == HelperKind.FakeBoxInit && IntAt(n, 0) is { } box && IsFrameAddress(box, out int at) &&
                    IntAt(n, 1) is { } klass && EvalKlass(klass) is { IsValueType: true } boxed)
                {
                    _fakeBoxes[at] = boxed;
                    _frameTypes[at + _header] = boxed;
                }
        if (classes == null || marks == null) return;
        foreach (var (offset, type) in classes)
        {
            if (!marks.Contains(offset + _ptr)) continue;
            _fakeBoxes[offset] = type;
            _frameTypes[offset + _header] = type;
        }
    }

    /// <summary>
    /// Stack memory handed to a call takes its type from what the callee expects there: a struct receiver, a
    /// by-reference argument, a struct passed or returned through a hidden pointer, a value being boxed.
    /// </summary>
    private void InferFrameTypes()
    {
        Dictionary<int, TypeSig?>? parked = NoParkedStructs ? null : ParkedStructParameters();
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node call in b.Nodes)
            {
                if (call.Dead || call.Op is not (Op.Call or Op.TailCall) || call.Aux is not CallInfo info || info.Intrinsic != null) continue;
                for (int i = 0; i < call.In.Length && i < info.Slots.Count; i++)
                {
                    // (One call reached from several paths, each with a stack object of its own to hand over:
                    // the address is merged, and each of the objects is what the call takes there.)
                    List<int>? merged = null;
                    bool mixed = false;
                    if (!IsFrameAddress(call.In[i], out int offset))
                    {
                        if (NoMergedAddresses || !MergedAddresses) continue;
                        if ((merged = MergedFrameAddresses(call.In[i])) == null)
                        {
                            // (Stack memory on some ways in, something else on others, a field say, or the same
                            // stack memory on every way: the stack memory is what the call takes there all the same.)
                            if (NoMixedMerges || (merged = FrameAddressesAmong(call.In[i])) == null) continue;
                            mixed = true;
                        }
                        offset = merged[0];
                    }
                    ArgSlot slot = info.Slots[i];
                    int position = slot.Kind == ArgSlotKind.IntReg ? slot.Index : slot.Kind == ArgSlotKind.Stack ? slot.Index + _fn.Regs.FirstStackPosition : -1;
                    if (position < 0) continue;
                    TypeSig? type = null;
                    if (!info.Indirect)
                    {
                        CallTarget target = _p.Resolve(info.Target);
                        if (target.Helper is { } helper && !target.IsManaged)
                        {
                            if (helper.Kind == HelperKind.Box && position == 1 && IntAt(call, 0) is { } k) type = EvalKlass(k);
                            else if (helper.Kind is HelperKind.UnboxAny or HelperKind.UnboxNullable && position == 2 && IntAt(call, 1) is { } k2) type = EvalKlass(k2);
                        }
                        else
                        {
                            if (NoReachableAssemblies)
                            {
                                foreach (MethodDef m in target.Methods)
                                    if ((type = PointeeOf(_p.Abi.For(m, [], []), position)) != null) break;
                                if (type == null)
                                    foreach (MethodInst inst in target.Insts)
                                        if ((type = PointeeOf(_p.Abi.For(inst), position)) != null) break;
                            }
                            else
                            {
                                // Of the methods that share the code, only those this code could call say anything:
                                // the first of them that takes a pointer there, where few do. Where more do (an empty
                                // function serves thousands of methods), the first is a guess unless they all say the
                                // same; which was called is then decided with the call, and the type with it.
                                var pointees = new List<TypeSig>();
                                bool differ = false;
                                int wanted = SharedPointeeLimit == int.MaxValue ? 1 : 64;
                                void Add(TypeSig t)
                                {
                                    if (pointees.Count != 0 && !ReferenceEquals(t, pointees[0]) && t.Key != pointees[0].Key) differ = true;
                                    pointees.Add(t);
                                }
                                foreach (MethodDef m in target.Methods)
                                    if (pointees.Count < wanted && Reachable(m.DeclaringType.Assembly) && PointeeOf(_p.Abi.For(m, [], []), position) is { } t)
                                        Add(t);
                                foreach (MethodInst inst in target.Insts)
                                    if (pointees.Count < wanted && Reachable(inst.Method.DeclaringType.Assembly) && PointeeOf(_p.Abi.For(inst), position) is { } t)
                                        Add(t);
                                if (pointees.Count != 0 && (pointees.Count <= SharedPointeeLimit || !differ)) type = pointees[0];
                                // Methods of several structs share the code: the one whose struct was put there
                                // is the one that is called.
                                if (differ && parked != null && parked.TryGetValue(offset, out TypeSig? held) && held != null &&
                                    pointees.Any(t => t.Key == held.Key))
                                    type = held;
                            }
                        }
                    }
                    if (type == null || Open(type) || !Nameable(type)) continue;
                    // "(byte*)&local": a pointer handed on to memory the code itself reads or writes in wider
                    // pieces is a view of it, not what it is.
                    if (merged == null && !NoWiderPointees && PointerParameterAt(info, position) && WiderAccessAt(offset, _p.Layouts.SizeOf(type).Size)) continue;
                    if (merged == null)
                    {
                        // (One call takes a struct there, another a different struct: the memory holds one object,
                        // then another - a Vector3 for one call, a Quaternion for the next. Each its own lifetime.)
                        _frameTypes.TryAdd(offset, type);
                    }
                    else
                    {
                        foreach (int at in merged)
                        {
                            // (Known as something else already: the memory is used for two things, one after the other.)
                            if (!_frameTypes.TryAdd(at, type) && _frameTypes[at].Key != type.Key) FrameConflicts.Add(at);
                        }
                        if (mixed) continue;
                        Node phi = call.In[i];
                        _addressPhis[phi] = _addressPhis.TryGetValue(phi, out TypeSig? other) && (other == null || other.Key != type.Key) ? null : type;
                    }
                }
            }
        }
        SpreadFrameTypes();
        DropCoveredFrameTypes();
    }

    private static readonly bool NoMergedAddresses = Environment.GetEnvironmentVariable("REWIND_NO_MERGED_ADDRESSES") != null;
    private static readonly bool MergedTrace = Environment.GetEnvironmentVariable("REWIND_MERGED_TRACE") != null;

    /// <summary>
    /// Merged values that are the address of one stack object or another, by the way they are reached, with
    /// what those objects are (null: handed to calls that take different things). Such a value is a reference
    /// variable: "ref T m = ref a" on one path, "ref b" on the other.
    /// </summary>
    private readonly Dictionary<Node, TypeSig?> _addressPhis = [];

    /// <summary>The stack offsets a merged value is the address of, one per way in, when it is nothing else and they are not all one.</summary>
    private List<int>? MergedFrameAddresses(Node n)
    {
        if (n.Op != Op.Phi || n.In.Length < 2 || n.In.Length > 8) return null;
        var offsets = new List<int>(n.In.Length);
        foreach (Node input in n.In)
        {
            if (!IsFrameAddress(input, out int at)) return null;
            offsets.Add(at);
        }
        return offsets.Distinct().Count() > 1 ? offsets : null;
    }

    private static readonly bool NoMixedMerges = Environment.GetEnvironmentVariable("REWIND_NO_MIXED_MERGES") != null;

    /// <summary>
    /// The stack offsets among a merged value's ways in, when some of them are stack addresses and the others
    /// something else (a field's address), or when they are all the same stack address.
    /// </summary>
    private List<int>? FrameAddressesAmong(Node n)
    {
        if (n.Op != Op.Phi || n.In.Length < 2 || n.In.Length > 8) return null;
        var offsets = new List<int>(n.In.Length);
        foreach (Node input in n.In)
            if (IsFrameAddress(input, out int at) && !offsets.Contains(at))
                offsets.Add(at);
        return offsets.Count != 0 ? offsets : null;
    }

    /// <summary>The type a merged stack address points to, when every object it may be the address of is known as that.</summary>
    private TypeSig? MergedPointee(Node phi)
    {
        if (!_addressPhis.TryGetValue(phi, out TypeSig? pointee) || pointee == null) return null;
        foreach (Node input in phi.In)
            if (!IsFrameAddress(input, out int at) || MergedPlace(at, pointee) == null)
            {
                if (MergedTrace) Console.Error.WriteLine($"[merged] %{phi.Id}: no {pointee.ShortName} at {(IsFrameAddress(input, out int where) ? where : 0)} (known there: {(_frameTypes.TryGetValue(where, out TypeSig? t) ? t.ShortName : FrameObjectAt(where) is int e ? "inside " + _frameTypes[e].ShortName + " at " + e : "nothing")})");
                return null;
            }
        return pointee;
    }

    /// <summary>The stack object of the given type at a stack offset: a local of that type, or a field of that type of a struct local.</summary>
    private HExpr? MergedPlace(int at, TypeSig pointee)
    {
        if (_frameTypes.TryGetValue(at, out TypeSig? held) && held.Key == pointee.Key)
            return FramePlace(at, -1) is PLocation whole && whole.Type.Key == pointee.Key ? whole.Location : null;
        if (FrameObjectAt(at) is not int enclosing || !IsStructType(_frameTypes[enclosing])) return null;
        if (_p.Layouts.SizeOf(pointee) is not { Known: true, Size: > 0 } size) return null;
        return FramePlace(at, size.Size) is PLocation field && field.Type.Key == pointee.Key ? field.Location : null;
    }

    private static readonly bool NoParkedStructs = Environment.GetEnvironmentVariable("REWIND_NO_PARKED_STRUCTS") != null;

    /// <summary>
    /// A struct that came in a register has no address: before one of its methods can be called on it, the code
    /// stores it on the stack. Those bytes then hold that struct, whatever else the code that is called there
    /// could be run on. Stack offset to the struct parameter stored there whole (null: more than one kind).
    /// </summary>
    private Dictionary<int, TypeSig?> ParkedStructParameters()
    {
        var found = new Dictionary<int, TypeSig?>();
        foreach (Block b in _fn.Blocks)
            foreach (Node store in b.Nodes)
            {
                if (store.Dead || store.Op != Op.Store || !IsFrameAddress(store.In[0], out int offset)) continue;
                Node value = store.In[1];
                int bytes = value.Type.Bytes();
                while (value.Op == Op.Trunc) value = value.In[0];
                if (!_sem.TryGetValue(value, out Sem? s) || s is not SVal { Expr: HArg { Type: { } type } } || !IsStructType(type) || Open(type) || !Nameable(type))
                    continue;
                if (_p.Layouts.SizeOf(type) is not { Known: true } size || size.Size != bytes) continue;
                found[offset] = found.TryGetValue(offset, out TypeSig? other) && (other == null || other.Key != type.Key) ? null : type;
            }
        return found;
    }

    /// <summary>
    /// Stack memory typed from a call on a field of a struct local ("machine.builder.Start(ref machine)" types
    /// both the machine and, inside it, the builder) is one object, the struct: the inner type is the type of
    /// the struct's field at that place and adds nothing. Types that do not agree with the field stay - that is
    /// memory used for two things.
    /// </summary>
    private void DropCoveredFrameTypes()
    {
        if (_frameTypes.Count < 2) return;
        foreach (var (inner, innerType) in _frameTypes.ToList())
        {
            if (_fakeBoxes.ContainsKey(inner - _header)) continue;
            foreach (var (outer, outerType) in _frameTypes)
            {
                if (outer >= inner || !IsStructType(outerType) || Open(outerType)) continue;
                if (inner >= outer + _p.Layouts.SizeOf(outerType).Size) continue;
                TypeSig type = outerType;
                int offset = inner - outer;
                bool covered = false;
                for (int depth = 0; depth < 8; depth++)
                {
                    if (_p.Layouts.FieldAt(type, offset) is not { } slot) break;
                    if (slot.Offset == offset && (slot.Type.Key == innerType.Key || (IsReference(slot.Type) && IsReference(innerType))))
                    {
                        covered = true;
                        break;
                    }
                    if (!IsStructType(slot.Type)) break;
                    offset -= slot.Offset;
                    type = slot.Type;
                }
                if (!covered) continue;
                _frameTypes.Remove(inner);
                break;
            }
        }
    }

    private static readonly bool NoFirstFields = Environment.GetEnvironmentVariable("REWIND_NO_FIRST_FIELDS") != null;

    /// <summary>
    /// A struct's address is also the address of its first field (and of that field's first field): where
    /// something of the field's type is wanted there ("Value.ToString()" called with the address of the
    /// struct that holds it), the location is that field. Unchanged when no field at the start is of exactly
    /// that type.
    /// </summary>
    private HExpr AtStart(HExpr location, TypeSig? held, TypeSig? expected)
    {
        if (NoFirstFields || held == null || expected == null || Open(expected) || held.Key == expected.Key) return location;
        int wanted = _p.Layouts.SizeOf(expected).Size;
        HExpr current = location;
        TypeSig type = held;
        for (int depth = 0; depth < 8 && IsStructType(type) && !Open(type); depth++)
        {
            // (In a union, the field of the wanted size is the one meant.)
            FieldSlot? first = _p.Layouts.FieldExactly(type, 0, wanted) is { } exact && exact.Type.Key == expected.Key ? exact : _p.Layouts.FieldAt(type, 0);
            if (first is not { Offset: 0 } slot) break;
            current = new HField { Object = current, Field = slot.Field, DeclaringType = type, Type = slot.Type };
            type = slot.Type;
            if (type.Key == expected.Key) return current;
        }
        return location;
    }

    /// <summary>The storage location a pointer argument refers to.</summary>
    private HExpr? LocationOf(Node pointer, TypeSig? expected)
    {
        // (What the code cannot name says nothing about its stack.)
        if (!Nameable(expected)) expected = null;
        Sem s = Eval(pointer);
        switch (s)
        {
            case SRef r:
                return AtStart(r.Location, r.Type, expected);
            case SFrame f when BufferAddress(f.Offset) is { } buffer:
            {
                // In a stackalloc'd buffer: what the pointer points at.
                TypeSig at = expected != null && !Open(expected) ? expected : _byte;
                HExpr into = ReferenceEquals(at, _byte) ? buffer : new HConv(HConvKind.U, buffer) { Type = _m.Sigs.Pointer(at) };
                return new HDeref(into) { Type = at };
            }
            case SFrame f:
            {
                // An address inside a struct local is the address of one of its fields (or of the fields that
                // start there): nothing new is learned about the stack.
                if (!_frameTypes.ContainsKey(f.Offset) && FrameObjectAt(f.Offset) is int enclosing && IsStructType(_frameTypes[enclosing]))
                {
                    int wanted = expected != null && !Open(expected) ? _p.Layouts.SizeOf(expected).Size : -1;
                    if (FramePlace(f.Offset, wanted) is PLocation field &&
                        (expected == null || wanted < 0 || _p.Layouts.SizeOf(field.Type).Size == wanted))
                        return field.Location;
                }
                if (expected != null && !_frameTypes.ContainsKey(f.Offset))
                {
                    _frameTypes[f.Offset] = expected;
                    // Learned only now: statements already translated may have treated these bytes as loose
                    // slots. Building again with the type known from the start puts them in one variable.
                    if (!Open(expected))
                    {
                        RefinedFrameTypes[f.Offset] = expected;
                        FrameTypesRefined = true;
                    }
                }
                if (expected != null && !Open(expected))
                {
                    if (!_frameVotes.TryGetValue(f.Offset, out HashSet<TypeSig>? votes)) _frameVotes[f.Offset] = votes = [];
                    votes.Add(expected);
                }
                // (Nothing says what is there: as wide as the code itself reads or writes it, not a guess.)
                int width = expected == null && !NoWiderPointees && !_frameTypes.ContainsKey(f.Offset) ? DirectAccessSize(f.Offset) : -1;
                return FramePlace(f.Offset, width) is PLocation loc ? loc.Location : null;
            }
            case SStatics statics:
            {
                // The address of a class's static data is the address of its first static field.
                TypeDef? owner = statics.Type.Definition;
                FieldDef? first = owner?.Fields.FirstOrDefault(f => f.IsStatic && !f.IsLiteral && f.Offset == 0);
                if (first == null) return null;
                TypeSig fieldType = statics.Type is GenericInstSig generic ? _m.Sigs.Substitute(first.Type, generic.Arguments, []) : first.Type;
                return new HField { Object = null, Field = first, DeclaringType = statics.Type, Type = fieldType };
            }
            case SVal { Type: ByRefSig byRef } v:
                return AtStart(new HDeref(v.Expr) { Type = byRef.ElementType }, byRef.ElementType, expected);
            case SVal { Type: PointerSig pointerType } v:
                return AtStart(new HDeref(v.Expr) { Type = pointerType.ElementType }, pointerType.ElementType, expected);
            default:
                return null;
        }
    }

    // ---- results -----------------------------------------------------------------------------------------------

    /// <summary>
    /// A struct made from a value of another type: a struct that is one number, from that number ("new
    /// Handle32(value)", its explicit conversion pasted in); anything else is marked.
    /// </summary>
    private HExpr StructOfValue(HExpr e, TypeSig structType, ulong addr)
    {
        TypeLayout layout = _p.Layouts.Of(structType);
        if (layout.Known && layout.Fields.Length == 1 && layout.Fields[0] is { Offset: 0 } only && only.Size == layout.Size &&
            only.Type is PrimitiveSig or { Definition.IsEnum: true } && !IsFloat(only.Type) && !IsFloat(e.Type) &&
            (e.Type is PrimitiveSig or { Definition.IsEnum: true }) && !IsReference(e.Type) && BitsOf(e.Type) == BitsOf(only.Type))
        {
            HVar temp = _h.NewLocal(structType, "s");
            temp.AddressTaken = true;
            Emit(new HAssign(new HField { Object = new HLocal(temp) { Type = structType }, Field = only.Field, DeclaringType = structType, Type = only.Type }, e), addr);
            return new HLocal(temp) { Type = structType };
        }
        string problem = $"could not rebuild {structType.DisplayName} from a {e.Type?.DisplayName ?? "value"}";
        Problem(problem);
        return Site(new HOpaque("struct_from_value", e) { Type = structType }, problem);
    }

    private void FinishCall(Node call, HExpr expr, ReturnKind kind, TypeSig returnType, bool tail)
    {
        expr.Type ??= returnType;
        if (tail)
        {
            if (kind == ReturnKind.Void || _abi.Return == ReturnKind.Void)
            {
                Emit(new HEval(expr), call.Addr);
                Emit(new HReturn(null), call.Addr);
            }
            else
            {
                // A struct returned where the call's result is something else (a conversion operator pasted in):
                // the struct made from it.
                if (_abi.ReturnType is { } returned && IsStructType(returned) && expr.Type is { } given && given.Key != returned.Key)
                    expr = StructOfValue(expr, returned, call.Addr);
                Emit(new HReturn(expr), call.Addr);
            }
            return;
        }

        if (kind is ReturnKind.StructInRegisterPair or ReturnKind.FloatAggregate)
        {
            FinishRegisterStruct(call, expr, kind, returnType);
            return;
        }
        Dictionary<int, Node> projs = Projections(call);
        switch (kind)
        {
            case ReturnKind.Void:
                Emit(new HEval(expr), call.Addr);
                break;
            case ReturnKind.Double:
            {
                projs.TryGetValue(CallResult.FloatLane0, out Node? lo);
                projs.TryGetValue(CallResult.FloatLane1, out Node? hi);
                if ((lo != null && IsUsed(lo)) || (hi != null && IsUsed(hi)))
                {
                    HVar t = Temp(_double, VT.F64);
                    Emit(new HAssign(new HLocal(t) { Type = _double }, expr), call.Addr);
                    var whole = new HLocal(t) { Type = _double };
                    if (lo != null) _sem[lo] = new SHalf(whole, false, null);
                    if (hi != null) _sem[hi] = new SHalf(whole, true, null);
                }
                else Emit(new HEval(expr), call.Addr);
                break;
            }
            default:
            {
                int which = kind == ReturnKind.Float ? CallResult.FloatLane0 : CallResult.IntReturn;
                if (!projs.TryGetValue(which, out Node? result) || !IsUsed(result))
                {
                    Emit(new HEval(expr), call.Addr);
                    break;
                }
                if (_materialize.Contains(result) || expr is HOpaque)
                {
                    HVar t = Temp(returnType, result.Type);
                    Emit(new HAssign(new HLocal(t) { Type = t.Type }, expr), call.Addr);
                    _sem[result] = new SVal(new HLocal(t) { Type = t.Type });
                }
                else _sem[result] = new SVal(expr); // folded into its single, immediately following consumer
                break;
            }
        }
    }

    // ---- dispatch ----------------------------------------------------------------------------------------------

    private static readonly bool NoNamedCopies = Environment.GetEnvironmentVariable("REWIND_NO_NAMED_COPIES") != null;

    /// <summary>
    /// A function that no table lists, handed a method's descriptor exactly where that method takes its own: the
    /// compiler writes small methods out a second time next to their callers, and code shared between
    /// instantiations hands such a copy its descriptor as it would the original. The caller thereby says which
    /// method it means; that the code at the address is that method's is then checked (read as the method, both
    /// must give the same statements).
    /// </summary>
    private CallTarget? NamedCopy(Node call, ulong address)
    {
        // Only in the method asked for: a check started from within another's would start others in turn. (In
        // the reading that a check compares, the function being checked calling itself is the method calling
        // itself.)
        bool own = _p.OwnTranslation && _p.Translations == 1;
        if (!own && !_p.CheckingCopies) return null;
        for (int position = 0; position < _fn.Regs.IntArgs.Length; position++)
        {
            if (IntAt(call, position) is not { } handed || Peek(handed) is not SMethod named) continue;
            MethodAbi abi = named.Inst != null ? _p.Abi.For(named.Inst) : _p.Abi.For(named.Method, [], []);
            if (abi.Params[^1].Position != position) continue;
            if (!(_p.AssumedCopy(address, named.Method) || (own && _p.IsCopyOf(address, named.Method, named.Inst)))) continue;
            _h.Notes.Add($"call target 0x{address:X} is handed the descriptor of {named.Method.FullName} and has the same recovered code: a private copy of it");
            var target = new CallTarget();
            if (named.Inst != null) target.Insts.Add(named.Inst);
            else target.Methods.Add(named.Method);
            return target;
        }
        return null;
    }

    private static readonly bool NoNativeFloatArgs = Environment.GetEnvironmentVariable("REWIND_NO_NATIVE_FLOAT_ARGS") != null;

    /// <summary>
    /// The value in the <paramref name="index"/>th floating-point argument register at a call to a function nothing is
    /// known about, when the method put one there: a double when the register's upper half is set too.
    /// </summary>
    private HExpr? NativeFloatArg(Node call, int index)
    {
        int position = _fn.Regs.SharedPositions ? index : _fn.Regs.FirstFloatPosition + index;
        int register = _fn.Regs.FloatRegisterOf(position);
        if (register < 0 || Input(call, ArgSlotKind.FloatReg, register * 4) is not { } low || Eval(low) is SJunk) return null;
        bool isDouble = Input(call, ArgSlotKind.FloatReg, register * 4 + 1) is { } high && Eval(high) is not SJunk;
        return FloatAt(call, position, isDouble);
    }

    private void EmitCall(Node call, bool tail)
    {
        var info = (CallInfo)call.Aux!;
        if (info.Intrinsic != null)
        {
            EmitIntrinsic(call, info);
            return;
        }
        if (info.Indirect)
        {
            EmitIndirectCall(call, tail);
            return;
        }
        CallTarget target = _p.Resolve(info.Target);
        if (!target.IsManaged && target.Helper == null && InvokerShape(info.Target) is { } invoker)
        {
            EmitHelperCall(call, invoker, tail);
            return;
        }
        if (!target.IsManaged && target.Helper == null && _p.SlotInvokerAt(info.Target) is { } slotInvoker)
        {
            EmitSlotInvokerCall(call, slotInvoker, info.Target, tail);
            return;
        }
        if (!target.IsManaged && target.Helper == null && !NoNamedCopies && NamedCopy(call, info.Target) is { } named) target = named;
        if (target.IsManaged)
        {
            EmitManagedCall(call, target, tail);
            return;
        }
        if (target.Helper != null)
        {
            EmitHelperCall(call, target.Helper, tail);
            return;
        }
        Problem($"call to unidentified native function 0x{info.Target:X}");
        var args = new List<HExpr>();
        for (int i = 0; i < 4; i++)
        {
            bool taken = false;
            if (IntAt(call, i) is { } a && Eval(a) is not SJunk)
            {
                args.Add(Value(a));
                taken = true;
            }
            // A floating-point argument (where the convention gives each position one register or the other: when
            // the general register at its position holds nothing).
            if (!NoNativeFloatArgs && (!taken || !_fn.Regs.SharedPositions) && NativeFloatArg(call, i) is { } f) args.Add(f);
        }
        FinishCall(call, new HOpaque($"native_0x{info.Target:X}", args.ToArray()) { Type = _long }, info.NoReturn ? ReturnKind.Void : ReturnKind.Integer, _long, tail);
        if (info.NoReturn) Emit(new HThrow(new HOpaque("noreturn")), call.Addr);
    }

    /// <summary>
    /// A call of an invoker made for one slot of the class's table (see SlotInvoker): the virtual method in that
    /// slot of the object's class, called on the object with the invoker's arguments moved down one position,
    /// or with the constants the invoker writes in. Where the method or how its arguments arrive is not
    /// recovered, the gap says so and names what is known: the slot and the object.
    /// </summary>
    private void EmitSlotInvokerCall(Node call, Rewind.Analysis.Runtime.SlotInvoker invoker, ulong address, bool tail)
    {
        Node? objectNode = IntAt(call, 1);
        string why;
        if (objectNode != null)
        {
            HExpr receiver = Value(objectNode);
            TypeSig? receiverType = receiver.Type;
            if (_castTypes.TryGetValue(objectNode, out List<TypeSig>? casts) && casts.Count == 1) receiverType = casts[0];
            if (receiverType != null) receiverType = Declared(receiverType);
            MethodDef? method = FindVirtual(receiverType, invoker.Slot);
            if (method == null) why = $"virtual slot {invoker.Slot} not found on {receiverType?.DisplayName ?? "unknown type"}";
            else
            {
                TypeSig[] classArgs = receiverType is GenericInstSig g && ReferenceEquals(g.Definition, method.DeclaringType) ? g.Arguments : [];
                MethodAbi abi = _p.Abi.For(method, classArgs, []);
                if (SlotInvokerConstants(invoker, abi, out why) is { } constants)
                {
                    BuildCall(call, method, classArgs, [], isVirtual: true, tail, null, skipFirst: false, receiverOverride: objectNode, shift: 1,
                        fixedArguments: constants);
                    return;
                }
                why = $"how {method.DeclaringType.Name}.{method.Name} is handed its arguments: {why}";
            }
        }
        else why = "object not captured";
        Problem($"call through vtable slot {invoker.Slot} (invoker 0x{address:X}) not recovered: {why}");
        // (Only the object is known for certain; the other values the invoker was handed are not shown.)
        HExpr[] known = objectNode != null ? [Value(objectNode)] : [];
        FinishCall(call, new HOpaque($"virtual_slot{invoker.Slot}_arguments_unknown", known) { Type = _long }, ReturnKind.Integer, _long, tail);
    }

    /// <summary>
    /// Whether the method's arguments arrive the way the invoker hands them on: each from the invoker's own
    /// argument one position further on, of the same kind, or as a constant it writes in (returned, by
    /// position); its method record right after them. Null, with the reason, when they do not.
    /// </summary>
    private Dictionary<int, long>? SlotInvokerConstants(Rewind.Analysis.Runtime.SlotInvoker invoker, MethodAbi abi, out string why)
    {
        var constants = new Dictionary<int, long>();
        why = "";
        if (!abi.Known)
        {
            why = "signature not known";
            return null;
        }
        int last = -1;
        foreach (AbiParam p in abi.Params)
        {
            last = Math.Max(last, p.Position);
            switch (p.Role)
            {
                case ParamRole.MethodInfo:
                    if (p.Position != invoker.MethodInfoPosition)
                    {
                        why = "a different number of arguments";
                        return null;
                    }
                    continue;
                case ParamRole.This:
                case ParamRole.Argument:
                {
                    if (p.Position >= invoker.MethodInfoPosition)
                    {
                        why = "a different number of arguments";
                        return null;
                    }
                    if (p.Pass is not (PassKind.Integer or PassKind.Float or PassKind.Indirect))
                    {
                        why = "an argument passed in parts";
                        return null;
                    }
                    bool inFloat = p.Pass == PassKind.Float && p.Position < 4;
                    Rewind.Analysis.Runtime.InvokerSource? source = inFloat ? invoker.FloatSources[p.Position] : invoker.IntSources[p.Position];
                    if (source is not { } s)
                    {
                        why = $"argument {p.Position} not handed on";
                        return null;
                    }
                    if (s.IsConstant)
                    {
                        if (p.Role == ParamRole.This || p.Pass == PassKind.Indirect || IsStructType(p.Type) || (IsReference(p.Type) && s.Constant != 0))
                        {
                            why = $"argument {p.Position} a constant of no such type";
                            return null;
                        }
                        constants[p.Position] = s.Constant;
                        continue;
                    }
                    if (s.Position != p.Position + 1)
                    {
                        why = $"argument {p.Position} not the invoker's next";
                        return null;
                    }
                    // (Of the same kind: the invoker's own argument arrived where the method's goes.)
                    if (s.Position < 4 && invoker.FloatIn[s.Position] != (p.Pass == PassKind.Float))
                    {
                        why = $"argument {p.Position} of another kind";
                        return null;
                    }
                    continue;
                }
                default:
                    why = $"a {p.Role} argument";
                    return null;
            }
        }
        if (last != invoker.MethodInfoPosition)
        {
            why = "a different number of arguments";
            return null;
        }
        return constants;
    }

    private static readonly bool NoInlineCompareExchange = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_COMPARE_EXCHANGE") != null;

    private void EmitIntrinsic(Node call, CallInfo info)
    {
        if (TryEmitBlockOp(call)) return;
        // A rounding the machine does in one instruction (AArch64's FRINT*): the Math method of that name.
        if (info.Intrinsic!.StartsWith("math.", StringComparison.Ordinal) && call.In.Length == 1 && call.Type is VT.F32 or VT.F64)
        {
            bool isDouble = call.Type == VT.F64;
            HExpr operand = AsFloat(FloatValue(call.In[0]), isDouble ? _double : _float);
            HExpr rounded = MathCall(info.Intrinsic[5..], isDouble, operand);
            if (!IsUsed(call)) Emit(new HEval(rounded), call.Addr);
            else if (_materialize.Contains(call))
            {
                HVar t = Temp(isDouble ? _double : _float, call.Type);
                Emit(new HAssign(new HLocal(t) { Type = t.Type }, rounded), call.Addr);
                _sem[call] = new SVal(new HLocal(t) { Type = t.Type });
            }
            else _sem[call] = new SVal(rounded);
            return;
        }
        // "lock cmpxchg" on a reference field (an inlined field-like event's add or remove, a lazy initializer):
        // what Interlocked.CompareExchange<T> does with it, as for the runtime's own helper.
        if (!NoInlineCompareExchange && info.Intrinsic == "atomic_compare_exchange" && call.In.Length == 3 && call.Type == VT.I64 &&
            LocationOf(call.In[0], null) is { Type: { } held } location && IsReference(held) &&
            _m.FindType("System.Threading.Interlocked")?.Methods.FirstOrDefault(m =>
                m.Name == "CompareExchange" && m.GenericParameters.Length == 1 && m.Parameters.Length == 3) is { } compareExchange)
        {
            HExpr[] arguments = [new HAddressOf(location) { Type = _m.Sigs.ByRef(held) }, ValueFor(call.In[1], held), ValueFor(call.In[2], held)];
            var exchange = new HCall { Method = compareExchange, MethodArguments = [held], Arguments = arguments, Type = held };
            if (!IsUsed(call)) Emit(new HEval(exchange), call.Addr);
            else
            {
                // (Once, into a variable: the exchange is done where the code does it, and its result read after.)
                HVar t = Temp(held, call.Type);
                Emit(new HAssign(new HLocal(t) { Type = held }, exchange), call.Addr);
                _sem[call] = new SVal(new HLocal(t) { Type = held });
            }
            return;
        }
        HExpr[] args = call.In.Select(Value).ToArray();
        var expr = new HOpaque(info.Intrinsic!, args) { Type = TypeForBits(call.Type) };
        if (info.Intrinsic == "memory_barrier") return; // volatile access marker
        Problem($"intrinsic {info.Intrinsic}");
        if (call.Type != VT.None && IsUsed(call))
        {
            HVar t = Temp(null, call.Type);
            Emit(new HAssign(new HLocal(t) { Type = t.Type }, expr), call.Addr);
            _sem[call] = new SVal(new HLocal(t) { Type = t.Type });
        }
        else Emit(new HEval(expr), call.Addr);
    }

    // ---- managed calls -----------------------------------------------------------------------------------------

    private bool IsAssignable(TypeSig? from, TypeSig to)
    {
        if (from == null) return true;
        if (ReferenceEquals(from, to)) return true;
        if (to is PrimitiveSig { Element: Rewind.Runtime.Il2CppTypeEnum.Object }) return IsReference(from);
        TypeDef? target = to.Definition;
        if (target == null) return false;
        for (TypeSig? t = from; t?.Definition != null;)
        {
            TypeDef def = t.Definition;
            if (ReferenceEquals(def, target)) return true;
            if (target.IsInterface)
                foreach (TypeSig i in def.Interfaces)
                    if (ReferenceEquals(i.Definition, target))
                        return true;
            if (def.BaseType == null) break;
            t = _m.Sigs.Substitute(def.BaseType, t is GenericInstSig g ? g.Arguments : [], []);
        }
        return false;
    }

    /// <summary>The nearest type both fit in: one of them when it takes the other, else the first base class of one that takes the other.</summary>
    private TypeSig JoinTypes(TypeSig a, TypeSig b)
    {
        if (IsAssignable(b, a)) return a;
        if (IsAssignable(a, b)) return b;
        for (TypeSig? t = a; t?.Definition != null;)
        {
            TypeDef def = t.Definition;
            if (def.BaseType == null) break;
            t = _m.Sigs.Substitute(def.BaseType, t is GenericInstSig g ? g.Arguments : [], []);
            if (t != null && IsAssignable(b, t)) return t;
        }
        return _object;
    }

    /// <summary>
    /// The form of a generic argument that decides which compiled body an instantiation uses: all reference
    /// types share one body, an enum shares with its underlying integer type, other value types stand alone.
    /// </summary>
    private TypeSig CanonicalArgument(TypeSig t)
    {
        if (IsReference(t)) return _object;
        if (t.Definition is { IsEnum: true, EnumUnderlyingType: { } underlying }) return underlying;
        if (t is GenericInstSig g) return _m.Sigs.GenericInst(g.Definition!, g.Arguments.Select(CanonicalArgument).ToArray());
        return t;
    }

    private bool SharesCode(TypeSig a, TypeSig b)
    {
        if (a is not GenericInstSig ga || b is not GenericInstSig gb || !ReferenceEquals(ga.Definition, gb.Definition)) return false;
        if (ga.Arguments.Length != gb.Arguments.Length) return false;
        for (int i = 0; i < ga.Arguments.Length; i++)
            if (!ReferenceEquals(CanonicalArgument(ga.Arguments[i]), CanonicalArgument(gb.Arguments[i])))
                return false;
        return true;
    }

    /// <summary>
    /// The generic arguments with which <paramref name="declaring"/> appears in the type of a receiver (looking
    /// through base classes and interfaces): the instantiation a call on that receiver really refers to.
    /// </summary>
    private TypeSig[]? DeclaringArguments(TypeSig? type, TypeDef declaring)
    {
        for (int depth = 0; type != null && depth < 32; depth++)
        {
            if (type is GenericInstSig g && ReferenceEquals(g.Definition, declaring))
                return g.Arguments.Any(Open) ? null : g.Arguments;
            TypeDef? def = type.Definition;
            if (def == null) return null;
            TypeSig[] arguments = type is GenericInstSig inst ? inst.Arguments : [];
            if (declaring.IsInterface)
                foreach (TypeSig i in def.Interfaces)
                    if (_m.Sigs.Substitute(i, arguments, []) is GenericInstSig gi && ReferenceEquals(gi.Definition, declaring) &&
                        !gi.Arguments.Any(Open))
                        return gi.Arguments;
            if (def.BaseType == null) return null;
            type = _m.Sigs.Substitute(def.BaseType, arguments, []);
        }
        return null;
    }

    /// <summary>Whether IL in the current method could name <paramref name="callee"/> at all.</summary>
    private bool IsAccessible(MethodDef callee)
    {
        TypeDef from = _method.DeclaringType, owner = callee.DeclaringType;
        bool Within(TypeDef inner, TypeDef outer)
        {
            for (TypeDef? t = inner; t != null; t = t.DeclaringType)
                if (ReferenceEquals(t, outer))
                    return true;
            return false;
        }
        bool Derives(TypeDef type, TypeDef ancestor)
        {
            int guard = 0;
            for (TypeDef? t = type; t != null && guard++ < 64; t = t.BaseType?.Definition)
                if (ReferenceEquals(t, ancestor))
                    return true;
            return false;
        }
        bool sameAssembly = ReferenceEquals(from.Assembly, owner.Assembly);
        bool family = false;
        for (TypeDef? t = from; t != null && !family; t = t.DeclaringType) family = Derives(t, owner);
        return (callee.Flags & MethodDef.AccessMask) switch
        {
            6 => true,                               // public
            1 => Within(from, owner),                // private
            3 => sameAssembly,                       // internal
            4 => family || Within(from, owner),      // protected
            5 => family || sameAssembly,             // protected internal
            2 => family && sameAssembly,             // private protected
            _ => Within(from, owner),
        };
    }

    /// <summary>What a value is, without using it (see _peeking).</summary>
    private Sem Peek(Node n)
    {
        _peeking++;
        try
        {
            return Eval(n);
        }
        finally
        {
            _peeking--;
        }
    }

    private int Score(Node call, MethodDef method, TypeSig[] classArgs, TypeSig[] methodArgs, MethodInst? inst)
    {
        _peeking++;
        try
        {
            return ScoreCore(call, method, classArgs, methodArgs, inst);
        }
        finally
        {
            _peeking--;
        }
    }

    private int ScoreCore(Node call, MethodDef method, TypeSig[] classArgs, TypeSig[] methodArgs, MethodInst? inst)
    {
        MethodAbi abi = _p.Abi.For(method, classArgs, methodArgs);
        int score = 0;
        foreach (AbiParam p in abi.Params)
        {
            if (p.Role == ParamRole.MethodInfo)
            {
                // Generic methods receive their own MethodInfo: an exact identification when present.
                if (IntAt(call, p.Position) is not { } mi) continue;
                if (Eval(mi) is SMethod sm)
                {
                    if (inst != null && sm.Inst != null && ReferenceEquals(sm.Inst, inst)) score += 1000;
                    else if (inst == null && sm.Inst == null && ReferenceEquals(sm.Method, method)) score += 1000;
                    else if (ReferenceEquals(sm.Method, method)) score += 200;
                    else score -= 500;
                }
                // A call to a method of an instantiation always hands it that method's descriptor; a call that
                // hands none (a null written out) is to a method that is no instantiation and shares the code.
                else if (inst != null && !NoNullDescriptors && mi.IsConstValue(0)) score -= 60;
                continue;
            }
            if (p.Pass == PassKind.Float || p.Type == null) continue;
            Node? node = IntAt(call, p.Position);
            if (node == null) continue;
            Sem s = Eval(node);
            // An argument the caller never set: this method takes more than the call passes.
            if (p.Role == ParamRole.Argument && (node.Op == Op.Undef || (node.Op == Op.Param && s is SJunk))) score -= 15;
            // A runtime class pointer is no object a method could be called on: what is called takes no receiver
            // (a static method sharing the code) and the register merely still holds it.
            if (p.Role == ParamRole.This && !NoReachableAssemblies && s is SKlass) score -= 50;
            // A method of a struct is called on the address of one. A receiver that is no address of anything
            // (a number, a leftover) means the call is to something else that shares this code.
            if (p.Role == ParamRole.This && p.Type.Definition is { IsValueType: true } &&
                s is not (SRef or SFrame or SUnboxed or SStatics) && !(s is SVal { Type: ByRefSig or PointerSig }) &&
                !(s is SVal { Type: { } boxed } && IsReference(boxed)))
                score -= 40;
            // A constructor runs a constructor of its base class (or another of its own) on the object it is
            // building, once, before anything else is called on it. An empty base constructor shares its code
            // with every other empty method of the program; of all of those, this is the one that is meant.
            if (p.Role == ParamRole.This && !_baseConstructorCalled && _method.Name == ".ctor" && method.Name == ".ctor" &&
                !ReferenceEquals(method, _method) && s is SVal { Expr: HArg { Index: -1 } } &&
                (ReferenceEquals(method.DeclaringType, _method.DeclaringType.BaseType?.Definition) || ReferenceEquals(method.DeclaringType, _method.DeclaringType) ||
                 // (The base class's constructor pasted in: the one it calls in turn is further up.)
                 (!NoFreshReceivers && Derives(_method.DeclaringType, method.DeclaringType))))
                score += 40;
            // Before a constructor has run the one of its base class, nothing but stores is done to the object:
            // an empty method of its class called there is the empty base constructor that shares its code.
            if (p.Role == ParamRole.This && !NoFreshReceivers && !_baseConstructorCalled && _method.Name == ".ctor" && !_method.IsStatic &&
                !_method.DeclaringType.IsValueType && method.Name != ".ctor" && s is SVal { Expr: HArg { Index: -1 } })
                score -= 40;
            // The first thing run on a freshly allocated object is a constructor of its class or of a class it
            // derives from ("new T()", or T's constructor pasted in and its base constructor called). An empty
            // constructor shares its code with every other empty method - a Dispose that does nothing, say - and
            // calling one of those on an object no constructor has run on is not what was written.
            if (p.Role == ParamRole.This && !NoFreshReceivers && s is SNewObject { Constructed: false } fresh && fresh.Type.Definition is { } allocated)
            {
                if (method.Name != ".ctor") score -= 40;
                else if (Derives(allocated, method.DeclaringType)) score += 40;
                else score -= 100;
            }
            TypeSig? actual = s switch
            {
                SVal v => v.Type,
                SRef r => r.Type,
                SNewObject o => o.Type,
                // The address of a stack object: what lives there (a struct local as receiver or by reference,
                // a value boxed in place as an object).
                SFrame f when _fakeBoxes.ContainsKey(f.Offset) => _object,
                SFrame f when _frameTypes.TryGetValue(f.Offset, out TypeSig? local) => local,
                // Stack memory nothing has typed yet: the struct that was stored there whole.
                SFrame f when p.Role == ParamRole.This && StoredStruct(f.Offset) is { } held => held,
                _ => null,
            };
            if (actual == null) continue;
            TypeSig expected = p.Type is ByRefSig byRef ? byRef.ElementType : p.Type;
            if (p.Role == ParamRole.ReturnBuffer) expected = abi.ReturnType;
            if (ReferenceEquals(actual, expected)) score += p.Role == ParamRole.This ? 20 : 4;
            else if (SharesCode(actual, expected)) score += p.Role == ParamRole.This ? 16 : 3;
            else if (IsReference(actual) && IsReference(expected))
                score += IsAssignable(actual, expected) ? (p.Role == ParamRole.This ? 10 : 2) : (p.Role == ParamRole.This ? -100 : -20);
            else if (IsReference(actual) != IsReference(expected) && !(s is SRef)) score -= 30;
        }
        // What the call gives goes straight into a place whose type is known (a field, a typed piece of the
        // stack): of the methods that share this code, the one that gives that type is the one written.
        if (!NoResultPlaces && abi.ReturnType is { IsVoid: false } gives && ResultPlace(call) is { } wanted &&
            (ReferenceEquals(gives, wanted) || gives.Key == wanted.Key))
            score += 6;
        // A method calling the same-named method of a base type is the usual "base.Method()" shape.
        if (method.Name == _method.Name && !ReferenceEquals(method, _method)) score += 3;
        // Code that could not have been written here (a private member of an unrelated class) can still show
        // up through inlining, so this is a strong hint rather than a rule.
        if (!IsAccessible(method)) score -= 25;
        // An assembly's code can only name what is in it or in the assemblies it uses: a plugin cannot call into
        // the game that uses it. (Inlined code comes from such assemblies too, so it is no exception.)
        if (!NoReachableAssemblies && !Reachable(method.DeclaringType.Assembly)) score -= 200;
        return score;
    }

    /// <summary>More methods than this taking a pointer where one piece of code they share is handed one (see InferFrameTypes): the first of them is a guess.</summary>
    private static readonly int SharedPointeeLimit = int.TryParse(Environment.GetEnvironmentVariable("REWIND_SHARED_POINTEE_LIMIT"), out int limit) ? limit : 2;
    private static readonly bool NoReachableAssemblies = Environment.GetEnvironmentVariable("REWIND_NO_REACHABLE_ASSEMBLIES") != null;

    /// <summary>
    /// Whether IL of this method's assembly can name a type at all (it and its type arguments come from the
    /// assembly or one it refers to directly): a type it cannot name is never what one of its locals is.
    /// </summary>
    private bool Nameable(TypeSig? type) => NoReachableAssemblies || AssemblyScope.Names(_method.DeclaringType.Assembly, type);

    /// <summary>
    /// Whether code of this method's assembly can end up calling into <paramref name="assembly"/>: it is the
    /// assembly itself or one it refers to, directly or through others (see AssemblyScope).
    /// </summary>
    private bool Reachable(AssemblyModel assembly) => NoReachableAssemblies || AssemblyScope.Reaches(_method.DeclaringType.Assembly, assembly);

    private static readonly bool NoStoredStructs = Environment.GetEnvironmentVariable("REWIND_NO_STORED_STRUCTS") != null;
    private Dictionary<int, List<Node>>? _frameStores;

    /// <summary>
    /// The struct type of what has been stored whole at a stack offset so far (a call's result, a field read
    /// in one piece), when every such store agrees; null when there is none or they differ. A struct that
    /// lives in a register is put on the stack before a method is called on it, and of the methods that share
    /// the called code, the one of that struct is meant.
    /// </summary>
    private TypeSig? StoredStruct(int offset)
    {
        if (NoStoredStructs) return null;
        if (_frameStores == null)
        {
            _frameStores = [];
            foreach (Block b in _fn.Blocks)
                foreach (Node store in b.Nodes)
                {
                    if (store.Dead || store.Op != Op.Store || !IsFrameAddress(store.In[0], out int at)) continue;
                    if (!_frameStores.TryGetValue(at, out List<Node>? list)) _frameStores[at] = list = [];
                    list.Add(store);
                }
        }
        if (!_frameStores.TryGetValue(offset, out List<Node>? stores)) return null;
        TypeSig? found = null;
        foreach (Node store in stores)
        {
            Node value = store.In[1];
            int bytes = value.Type.Bytes();
            while (value.Op == Op.Trunc) value = value.In[0];
            // (What has no meaning yet is stored later than the call being looked at.)
            if (!_sem.TryGetValue(value, out Sem? s) || s is not SVal { Type: { } type } || !IsStructType(type) || Open(type) || !Nameable(type)) continue;
            if (_p.Layouts.SizeOf(type) is not { Known: true } size || size.Size != bytes) continue;
            if (found != null && found.Key != type.Key) return null;
            found = type;
        }
        return found;
    }

    private static readonly bool NoResultPlaces = Environment.GetEnvironmentVariable("REWIND_NO_RESULT_PLACES") != null;
    private static readonly bool NoReturnedResults = Environment.GetEnvironmentVariable("REWIND_NO_RETURNED_RESULTS") != null;
    private static readonly bool NoNullDescriptors = Environment.GetEnvironmentVariable("REWIND_NO_NULL_DESCRIPTORS") != null;
    private static readonly bool NoFreshReceivers = Environment.GetEnvironmentVariable("REWIND_NO_FRESH_RECEIVERS") != null;

    /// <summary>Whether <paramref name="type"/> is <paramref name="ancestor"/> or derives from it.</summary>
    private static bool Derives(TypeDef type, TypeDef ancestor)
    {
        int guard = 0;
        for (TypeDef? t = type; t != null && guard++ < 64; t = t.BaseType?.Definition)
            if (ReferenceEquals(t, ancestor))
                return true;
        return false;
    }

    private readonly Dictionary<Node, TypeSig?> _resultPlaces = [];

    /// <summary>
    /// The type of the place a call's result is put into as it comes back - a field of an object, a piece of
    /// the stack whose type is known; null when it goes anywhere else.
    /// </summary>
    private TypeSig? ResultPlace(Node call)
    {
        if (_resultPlaces.TryGetValue(call, out TypeSig? known)) return known;
        TypeSig? type = null;
        // What a method hands back as it comes from a call is what that call gives: the result type of the
        // method is the place.
        TypeSig? returned = !NoReturnedResults && _abi.Return is ReturnKind.Integer or ReturnKind.StructInRegister && _abi.ReturnType is { IsVoid: false } r && !Open(r) ? r : null;
        if (returned != null && call.Op == Op.TailCall) return _resultPlaces[call] = returned;
        if (call.Block != null && _position.ContainsKey(call) && Projections(call).TryGetValue(CallResult.IntReturn, out Node? result))
        {
            var holders = new List<Node> { result };
            if (_uses.TryGetValue(result, out List<Node>? direct))
                foreach (Node use in direct)
                    if (!use.Dead && use.Op == Op.Trunc)
                        holders.Add(use);
            if (returned != null)
                foreach (Node holder in holders)
                {
                    if (type != null || !_uses.TryGetValue(holder, out List<Node>? uses)) continue;
                    int bytes = holder.Type.Bytes();
                    if (!(IsReference(returned) || returned is PointerSig or ByRefSig ? bytes == 8 : _p.Layouts.SizeOf(returned) is { Known: true } size && size.Size == bytes)) continue;
                    foreach (Node use in uses)
                        if (!use.Dead && use.Op == Op.Return && use.In.Length != 0 && ReferenceEquals(use.In[0], holder) && ReferenceEquals(use.Block, call.Block))
                            type = returned;
                }
            foreach (Node holder in holders)
            {
                if (type != null || !_uses.TryGetValue(holder, out List<Node>? uses)) continue;
                foreach (Node store in uses)
                {
                    if (store.Dead || store.Op != Op.Store || !ReferenceEquals(store.In[1], holder) || !ReferenceEquals(store.Block, call.Block)) continue;
                    Node address = store.In[0];
                    int bytes = holder.Type.Bytes();
                    TypeSig? found = null;
                    if (IsFrameAddress(address, out int offset))
                    {
                        if (_frameTypes.TryGetValue(offset, out TypeSig? local)) found = local;
                    }
                    else if (address.Op == Op.Add && address.In[1].IsConst && Peek(address.In[0]) is SVal { Type: { } owner } &&
                             IsReference(owner) && !Open(owner))
                    {
                        int at = (int)IrBuilder.SImm(address.In[1]);
                        if (_p.Layouts.FieldAt(owner, at) is { } slot && slot.Offset == at) found = slot.Type;
                    }
                    // The whole of the place, not a part of something bigger there.
                    if (found != null && !Open(found) && (IsReference(found) ? bytes == 8 : _p.Layouts.SizeOf(found).Size == bytes))
                    {
                        type = found;
                        break;
                    }
                }
            }
        }
        return _resultPlaces[call] = type;
    }

    private void EmitManagedCall(Node call, CallTarget target, bool tail)
    {
        MethodDef? best = null;
        MethodInst? bestInst = null;
        int bestScore = int.MinValue;
        var ties = new List<MethodDef>();
        void Consider(MethodDef m, MethodInst? inst)
        {
            int score = Score(call, m, inst?.ClassArguments ?? [], inst?.MethodArguments ?? [], inst);
            if (score > bestScore)
            {
                bestScore = score;
                best = m;
                bestInst = inst;
                ties.Clear();
            }
            else if (score == bestScore && !ReferenceEquals(m, best)) ties.Add(m);
        }
        foreach (MethodDef m in target.Methods) Consider(m, null);
        foreach (MethodInst inst in target.Insts) Consider(inst.Method, inst);
        if (best == null)
        {
            Problem("managed call with no candidates");
            return;
        }
        // One function that only gives a constant, and it is the code of methods of several return types
        // ("PlayerRef.None", "TickTimer.None", ... are all "return 0"): which of them was written cannot be
        // told from the call, and guessing one gives the result a type it may not have. What it gives is
        // certain.
        if (!tail && ties.Count != 0 && ties.Any(t => !ReferenceEquals(t.ReturnType, best.ReturnType)) && ConstantFunction(best.Address) is { } given)
        {
            if (Projections(call).TryGetValue(CallResult.IntReturn, out Node? result))
                _sem[result] = new SVal(result.Type == VT.I64 ? new HConst(given, _long) : new HConst((int)given, _int));
            return;
        }
        // One function that only hands back what it is given ("mov eax, ecx; ret"), and it is the code of
        // methods that take and give different things (a layer mask from a number, a number from a layer
        // mask, an easing function from its mode, ...): which of them was written cannot be told from the
        // call, and guessing one names types that may have nothing to do with the place. What it gives is
        // certain: what it was given. Where that is a struct's own number, the struct's methods are
        // recognized by the field it ends up in.
        if (!tail && !NoIdentityCalls && ties.Count != 0 && ties.Any(t => !SameShape(t, best!)) && IdentityFunction(best.Address) is { } width &&
            IntAt(call, 0) is { } handed && Projections(call).TryGetValue(CallResult.IntReturn, out Node? back))
        {
            Sem passed = Eval(handed);
            // A number written out: what comes back is its low half.
            if (width == 32 && passed is SVal { Expr: HConst { Value: var number } })
            {
                long? plain = number switch
                {
                    int i => i, uint u => u, long l => l, ulong ul => unchecked((long)ul), short s => s, ushort us => us, byte b => b, sbyte sb => sb,
                    _ => null,
                };
                if (plain is { } low) passed = new SVal(new HConst(unchecked((int)low), _int));
            }
            // A number made wider on its way into the register: its low half is the number itself.
            else if (width == 32 && passed is SVal { Expr: HConv { Kind: HConvKind.U8 or HConvKind.I8, Operand: { } narrow } } &&
                     BitsOf(narrow.Type) is > 0 and <= 32 && !IsFloat(narrow.Type))
                passed = new SVal(narrow);
            bool whole = width == 64 || passed is SVal { Type: var held } && (held == null ? back.Type != VT.I64 : BitsOf(held) is > 0 and <= 32 || (IsStructType(held) && _p.Layouts.SizeOf(held).Item1 <= 4));
            if (whole && passed is not (SJunk or SPair or SParts or SHalf))
            {
                _sem[back] = passed;
                return;
            }
        }
        // Every method known to share this code is in an assembly this code cannot reach: what was called is
        // something else with the same code (a helper the compiler made, folded with them by the linker). What a
        // tiny body computes is certain; anything else is called as one of them, and said to be uncertain.
        if (!NoReachableAssemblies && !Reachable(best.DeclaringType.Assembly))
        {
            if (!tail && Projections(call).TryGetValue(CallResult.IntReturn, out Node? sharedResult))
            {
                if (ConstantFunction(best.Address) is { } constant)
                {
                    _sem[sharedResult] = new SVal(sharedResult.Type == VT.I64 ? new HConst(constant, _long) : new HConst((int)constant, _int));
                    return;
                }
                if (SumFunction(best.Address) is { } wide && IntAt(call, 0) is { } left && IntAt(call, 1) is { } right)
                {
                    TypeSig type = wide ? _long : _int;
                    HExpr Operand(Node n)
                    {
                        HExpr v = IntValue(n);
                        return wide || BitsOf(v.Type) is > 0 and <= 32 ? v : new HConv(HConvKind.I4, v) { Type = _int };
                    }
                    _sem[sharedResult] = new SVal(new HBinary(HBinaryOp.Add, Operand(left), Operand(right)) { Type = type });
                    return;
                }
            }
            Problem($"call to code shared only by methods this assembly cannot reach ({best.DeclaringType.Name}.{best.Name})");
        }
        BuildCall(call, best, bestInst?.ClassArguments ?? [], bestInst?.MethodArguments ?? [], isVirtual: false, tail, ties, skipFirst: false, listed: bestInst != null);
    }

    private readonly Dictionary<ulong, bool?> _sumFunctions = [];

    /// <summary>
    /// A function that only adds its first two arguments ("lea eax, [rcx+rdx]; ret"): true when it does so in 64
    /// bits, false in 32, null for any other function.
    /// </summary>
    private bool? SumFunction(ulong address)
    {
        if (address == 0) return null;
        if (_sumFunctions.TryGetValue(address, out bool? known)) return known;
        bool? wide = null;
        X64Cfg cfg = X64Cfg.Build(_p.Context, address);
        if (cfg.Blocks.Count == 1 && cfg.Blocks[0].Instructions.Count == 2 && cfg.Blocks[0].Instructions[1].Mnemonic == Iced.Intel.Mnemonic.Ret)
        {
            Iced.Intel.Instruction lea = cfg.Blocks[0].Instructions[0];
            if (lea.Mnemonic == Iced.Intel.Mnemonic.Lea && lea.Op0Kind == Iced.Intel.OpKind.Register && lea.Op0Register is Iced.Intel.Register.EAX or Iced.Intel.Register.RAX &&
                lea.MemoryDisplacement64 == 0 && lea.MemoryIndexScale == 1 &&
                ((lea.MemoryBase == Iced.Intel.Register.RCX && lea.MemoryIndex == Iced.Intel.Register.RDX) || (lea.MemoryBase == Iced.Intel.Register.RDX && lea.MemoryIndex == Iced.Intel.Register.RCX)))
                wide = lea.Op0Register == Iced.Intel.Register.RAX;
        }
        return _sumFunctions[address] = wide;
    }

    private static readonly bool NoIdentityCalls = Environment.GetEnvironmentVariable("REWIND_NO_IDENTITY_CALLS") != null;

    /// <summary>Whether two methods take and give the same things.</summary>
    private static bool SameShape(MethodDef a, MethodDef b)
    {
        if (a.IsStatic != b.IsStatic || !ReferenceEquals(a.ReturnType, b.ReturnType) || a.Parameters.Length != b.Parameters.Length) return false;
        if (!a.IsStatic && !ReferenceEquals(a.DeclaringType, b.DeclaringType)) return false;
        for (int i = 0; i < a.Parameters.Length; i++)
            if (!ReferenceEquals(a.Parameters[i].Type, b.Parameters[i].Type))
                return false;
        return true;
    }

    private readonly Dictionary<ulong, int> _identityFunctions = [];

    /// <summary>
    /// For a function that only hands back its first argument ("mov eax, ecx; ret"): how many bits of it
    /// (32 or 64); null for any other.
    /// </summary>
    private int? IdentityFunction(ulong address)
    {
        if (address == 0) return null;
        if (!_identityFunctions.TryGetValue(address, out int known))
        {
            known = 0;
            X64Cfg cfg = X64Cfg.Build(_p.Context, address);
            if (cfg.Blocks.Count == 1 && cfg.Blocks[0].Instructions.Count is >= 2 and <= 6 && cfg.Blocks[0].Instructions[^1].Mnemonic == Iced.Intel.Mnemonic.Ret)
            {
                // Which registers hold the first argument, and how many bits of it: only moves between
                // registers (and padding) on the way to the one results come back in.
                var holds = new Dictionary<Iced.Intel.Register, int> { [Iced.Intel.Register.RCX] = 64 };
                bool plain = true;
                for (int i = 0; i < cfg.Blocks[0].Instructions.Count - 1 && plain; i++)
                {
                    Iced.Intel.Instruction move = cfg.Blocks[0].Instructions[i];
                    if (move.Mnemonic == Iced.Intel.Mnemonic.Nop) continue;
                    // Padding the linker puts first, so the function can be patched while it runs.
                    if (move.Mnemonic == Iced.Intel.Mnemonic.Xchg && move.Op0Kind == Iced.Intel.OpKind.Register && move.Op1Kind == Iced.Intel.OpKind.Register && move.Op0Register == move.Op1Register) continue;
                    plain = false;
                    if (move.Mnemonic != Iced.Intel.Mnemonic.Mov || move.Op0Kind != Iced.Intel.OpKind.Register || move.Op1Kind != Iced.Intel.OpKind.Register) break;
                    int bits = Iced.Intel.RegisterExtensions.GetSize(move.Op0Register) * 8;
                    if (bits is not (32 or 64) || Iced.Intel.RegisterExtensions.GetSize(move.Op1Register) * 8 != bits) break;
                    Iced.Intel.Register from = Iced.Intel.RegisterExtensions.GetFullRegister(move.Op1Register), to = Iced.Intel.RegisterExtensions.GetFullRegister(move.Op0Register);
                    if (!holds.TryGetValue(from, out int had))
                    {
                        // Something else moved over a register that held it: gone from there.
                        holds.Remove(to);
                        plain = true;
                        continue;
                    }
                    holds[to] = Math.Min(had, bits);
                    plain = true;
                }
                if (plain && holds.TryGetValue(Iced.Intel.Register.RAX, out int back)) known = back;
            }
            _identityFunctions[address] = known;
        }
        return known == 0 ? null : known;
    }

    private static readonly bool ForwardersMayStore = Environment.GetEnvironmentVariable("REWIND_FORWARDERS_MAY_STORE") != null;
    private static readonly bool NoParameterSlots = Environment.GetEnvironmentVariable("REWIND_NO_PARAMETER_SLOTS") != null;
    private readonly Dictionary<ulong, bool> _writesMemory = [];

    /// <summary>Whether a (short) function writes to memory: one that does is more than a jump to another.</summary>
    private bool WritesMemory(ulong address)
    {
        if (ForwardersMayStore) return false;
        if (_writesMemory.TryGetValue(address, out bool known)) return known;
        bool writes = false;
        foreach (var block in X64Cfg.Build(_p.Context, address).Blocks)
            foreach (Iced.Intel.Instruction i in block.Instructions)
                if (i.OpCount > 0 && i.Op0Kind == Iced.Intel.OpKind.Memory &&
                    i.Mnemonic is not (Iced.Intel.Mnemonic.Cmp or Iced.Intel.Mnemonic.Test or Iced.Intel.Mnemonic.Push or Iced.Intel.Mnemonic.Jmp or Iced.Intel.Mnemonic.Call))
                    writes = true;
        return _writesMemory[address] = writes;
    }

    private static readonly bool NoInvokerShapes = Environment.GetEnvironmentVariable("REWIND_NO_INVOKER_SHAPES") != null;
    private static readonly bool NoBufferInvokers = Environment.GetEnvironmentVariable("REWIND_NO_BUFFER_INVOKERS") != null;
    private static readonly bool NoGenericInvokerShapes = Environment.GetEnvironmentVariable("REWIND_NO_GENERIC_INVOKERS") != null;
    private static readonly bool NoRgctxCalls = Environment.GetEnvironmentVariable("REWIND_NO_RGCTX_CALLS") != null;
    // (Asked from every thread that recovers methods; what a function is does not depend on who asks.)
    private static readonly System.Collections.Concurrent.ConcurrentDictionary<ulong, HelperInfo?> InvokerShapes = new();

    /// <summary>
    /// Whether a function without a name is one of those IL2CPP makes for calling a method by its slot:
    /// "Virtual...Invoker::Invoke(slot, obj, args...)" or "Interface...Invoker::Invoke(slot, interfaceClass, obj,
    /// args...)". Told by what it does: the slot arrives as a 16-bit number in the first argument, the class is
    /// read from the object (the second argument, or the third), the class's table is read - at the slot, or
    /// after the search of the interface offsets, where the only call is the runtime's slow path for that
    /// search - and what the table holds is called.
    /// </summary>
    private HelperInfo? InvokerShape(ulong address)
    {
        if (address == 0 || NoInvokerShapes) return null;
        if (InvokerShapes.TryGetValue(address, out HelperInfo? known)) return known;
        HelperInfo? found = null;
        X64Cfg cfg = X64Cfg.Build(_p.Context, address);
        int count = 0;
        foreach (var block in cfg.Blocks) count += block.Instructions.Count;
        if (cfg.Blocks.Count is >= 1 and <= 16 && count is >= 6 and <= 96)
        {
            // Which argument each register still holds, in the first stretch.
            var holds = new Dictionary<Iced.Intel.Register, Iced.Intel.Register>
            {
                [Iced.Intel.Register.RDX] = Iced.Intel.Register.RDX,
                [Iced.Intel.Register.R8] = Iced.Intel.Register.R8,
                [Iced.Intel.Register.R9] = Iced.Intel.Register.R9,
            };
            Iced.Intel.Register objectIn = Iced.Intel.Register.None, classIn = Iced.Intel.Register.None;
            bool slot = false, entry = false, offsets = false, through = false, others = false, slow = false, generic = false;
            // (One that returns a struct is handed the address it goes to first: the slot comes second.)
            bool slotSecond = false;
            bool first = true;
            foreach (var block in cfg.Blocks)
            {
                foreach (Iced.Intel.Instruction i in block.Instructions)
                {
                    bool load = i.Mnemonic == Iced.Intel.Mnemonic.Mov && i.Op0Kind == Iced.Intel.OpKind.Register && i.Op1Kind == Iced.Intel.OpKind.Memory;
                    if (i.Mnemonic == Iced.Intel.Mnemonic.Movzx && i.Op1Kind == Iced.Intel.OpKind.Register && i.Op1Register == Iced.Intel.Register.CX) slot = true;
                    if (i.Mnemonic == Iced.Intel.Mnemonic.Movzx && i.Op1Kind == Iced.Intel.OpKind.Register && i.Op1Register == Iced.Intel.Register.DX) slotSecond = true;
                    // The class of the object: read through the register an argument came in, or a copy of it.
                    if (first && load && classIn == Iced.Intel.Register.None && i.MemoryIndex == Iced.Intel.Register.None && i.MemoryDisplacement64 == 0 &&
                        holds.TryGetValue(i.MemoryBase, out Iced.Intel.Register argument))
                    {
                        objectIn = argument;
                        classIn = i.Op0Register;
                    }
                    else if (classIn != Iced.Intel.Register.None && i.Op1Kind == Iced.Intel.OpKind.Memory && i.MemoryBase == classIn)
                    {
                        long at = (long)i.MemoryDisplacement64;
                        if (load && i.MemoryIndex != Iced.Intel.Register.None && i.MemoryIndexScale == 8 && at == _p.Klass.VTable) entry = true;
                        if (i.MemoryIndex == Iced.Intel.Register.None && (at == _p.Klass.InterfaceOffsets || at == _p.Klass.InterfaceOffsetsCount)) offsets = true;
                    }
                    if (i.Mnemonic == Iced.Intel.Mnemonic.Call || i.Mnemonic == Iced.Intel.Mnemonic.Jmp)
                    {
                        if (i.Op0Kind == Iced.Intel.OpKind.Register) through = true;
                        else if (i.Mnemonic == Iced.Intel.Mnemonic.Call && i.Op0Kind == Iced.Intel.OpKind.NearBranch64)
                        {
                            HelperKind? asked = _p.Resolve(i.NearBranchTarget).Helper?.Kind;
                            if (asked == HelperKind.InterfaceInvokeDataSlow) slow = true;
                            else if (asked == HelperKind.GetGenericVirtualMethod) generic = true;
                            else others = true;
                        }
                        else if (i.Mnemonic == Iced.Intel.Mnemonic.Call) others = true;
                    }
                    if (first && i.Op0Kind == Iced.Intel.OpKind.Register)
                    {
                        // (What is written to no longer holds the argument; a plain copy holds what its source held.)
                        Iced.Intel.Register written = Iced.Intel.RegisterExtensions.GetFullRegister(i.Op0Register);
                        Iced.Intel.Register? copied = i.Mnemonic == Iced.Intel.Mnemonic.Mov && i.Op1Kind == Iced.Intel.OpKind.Register && i.Op0Register == written &&
                                                      holds.TryGetValue(i.Op1Register, out Iced.Intel.Register from) ? from : null;
                        bool reads = i.Mnemonic is Iced.Intel.Mnemonic.Cmp or Iced.Intel.Mnemonic.Test or Iced.Intel.Mnemonic.Push;
                        if (!reads)
                        {
                            holds.Remove(written);
                            if (copied is { } same) holds[written] = same;
                        }
                    }
                }
                first = false;
            }
            // Invoke(method, obj, args...) of a generic virtual method: no slot number comes in (the method
            // has it), and the runtime is asked which version of the method the object's class has.
            if (generic && through && !others && !slot && objectIn == Iced.Intel.Register.RDX && !NoGenericInvokerShapes)
            {
                if (offsets) found = new HelperInfo(HelperKind.GenericInterfaceInvoker, 0, false, true, "GenericInterfaceInvoker (known by its code)");
                else if (entry && !slow) found = new HelperInfo(HelperKind.GenericVirtualInvoker, 0, false, true, "GenericVirtualInvoker (known by its code)");
            }
            else if (slot && through && !others && !generic)
            {
                if (objectIn == Iced.Intel.Register.RDX && entry && !offsets && !slow)
                    found = new HelperInfo(HelperKind.VirtualInvoker, 0, false, true, "VirtualInvoker (known by its code)");
                else if (objectIn == Iced.Intel.Register.R8 && offsets)
                    found = new HelperInfo(HelperKind.InterfaceInvoker, 0, false, true, "InterfaceInvoker (known by its code)");
            }
            else if (slotSecond && !slot && through && !others && !generic && !NoBufferInvokers)
            {
                if (objectIn == Iced.Intel.Register.R8 && entry && !offsets && !slow)
                    found = new HelperInfo(HelperKind.VirtualInvoker, 0, false, true, "VirtualInvoker returning a struct (known by its code)") { BufferFirst = true };
                else if (objectIn == Iced.Intel.Register.R9 && offsets)
                    found = new HelperInfo(HelperKind.InterfaceInvoker, 0, false, true, "InterfaceInvoker returning a struct (known by its code)") { BufferFirst = true };
            }
        }
        return InvokerShapes.GetOrAdd(address, found);
    }

    private readonly Dictionary<ulong, long?> _constantFunctions = [];
    private static readonly bool NoByteConstants = Environment.GetEnvironmentVariable("REWIND_NO_BYTE_CONSTANTS") != null;

    /// <summary>What a function gives when giving a constant is all it does ("xor eax, eax; ret"); null for any other.</summary>
    private long? ConstantFunction(ulong address)
    {
        if (address == 0) return null;
        if (_constantFunctions.TryGetValue(address, out long? known)) return known;
        long? value = null;
        X64Cfg cfg = X64Cfg.Build(_p.Context, address);
        if (cfg.Blocks.Count == 1 && cfg.Blocks[0].Instructions.Count == 2 && cfg.Blocks[0].Instructions[1].Mnemonic == Iced.Intel.Mnemonic.Ret)
        {
            Iced.Intel.Instruction set = cfg.Blocks[0].Instructions[0];
            bool whole = set.Op0Kind == Iced.Intel.OpKind.Register && set.Op0Register is Iced.Intel.Register.EAX or Iced.Intel.Register.RAX;
            if (whole && set.Mnemonic == Iced.Intel.Mnemonic.Xor && set.Op1Kind == Iced.Intel.OpKind.Register && set.Op1Register == set.Op0Register) value = 0;
            else if (whole && set.Mnemonic == Iced.Intel.Mnemonic.Mov && set.Op0Register == Iced.Intel.Register.EAX && set.Op1Kind == Iced.Intel.OpKind.Immediate32)
                value = set.Immediate32;
            else if (whole && set.Mnemonic == Iced.Intel.Mnemonic.Mov && set.Op0Register == Iced.Intel.Register.RAX &&
                     set.Op1Kind is Iced.Intel.OpKind.Immediate32to64 or Iced.Intel.OpKind.Immediate64)
                value = (long)set.GetImmediate(1);
            // A yes/no or a byte: only the low byte of the register is set, and only it is looked at ("mov al, 1").
            else if (!NoByteConstants && set.Mnemonic == Iced.Intel.Mnemonic.Mov && set.Op0Kind == Iced.Intel.OpKind.Register &&
                     set.Op0Register == Iced.Intel.Register.AL && set.Op1Kind == Iced.Intel.OpKind.Immediate8)
                value = set.Immediate8;
        }
        return _constantFunctions[address] = value;
    }

    private static readonly bool NoUnknownInstantiations = Environment.GetEnvironmentVariable("REWIND_NO_UNKNOWN_INSTANTIATIONS") != null;

    /// <summary>Whether a type argument is, or is made of, "object": what the code shared by every instantiation over classes is listed under.</summary>
    private bool NamesObject(TypeSig t) => t switch
    {
        GenericInstSig g => g.Arguments.Any(NamesObject),
        SzArraySig a => NamesObject(a.ElementType),
        _ => ReferenceEquals(t, _object),
    };

    /// <summary>
    /// Builds the call expression for a chosen method from the captured argument values.
    /// <paramref name="listed"/>: the type arguments are those the code at the call's address is listed under,
    /// not ones that something else told.
    /// </summary>
    private void BuildCall(Node call, MethodDef method, TypeSig[] classArgs, TypeSig[] methodArgs, bool isVirtual, bool tail,
        List<MethodDef>? alternatives, bool skipFirst, Node? receiverOverride = null, int shift = 0, bool listed = false, bool bufferFirst = false,
        IReadOnlyDictionary<int, long>? fixedArguments = null)
    {
        MethodAbi abi = _p.Abi.For(method, classArgs, methodArgs);
        bool classTold = false, methodTold = false;

        // One compiled body serves every instantiation that differs only in reference types, so the callee's
        // address cannot say whether this is List<Creature>.Add or List<string>.Add. Two things can: the
        // method descriptor the shared code is handed, and the type of the receiver.
        foreach (AbiParam p in abi.Params)
        {
            if (p.Role != ParamRole.MethodInfo || IntAt(call, Shifted(p, shift)) is not { } descriptor) continue;
            // The hidden method argument is whatever the register held unless the callee is generic: only looked at.
            if (Peek(descriptor) is SMethod { Inst: { } named } sm && ReferenceEquals(sm.Method, method) &&
                !named.ClassArguments.Any(Open) && !named.MethodArguments.Any(Open))
            {
                classArgs = named.ClassArguments;
                methodArgs = named.MethodArguments;
                abi = _p.Abi.For(method, classArgs, methodArgs);
                classTold = methodTold = true;
            }
            // A call through a constraint is handed the record of the method as the constrained type has it:
            // the method is that type's, with that type's arguments.
            else if (Peek(descriptor) is SConstrained { On: var on } && method.GenericParameters.Length == 0 &&
                     DeclaringArguments(on, method.DeclaringType) is { } constrained && !constrained.Any(Open))
            {
                classArgs = constrained;
                abi = _p.Abi.For(method, classArgs, methodArgs);
                classTold = true;
            }
        }
        if (!method.IsStatic && method.DeclaringType.GenericParameters.Length != 0 && abi.This != null)
        {
            Node? receiverNode = receiverOverride ?? IntAt(call, Shifted(abi.This, shift));
            TypeSig? receiverType = receiverNode == null ? null : Eval(receiverNode) switch
            {
                SNewObject o => o.Type,
                SVal v => v.Type,
                SRef r => r.Type,
                _ => null,
            };
            if (receiverNode != null && receiverType != null && DeclaringArguments(receiverType, method.DeclaringType) == null &&
                _castTypes.TryGetValue(receiverNode, out List<TypeSig>? receiverCasts) && receiverCasts.Count == 1)
                receiverType = receiverCasts[0];
            if (DeclaringArguments(receiverType, method.DeclaringType) is { } exact)
            {
                classArgs = exact;
                abi = _p.Abi.For(method, classArgs, methodArgs);
                classTold = true;
            }
        }
        // Neither said it: the code is listed under "object" because every instantiation over classes shares
        // it, and which of them is called here is not known. Written as the one over object it would read as
        // code that can be compiled and does something else (a List<Creature> is no List<object>).
        if (listed && !NoUnknownInstantiations && ((!classTold && classArgs.Any(NamesObject)) || (!methodTold && methodArgs.Any(NamesObject))))
            Problem($"which instantiation of {method.DeclaringType.Name}.{method.Name} is called was not recovered (its code is shared by every instantiation over classes)");
        ChosenCalls[call] = (method, abi, shift);

        HExpr? thisExpr = null;
        var args = new HExpr[method.Parameters.Length];
        MethodDef? stringConstructor = null;
        HExpr? returnLocation = null;

        foreach (AbiParam p in abi.Params)
        {
            // (Where the invoker is handed the result's address first, that stays where it is.)
            int position = bufferFirst && p.Role == ParamRole.ReturnBuffer ? p.Position : Shifted(p, shift);
            switch (p.Role)
            {
                case ParamRole.MethodInfo:
                    break;
                case ParamRole.ReturnBuffer:
                {
                    Node? node = IntAt(call, position);
                    returnLocation = node != null ? LocationOf(node, abi.ReturnType) : null;
                    if (returnLocation == null) Problem("return buffer location not recovered");
                    break;
                }
                case ParamRole.This:
                {
                    Node? node = receiverOverride ?? IntAt(call, position);
                    if (node == null) { thisExpr = Missing(p.Type!); break; }
                    if (p.Type!.Definition is { IsValueType: true })
                    {
                        thisExpr = LocationOf(node, p.Type);
                        if (thisExpr == null)
                        {
                            Problem($"struct receiver location not recovered on {method.DeclaringType.Name}.{method.Name}");
                            thisExpr = Value(node);
                        }
                    }
                    else if (!NoNullReceivers && node.IsConstValue(0))
                    {
                        // A string constructor: IL2CPP makes each one a method "CreateString" with the same
                        // arguments, called with no object - the string is what it returns.
                        if (StringConstructorOf(method) is { } made) stringConstructor = made;
                        // An instance method handed zero for its object: the code it shares never reads the
                        // object, and the C++ compiler, seeing that, did not keep which one it was. "null" here
                        // would throw where the program does not; what it was called on is not known.
                        else Problem(UnkeptReceiver);
                        thisExpr = new HConst(null, p.Type);
                    }
                    else
                    {
                        thisExpr = Value(node);
                        // A struct wrapping the object (see IsReferenceWrapper): the receiver is the object.
                        if (thisExpr.Type is { } held && IsReferenceWrapper(held)) thisExpr = Coerce(thisExpr, p.Type);
                        if (Eval(node) is SNewObject) { }
                        else if (CheckedClassHere(node) is { } checkedAs && !IsAssignable(thisExpr.Type, p.Type))
                            thisExpr = new HTypeExpr(HTypeOp.CastClass, checkedAs, thisExpr) { Type = checkedAs };
                    }
                    break;
                }
                case ParamRole.Argument:
                {
                    TypeSig type = p.Type!;
                    HExpr arg;
                    // A value the code called through writes in itself (the same at every call).
                    if (fixedArguments != null && fixedArguments.TryGetValue(p.Position, out long bits))
                        arg = ValueFromBits(new HConst(bits, _long), type, Math.Max(1, _p.Layouts.SizeOf(type).Size));
                    else if (p.Pass == PassKind.Float) arg = FloatAt(call, position, p.IsDouble);
                    else if (p.Pass is PassKind.IntegerPair or PassKind.FloatAggregate)
                    {
                        List<Node?> registers = ArgumentRegisters(call, p, position, out Carried how);
                        arg = StructFromRegisters(registers, type, how, call.Addr);
                    }
                    else
                    {
                        Node? node = IntAt(call, position);
                        if (node == null) arg = Missing(type);
                        else if (p.Pass == PassKind.Indirect)
                        {
                            arg = LocationOf(node, type) ?? Value(node);
                        }
                        else if (type is ByRefSig byRef)
                        {
                            HExpr? location = LocationOf(node, byRef.ElementType);
                            arg = location != null ? new HAddressOf(location) { Type = type } : Value(node);
                        }
                        else if (type is PointerSig && !NoWiderPointees && Eval(node) is SFrame frame && BufferAddress(frame.Offset) == null &&
                                 FramePlace(frame.Offset, DirectAccessSize(frame.Offset)) is PLocation { Location: { Type: { } heldType } held })
                        {
                            // The address of a local handed over as a pointer ("(byte*)&value").
                            arg = new HAddressOf(held) { Type = _m.Sigs.ByRef(heldType) };
                        }
                        else
                        {
                            arg = ValueFor(node, type);
                            if (IsReference(type) && CheckedClassHere(node) is { } checkedAs &&
                                !IsAssignable(arg.Type, type) && IsAssignable(checkedAs, type))
                                arg = new HTypeExpr(HTypeOp.CastClass, checkedAs, arg) { Type = checkedAs };
                        }
                    }
                    args[p.ArgumentIndex] = arg;
                    break;
                }
            }
        }
        _ = skipFirst;

        TypeSig? declaring = classArgs.Length != 0 && method.DeclaringType.GenericParameters.Length != 0
            ? _m.Sigs.GenericInst(method.DeclaringType, classArgs)
            : null;

        // A constructor call on a freshly allocated object is "new T(args)".
        Node? receiver = receiverOverride ?? (abi.This != null ? IntAt(call, abi.This.Position + shift) : null);
        if (method.Name == ".ctor" && receiver != null && Eval(receiver) is SNewObject fresh &&
            (!fresh.Constructed || (!NoEarlyCopiedObjects && fresh.Claims.Count > 0)))
        {
            // A second constructor call on an allocation one already claimed: one allocation, a call on each arm.
            if (fresh.Constructed) fresh.Shared = true;
            fresh.Constructed = true;
            bool inlined = false;
            if (fresh.Type.Definition is { } allocated && !ReferenceEquals(allocated, method.DeclaringType))
            {
                // The object is of a derived class but a base class constructor is called on it: the class's
                // own constructor was inlined here. When that constructor does nothing except pass its
                // arguments on to this very call, "new Derived(args)" is the same thing.
                ulong target = call.Aux is CallInfo { Indirect: false } direct ? direct.Target : 0;
                MethodDef? own = null;
                foreach (MethodDef c in allocated.Methods)
                {
                    if (c.Name != ".ctor" || c.IsStatic || c.Address == 0 || c.Parameters.Length != method.Parameters.Length) continue;
                    // A forwarder: at most a register set-up (the unused method descriptor) and a jump to the target.
                    if (c.Address == target || (_p.Code.Get(c.Address) is { Instructions: <= 3, Callees.Count: 1 } code &&
                                                _p.Code.ThunkTarget(code.Callees[0]) == _p.Code.ThunkTarget(target) && !WritesMemory(c.Address)))
                    {
                        own = c;
                        break;
                    }
                }
                if (own != null)
                {
                    method = own;
                    declaring = fresh.Type is GenericInstSig ? fresh.Type : null;
                }
                // Otherwise the statements of the class's constructor were pasted here, and this call is the
                // first of them. It stays an ordinary call on the raw object; putting the constructor back is
                // done afterwards, on the finished statements (ConstructorFolding).
                else inlined = true;
            }
            if (!inlined)
            {
                var created = new HNewObject { Constructor = method, DeclaringType = declaring, Arguments = args, Type = fresh.Type };
                var made = new HAssign(new HLocal(fresh.Variable) { Type = fresh.Type }, created);
                if (NoEarlyCopiedObjects)
                {
                    if (fresh.Allocation != null)
                    {
                        if (!_cur.Statements.Remove(fresh.Allocation))
                            foreach (HBlock block in _h.Blocks)
                                if (block.Statements.Remove(fresh.Allocation))
                                    break;
                        fresh.Allocation = null;
                    }
                }
                else
                {
                    // Whether "new T(args)" can stand for the allocation and this call is settled once every block
                    // is built (SettleNewObjects): until then the allocation stays.
                    fresh.Claims.Add((_cur, made, new HCall
                    {
                        Method = method,
                        DeclaringType = declaring,
                        This = new HLocal(fresh.Variable) { Type = fresh.Type },
                        Arguments = args,
                        Type = abi.ReturnType,
                    }));
                }
                Emit(made, call.Addr);
                if (tail) Emit(new HReturn(null), call.Addr);
                return;
            }
        }

        // Calling a virtual method of a base class directly from an override is "base.Method()"; any other
        // direct call to a virtual method is ordinary dispatch that the compiler devirtualized.
        bool virtualCall = isVirtual;
        if (!isVirtual && method.IsVirtual && !method.DeclaringType.IsValueType)
        {
            bool onThis = thisExpr is HArg { Index: -1 };
            bool baseCall = onThis && !ReferenceEquals(method.DeclaringType, _method.DeclaringType);
            virtualCall = !baseCall;
        }

        if (stringConstructor != null && abi.Return == ReturnKind.Integer)
        {
            FinishCall(call, new HNewObject { Constructor = stringConstructor, Arguments = args, Type = _string }, abi.Return, _string, tail);
            return;
        }

        var expr = new HCall
        {
            Method = method,
            DeclaringType = declaring,
            MethodArguments = methodArgs,
            This = thisExpr,
            Arguments = args,
            Virtual = virtualCall,
            Type = abi.ReturnType,
        };
        if (alternatives != null) expr.Alternatives.AddRange(alternatives);
        if (method.Name == ".ctor" && _method.Name == ".ctor" && thisExpr is HArg { Index: -1 }) _baseConstructorCalled = true;

        if (abi.Return == ReturnKind.Buffer)
        {
            if (returnLocation != null) Emit(new HAssign(returnLocation, expr), call.Addr);
            else Emit(new HEval(expr), call.Addr);
            // The function also returns the buffer address.
            if (Projections(call).TryGetValue(CallResult.IntReturn, out Node? address) && returnLocation != null)
                _sem[address] = new SRef(returnLocation, abi.ReturnType);
            if (tail)
            {
                if (_abi.Return == ReturnKind.Buffer && _returnBuffer != null) Emit(new HReturn(new HLocal(_returnBuffer) { Type = _returnBuffer.Type }), call.Addr);
                else Emit(new HReturn(returnLocation), call.Addr);
            }
            return;
        }
        FinishCall(call, expr, abi.Return, abi.ReturnType, tail);
    }

    // ---- indirect calls: virtual dispatch and delegates --------------------------------------------------------

    /// <summary>
    /// The method a vtable slot denotes for a receiver of the given static type: the least derived method that
    /// occupies the slot, which is the one a compiler names in a callvirt.
    /// </summary>
    private MethodDef? FindVirtual(TypeSig? type, int slot)
    {
        MethodDef? found = null;
        TypeSig? start = type == null ? null : Declared(type);
        // A value of a type parameter: what is known of it is the class its constraints name - or, failing
        // that, that it is an object.
        if (start is GenericParamSig open && !NoParameterSlots)
            start = open.Parameter.Constraints.FirstOrDefault(c => c.Definition is { IsInterface: false, IsValueType: false }) ?? _object;
        for (TypeSig? t = start; t?.Definition != null;)
        {
            TypeDef def = t.Definition;
            foreach (MethodDef m in def.Methods)
                if (m.HasSlot && m.Slot == slot && m.IsVirtual && !m.IsStatic)
                    found = m;
            if (def.BaseType == null) break;
            t = _m.Sigs.Substitute(def.BaseType, t is GenericInstSig g ? g.Arguments : [], []);
        }
        return found;
    }

    /// <summary>
    /// The method each way into a merged code pointer picks, when every way in takes a virtual method's code from
    /// the object's class (or an interface's), and the methods take the same arguments and return the same type.
    /// </summary>
    private MethodDef[]? MergedVirtualTargets(Node phi)
    {
        if (phi.In.Length < 2 || phi.In.Length > 16) return null;
        var ways = new MethodDef[phi.In.Length];
        for (int i = 0; i < phi.In.Length; i++)
        {
            MethodDef? method = null;
            Sem s = Peek(phi.In[i]);
            if (s is SVTable { MethodInfo: false, Interface: { } iface } it)
                method = iface.Definition?.Methods.FirstOrDefault(m => m.HasSlot && m.Slot == it.Slot);
            else if (s is SVTable { MethodInfo: false } vt)
            {
                TypeSig? receiverType = Peek(vt.Object) is SVal { Type: { } t } ? t : null;
                if (_castTypes.TryGetValue(vt.Object, out List<TypeSig>? casts) && casts.Count == 1) receiverType = casts[0];
                if (receiverType != null) method = FindVirtual(Declared(receiverType), vt.Slot);
            }
            if (method == null || method.IsStatic || method.GenericParameters.Length != 0 || method.DeclaringType.GenericParameters.Length != 0) return null;
            ways[i] = method;
        }
        MethodDef first = ways[0];
        foreach (MethodDef m in ways)
            if (m.Parameters.Length != first.Parameters.Length || m.ReturnType.Key != first.ReturnType.Key ||
                m.Parameters.Zip(first.Parameters).Any(p => p.First.Type.Key != p.Second.Type.Key))
                return null;
        return ways;
    }

    private static readonly bool NoNestedMergedTargets = Environment.GetEnvironmentVariable("REWIND_NO_NESTED_MERGED_TARGETS") != null;

    /// <summary>
    /// A merged code pointer some of whose ways in are merges themselves (ways that met before this point), each
    /// way at the end taking the same virtual method's code from the class of the object it is called on: that
    /// method, called on that object. (Where the ways pick different methods, only a merge of plain ways is
    /// taken apart, above.)
    /// </summary>
    private MethodDef? OneMergedVirtualTarget(Node phi, Node? callReceiver)
    {
        var leaves = new List<Node>();
        var seen = new HashSet<Node>();
        bool Collect(Node n, int depth)
        {
            if (!seen.Add(n)) return true;
            if (n.Op != Op.Phi) { leaves.Add(n); return true; }
            if (depth > 4 || n.In.Length > 16) return false;
            foreach (Node input in n.In)
                if (!Collect(input, depth + 1)) return false;
            return true;
        }
        if (!Collect(phi, 0) || leaves.Count < 2 || leaves.Count > 32) return null;
        MethodDef? only = null;
        Node? receiver = null;
        foreach (Node leaf in leaves)
        {
            if (Peek(leaf) is not SVTable { MethodInfo: false, Interface: null } vt) return null;
            TypeSig? receiverType = Peek(vt.Object) is SVal { Type: { } t } ? t : null;
            if (_castTypes.TryGetValue(vt.Object, out List<TypeSig>? casts) && casts.Count == 1) receiverType = casts[0];
            MethodDef? method = receiverType != null ? FindVirtual(Declared(receiverType), vt.Slot) : null;
            if (method == null || method.IsStatic || method.GenericParameters.Length != 0 || method.DeclaringType.GenericParameters.Length != 0) return null;
            // (One object throughout: the call's receiver is then the object every way read the class of.)
            if ((only != null && !ReferenceEquals(only, method)) || (receiver != null && !ReferenceEquals(receiver, vt.Object))) return null;
            only = method;
            receiver = vt.Object;
        }
        return callReceiver != null && ReferenceEquals(callReceiver, receiver) ? only : null;
    }

    /// <summary>
    /// The call of a merged code pointer whose ways in each picked a virtual method: a branch (or a switch) on the
    /// number of the method, each arm calling its method with the call's arguments, all meeting again after it.
    /// </summary>
    private void EmitDispatch(Node call, HVar which, MethodDef[] methods, bool tail)
    {
        // The number is read here: the copies into it stay (see SettlePhis).
        _phiRead.Add(call.In[0]);
        int scope = _cur.Scope;
        HBlock NewBlock()
        {
            var block = new HBlock { Id = _h.Blocks.Count, Scope = scope };
            _h.Blocks.Add(block);
            return block;
        }
        HBlock[] arms = methods.Select(_ => NewBlock()).ToArray();
        HBlock? join = tail ? null : NewBlock();
        var chosen = new HLocal(which) { Type = _int };
        if (arms.Length == 2) Emit(new HBranch(new HCompare(HCompareOp.Eq, chosen, new HConst(0, _int)) { Type = _bool }, arms[0], arms[1]), call.Addr);
        else Emit(new HSwitch(chosen, arms[..^1], arms[^1]), call.Addr);
        for (int j = 0; j < arms.Length; j++)
        {
            _cur = arms[j];
            BuildCall(call, methods[j], [], [], isVirtual: true, tail, null, skipFirst: false);
            if (join != null) Emit(new HJump(join), call.Addr);
        }
        if (join != null) _cur = join;
    }

    /// <summary>
    /// "ldvirtftn": a virtual slot of an object's class read as a value - what a delegate made from a virtual
    /// method ("new Action(this.OnChanged)") is constructed with.
    /// </summary>
    private HExpr? VirtualPointer(SVTable entry)
    {
        if (Value(entry.Object) is not HArg receiver) return null;
        MethodDef? method;
        TypeSig? declaring = null;
        if (entry.Interface is { } iface)
        {
            method = iface.Definition?.Methods.FirstOrDefault(m => m.HasSlot && m.Slot == entry.Slot);
            if (iface is GenericInstSig) declaring = iface;
        }
        else
        {
            TypeSig? receiverType = receiver.Type;
            if (_castTypes.TryGetValue(entry.Object, out List<TypeSig>? casts) && casts.Count == 1) receiverType = casts[0];
            method = FindVirtual(receiverType, entry.Slot);
            if (method != null && receiverType is GenericInstSig g && ReferenceEquals(g.Definition, method.DeclaringType)) declaring = g;
            else if (method != null && method.DeclaringType.GenericParameters.Length != 0) return null; // declared in a generic base: not followed
        }
        if (method == null || method.GenericParameters.Length != 0) return null;
        return new HMethodPointer { Method = method, DeclaringType = declaring, VirtualOn = receiver, Type = _nint };
    }

    private void EmitIndirectCall(Node call, bool tail)
    {
        Node targetNode = call.In[0];
        // The code of one virtual method or another, by the way in, then called: the compiler merged the calls
        // of "if (dying) HandleDie(); else HandleRevive();" into one.
        if (!NoMergedDispatch && targetNode.Op == Op.Phi)
        {
            if (_dispatch.TryGetValue(targetNode, out var known))
            {
                EmitDispatch(call, known.Which, known.Distinct, tail);
                return;
            }
            if (MergedVirtualTargets(targetNode) is { } ways)
            {
                if (ways.Distinct().Count() == 1)
                {
                    BuildCall(call, ways[0], [], [], isVirtual: true, tail, null, skipFirst: false);
                    return;
                }
                // (The calls return nothing that is used: one result made of several calls' is not built yet.)
                if (!Projections(call).Values.Any(IsUsed))
                {
                    DispatchPhis[targetNode] = ways;
                    DispatchRefined = true;
                }
            }
            else if (!NoNestedMergedTargets && OneMergedVirtualTarget(targetNode, IntAt(call, 0)) is { } only)
            {
                BuildCall(call, only, [], [], isVirtual: true, tail, null, skipFirst: false);
                return;
            }
        }
        Sem target = Eval(targetNode);

        if (target is SNativeCode native)
        {
            // The implementation takes the method's own arguments (and no trailing method descriptor).
            BuildCall(call, native.Method, [], [], isVirtual: false, tail, null, skipFirst: false);
            return;
        }
        if (target is SMethodCode code)
        {
            // The code pointer of a method's own record, called with the method's arguments and the record itself.
            BuildCall(call, code.Method, code.Inst?.ClassArguments ?? [], code.Inst?.MethodArguments ?? [], isVirtual: false, tail, null, skipFirst: false);
            return;
        }
        if (target is SPInvoke pinvoke)
        {
            if (TryBuildPInvokeCall(call, pinvoke.Method, tail)) return;
            Problem($"marshaled arguments of a call to {pinvoke.Method.Name} not recovered");
        }
        if (target is SVTable { MethodInfo: false, Interface: { } iface } it)
        {
            MethodDef? interfaceMethod = iface.Definition?.Methods.FirstOrDefault(m => m.HasSlot && m.Slot == it.Slot);
            if (interfaceMethod != null)
            {
                BuildCall(call, interfaceMethod, iface is GenericInstSig gi ? gi.Arguments : [], [], isVirtual: true, tail, null, skipFirst: false, receiverOverride: it.Object);
                return;
            }
            Problem($"interface slot {it.Slot} not found on {iface.DisplayName}");
        }
        else if (target is SVTable { MethodInfo: false } vt)
        {
            HExpr receiver = Value(vt.Object);
            TypeSig? receiverType = receiver.Type;
            if (_castTypes.TryGetValue(vt.Object, out List<TypeSig>? casts) && casts.Count == 1) receiverType = casts[0];
            if (receiverType != null) receiverType = Declared(receiverType);
            MethodDef? method = FindVirtual(receiverType, vt.Slot);
            if (method != null)
            {
                TypeSig[] classArgs = receiverType is GenericInstSig g && ReferenceEquals(g.Definition, method.DeclaringType) ? g.Arguments : [];
                BuildCall(call, method, classArgs, [], isVirtual: true, tail, null, skipFirst: false);
                return;
            }
            Problem($"virtual slot {vt.Slot} not found on {receiverType?.DisplayName ?? "unknown type"}");
        }
        else if ((target is SVal { Expr: HField { Field.Name: "invoke_impl", Object: not null } } ||
                  (target is SVal { Expr: HLocal held } && _fieldTemps.TryGetValue(held.Variable, out HField? loaded) && loaded is { Field.Name: "invoke_impl", Object: not null })) &&
                 ((target as SVal)!.Expr is HField direct ? direct.Object : _fieldTemps[((HLocal)((SVal)target).Expr).Variable].Object) is { } del)
        {
            // Delegate invocation: invoke_impl(method_code, args..., method). The managed call is Invoke(args).
            TypeDef? delegateType = del.Type?.Definition;
            MethodDef? invoke = delegateType?.Methods.FirstOrDefault(m => m.Name == "Invoke");
            if (invoke != null && delegateType != null)
            {
                TypeSig[] classArgs = del.Type is GenericInstSig g ? g.Arguments : [];
                BuildDelegateInvoke(call, del, invoke, classArgs, tail);
                return;
            }
            Problem("delegate type for invocation not recovered");
        }
        else Problem($"indirect call through {target.GetType().Name[1..]}");

        var args = new List<HExpr> { Value(targetNode) };
        for (int i = 0; i < 4; i++)
            if (IntAt(call, i) is { } a && Eval(a) is not SJunk)
                args.Add(Value(a));
        FinishCall(call, new HOpaque("call_indirect", args.ToArray()) { Type = _long }, ReturnKind.Integer, _long, tail);
    }

    /// <summary>
    /// A call through the function a P/Invoke declaration imports, with the arguments as the inlined wrapper
    /// marshaled them, as a call of the declaration with the managed values. Only marshaling that maps back
    /// exactly is undone: values passed as they are, bools passed as 4-byte BOOL, and strings pinned as UTF-16.
    /// </summary>
    private bool TryBuildPInvokeCall(Node call, MethodDef method, bool tail)
    {
        if (!method.IsStatic || method.GenericParameters.Length != 0) return false;
        PInvokeImport? import = _p.PInvokeOf(method);
        var arguments = new HExpr[method.Parameters.Length];
        int ints = 0, floats = 0;
        for (int i = 0; i < arguments.Length; i++)
        {
            TypeSig type = method.Parameters[i].Type;
            if (IsFloat(type))
            {
                arguments[i] = FloatAt(call, _fn.Regs.SharedPositions ? i : FloatArgPosition(floats), BitsOf(type) == 64);
                floats++;
                continue;
            }
            int at = IntArgPosition(ints++, floats);
            if (!_fn.Regs.SharedPositions && at >= 8) return false;
            if (IntAt(call, _fn.Regs.SharedPositions ? i : at) is not { } native || Unmarshal(native, type, import) is not { } value) return false;
            arguments[i] = value;
        }
        TypeSig returnType = method.ReturnType;
        ReturnKind kind;
        if (returnType.IsVoid) kind = ReturnKind.Void;
        else if (IsFloat(returnType)) kind = BitsOf(returnType) == 64 ? ReturnKind.Double : ReturnKind.Float;
        else if (IsPassedAsIs(returnType) || ReferenceEquals(returnType, _bool)) kind = ReturnKind.Integer;
        else return false;
        // (What the call takes is the method's arguments, in their places, and nothing after them.)
        if (!NoPInvokeChoices) ChosenCalls[call] = (method, _p.Abi.For(method, [], []), 0);
        FinishCall(call, new HCall { Method = method, Arguments = arguments, Type = returnType }, kind, returnType, tail);
        return true;
    }

    private static readonly bool NoPInvokeChoices = Environment.GetEnvironmentVariable("REWIND_NO_PINVOKE_CHOICES") != null;
    private static readonly bool NoNullReceivers = Environment.GetEnvironmentVariable("REWIND_NO_NULL_RECEIVERS") != null;
    internal const string UnkeptReceiver = "an instance method called on an object the code did not keep";

    /// <summary>The string constructor a "CreateString" method of System.String stands for: the one that takes the same arguments.</summary>
    private MethodDef? StringConstructorOf(MethodDef method)
    {
        if (method.Name != "CreateString" || _string.Definition is not { } type || !ReferenceEquals(method.DeclaringType, type)) return null;
        foreach (MethodDef candidate in type.Methods)
        {
            if (candidate.Name != ".ctor" || candidate.IsStatic || candidate.Parameters.Length != method.Parameters.Length) continue;
            bool same = true;
            for (int i = 0; i < candidate.Parameters.Length && same; i++)
                same = candidate.Parameters[i].Type.Key == method.Parameters[i].Type.Key;
            if (same) return candidate;
        }
        return null;
    }

    /// <summary>Types the marshaler passes unchanged: numbers, chars, pointers, native ints, enums.</summary>
    private static bool IsPassedAsIs(TypeSig type) => type switch
    {
        PointerSig => true,
        PrimitiveSig { Element: Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4
            or Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.I or Il2CppTypeEnum.U } => true,
        _ => type.Definition is { IsEnum: true },
    };

    /// <summary>A struct the marshaler hands over in place: all its instance fields are numbers, pointers, enums or such structs.</summary>
    private static bool IsBlittableStruct(TypeSig type, int depth = 0)
    {
        if (depth > 8 || type.Definition is not { IsValueType: true, IsEnum: false } definition || type is PrimitiveSig || type is GenericInstSig) return false;
        foreach (FieldDef field in definition.Fields)
        {
            if (field.IsStatic) continue;
            if (!IsPassedAsIs(field.Type) && !IsBlittableStruct(field.Type, depth + 1)) return false;
        }
        return true;
    }

    private HExpr? Unmarshal(Node native, TypeSig type, PInvokeImport? import)
    {
        if (IsPassedAsIs(type)) return ValueFor(native, type);
        if (type is ByRefSig byRef && (IsPassedAsIs(byRef.ElementType) || IsBlittableStruct(byRef.ElementType)))
        {
            // ref/out of something the marshaler does not convert: the location itself is passed.
            HExpr? location = LocationOf(native, byRef.ElementType);
            return location == null ? null : new HAddressOf(location) { Type = type };
        }
        if (ReferenceEquals(type, _bool))
        {
            // BOOL: the bool widened to four bytes.
            HExpr value = Value(native);
            while (value is HConv conv && !ReferenceEquals(value.Type, _bool)) value = conv.Operand;
            return ReferenceEquals(value.Type, _bool) ? value : null;
        }
        if (ReferenceEquals(type, _string) && import?.CharSet == PInvokeImport.CharSetUnicode)
        {
            // Pinned UTF-16: s == null ? null : &s._firstChar.
            if (Value(native) is HSelect { WhenTrue: var a, WhenFalse: var b })
            {
                HExpr? Chars(HExpr e) => e is HAddressOf { Target: HField { Field.Name: "_firstChar", Object: { } s } } && ReferenceEquals(s.Type, _string) ? s : null;
                bool IsNull(HExpr e) => e is HConst { Value: null or 0L or 0 };
                if (Chars(b) is { } fromB && IsNull(a)) return fromB;
                if (Chars(a) is { } fromA && IsNull(b)) return fromA;
            }
            return null;
        }
        return null;
    }

    private void BuildDelegateInvoke(Node call, HExpr del, MethodDef invoke, TypeSig[] classArgs, bool tail)
    {
        MethodAbi abi = _p.Abi.For(invoke, classArgs, []);
        ChosenCalls[call] = (invoke, abi, 0);
        var args = new HExpr[invoke.Parameters.Length];
        HExpr? returnLocation = null;
        foreach (AbiParam p in abi.Params)
        {
            switch (p.Role)
            {
                case ParamRole.ReturnBuffer:
                    returnLocation = IntAt(call, p.Position) is { } rb ? LocationOf(rb, abi.ReturnType) : null;
                    break;
                case ParamRole.Argument:
                {
                    TypeSig type = p.Type!;
                    if (p.Pass == PassKind.Float) args[p.ArgumentIndex] = FloatAt(call, p.Position, p.IsDouble);
                    else if (p.Pass is PassKind.IntegerPair or PassKind.FloatAggregate)
                        args[p.ArgumentIndex] = StructFromRegisters(ArgumentRegisters(call, p, p.Position, out Carried how), type, how, call.Addr);
                    else if (IntAt(call, p.Position) is not { } node) args[p.ArgumentIndex] = Missing(type);
                    else if (p.Pass == PassKind.Indirect) args[p.ArgumentIndex] = LocationOf(node, type) ?? Value(node);
                    else if (type is ByRefSig byRef && LocationOf(node, byRef.ElementType) is { } location)
                        args[p.ArgumentIndex] = new HAddressOf(location) { Type = type };
                    else args[p.ArgumentIndex] = ValueFor(node, type);
                    break;
                }
            }
        }
        var expr = new HCall
        {
            Method = invoke,
            DeclaringType = classArgs.Length != 0 ? del.Type : null,
            This = del,
            Arguments = args,
            Virtual = true,
            Type = abi.ReturnType,
        };
        if (abi.Return == ReturnKind.Buffer)
        {
            if (returnLocation != null) Emit(new HAssign(returnLocation, expr), call.Addr);
            else Emit(new HEval(expr), call.Addr);
            if (tail) Emit(new HReturn(_returnBuffer != null ? new HLocal(_returnBuffer) { Type = _returnBuffer.Type } : returnLocation), call.Addr);
            return;
        }
        FinishCall(call, expr, abi.Return, abi.ReturnType, tail);
    }

    // ---- runtime helpers ---------------------------------------------------------------------------------------

    private HExpr NewException(string typeName)
    {
        TypeDef? type = _m.FindType(typeName);
        MethodDef? ctor = type?.Methods.FirstOrDefault(m => m.Name == ".ctor" && m.Parameters.Length == 0);
        if (type == null || ctor == null) return new HOpaque("new_" + typeName.Replace('.', '_'));
        return new HNewObject { Constructor = ctor, Arguments = [], Type = type.Sig };
    }

    /// <summary>
    /// A call to the System.Math (or MathF) method that a C runtime math function stands for. Unity's class
    /// library predates MathF in older versions; there the single precision form is the double method between
    /// two conversions, which computes the same value.
    /// </summary>
    private HExpr MathCall(string name, bool isDouble, params HExpr[] args)
    {
        TypeSig type = isDouble ? _double : _float;
        // (A class this code can name: Unity 2020's System.Numerics has a MathF of its own that nothing outside it sees.)
        bool Usable(TypeDef owner) => (owner.Flags & TypeDef.VisibilityMask) == 1 || ReferenceEquals(owner.Assembly, _method.DeclaringType.Assembly);
        MethodDef? Find(string typeName, TypeSig operand) => _m.FindType(typeName) is { } owner && Usable(owner) ? owner.Methods.FirstOrDefault(m =>
            m.IsStatic && m.Name == name && m.Parameters.Length == args.Length && ReferenceEquals(m.ReturnType, operand) &&
            m.Parameters.All(p => ReferenceEquals(p.Type, operand)) && IsAccessible(m)) : null;

        MethodDef? method = isDouble ? Find("System.Math", _double) : Find("System.MathF", _float) ?? Find("System.Math", _float);
        if (method != null) return new HCall { Method = method, Arguments = args, Type = type };
        if (!isDouble && Find("System.Math", _double) is { } wide)
        {
            HExpr[] widened = args.Select(a => (HExpr)new HConv(HConvKind.R8, a) { Type = _double }).ToArray();
            return new HConv(HConvKind.R4, new HCall { Method = wide, Arguments = widened, Type = _double }) { Type = _float };
        }
        Problem($"math function {name} has no managed counterpart in this build");
        return new HOpaque(name.ToLowerInvariant(), args) { Type = type };
    }

    private void EmitHelperCall(Node call, HelperInfo helper, bool tail)
    {
        Dictionary<int, Node> projs = Projections(call);
        projs.TryGetValue(CallResult.IntReturn, out Node? result);
        Node? a0 = IntAt(call, 0), a1 = IntAt(call, 1), a2 = IntAt(call, 2);

        switch (helper.Kind)
        {
            case HelperKind.MathFunction:
            {
                var operands = new HExpr[helper.FloatArgs];
                for (int i = 0; i < operands.Length; i++) operands[i] = FloatAt(call, FloatArgPosition(i), helper.IsDouble);
                TypeSig type = helper.IsDouble ? _double : _float;
                // fmod is the IL "rem" instruction applied to floating point operands.
                HExpr value = helper.MathName == "fmod" && operands.Length == 2
                    ? new HBinary(HBinaryOp.Rem, operands[0], operands[1]) { Type = type }
                    : MathCall(helper.MathName, helper.IsDouble, operands);
                FinishCall(call, value, helper.IsDouble ? ReturnKind.Double : ReturnKind.Float, type, tail);
                return;
            }
            case HelperKind.Modf:
            {
                // modf(x, &whole): the whole part is x truncated toward zero, the result is what is left - and
                // for an infinity a zero of its sign, where "x - whole" would give NaN.
                TypeSig type = helper.IsDouble ? _double : _float;
                Node? pointer = IntAt(call, IntArgPosition(0, 1));
                HExpr? location = pointer != null ? LocationOf(pointer, type) : null;
                MethodDef? isInfinity = _m.FindType(helper.IsDouble ? "System.Double" : "System.Single")?.Methods
                    .FirstOrDefault(m => m.Name == "IsInfinity" && m.IsStatic && m.Parameters.Length == 1);
                if (location == null || isInfinity == null) break;
                HVar x = _h.NewLocal(type, "t"), whole = _h.NewLocal(type, "t");
                HExpr X() => new HLocal(x) { Type = type };
                HExpr Whole() => new HLocal(whole) { Type = type };
                Emit(new HAssign(X(), FloatAt(call, FloatArgPosition(0), helper.IsDouble)), call.Addr);
                Emit(new HAssign(Whole(), MathCall("Truncate", helper.IsDouble, [X()])), call.Addr);
                Emit(new HAssign(location, Whole()), call.Addr);
                HExpr zero = helper.IsDouble ? new HConst(0.0, type) : new HConst(0f, type);
                HExpr fraction = new HSelect(new HCall { Method = isInfinity, Arguments = [X()], Type = _bool },
                    new HBinary(HBinaryOp.Div, zero, X()) { Type = type },
                    new HBinary(HBinaryOp.Sub, X(), Whole()) { Type = type }) { Type = type };
                FinishCall(call, fraction, helper.IsDouble ? ReturnKind.Double : ReturnKind.Float, type, tail);
                return;
            }
            case HelperKind.ObjectNew:
            {
                TypeSig? type = a0 != null ? EvalKlass(a0) : null;
                if (type == null) break;
                HVar variable = _h.NewLocal(type, "o");
                if (result != null)
                {
                    // Until a constructor call claims it, the object is what the machine made: zeroed memory of
                    // that class.
                    var fresh = new SNewObject(type, variable)
                    {
                        Allocation = new HAssign(new HLocal(variable) { Type = type }, new HTypeExpr(HTypeOp.Allocate, type, null) { Type = type }),
                    };
                    _freshObjects.Add(fresh);
                    Emit(fresh.Allocation, call.Addr);
                    _sem[result] = fresh;
                }
                return;
            }
            case HelperKind.SzArrayNew:
            {
                TypeSig? type = a0 != null ? EvalKlass(a0) : null;
                if (type is not SzArraySig array || a1 == null) break;
                FinishCall(call, new HNewArray(array.ElementType, IntValue(a1)) { Type = type }, ReturnKind.Integer, type, tail);
                return;
            }
            case HelperKind.Box:
            {
                TypeSig? type = a0 != null ? EvalKlass(a0) : null;
                if (type == null || a1 == null) break;
                HExpr? location = LocationOf(a1, type);
                if (location == null) break;
                FinishCall(call, new HTypeExpr(HTypeOp.Box, type, location) { Type = _object }, ReturnKind.Integer, _object, tail);
                return;
            }
            case HelperKind.Unbox:
                if (a0 == null || result == null) break;
                _sem[result] = new SUnboxed(a0);
                return;
            case HelperKind.ArraySetAt or HelperKind.ArrayGetAt or HelperKind.ArrayGetAddressAt:
            {
                // An array's own accessors (GetAt, SetAt, GetAddressAt: the bounds check, then the element),
                // which clang keeps as functions of their own: array[index].
                if (a0 == null || a1 == null || Value(a0) is not { Type: SzArraySig arrayType } array) break;
                TypeSig elementType = arrayType.ElementType;
                HExpr index = IndexValue(a1, 0);
                if (index is HConst { Value: long fixedIndex } && fixedIndex is >= 0 and <= int.MaxValue) index = new HConst((int)fixedIndex, _int);
                var element = new HElement { Array = array, Index = index, Type = elementType };
                if (helper.Kind == HelperKind.ArrayGetAddressAt)
                {
                    if (result != null) _sem[result] = new SRef(element, elementType);
                    if (tail) Emit(new HReturn(null), call.Addr);
                    return;
                }
                // A value in one register: a reference, a primitive, an enum.
                bool isFloat = elementType is PrimitiveSig { Element: Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8 };
                bool isDouble = elementType is PrimitiveSig { Element: Il2CppTypeEnum.R8 };
                if (!(IsReference(elementType) || elementType is PrimitiveSig { Element: not Il2CppTypeEnum.TypedByRef } or PointerSig ||
                      elementType.Definition is { IsEnum: true })) break;
                if (helper.Kind == HelperKind.ArrayGetAt)
                {
                    FinishCall(call, element, isDouble ? ReturnKind.Double : isFloat ? ReturnKind.Float : ReturnKind.Integer, elementType, tail);
                    return;
                }
                HExpr value;
                if (isFloat) value = FloatAt(call, _fn.Regs.SharedPositions ? 2 : FloatArgPosition(0), isDouble);
                else if (a2 != null) value = Value(a2);
                else break;
                Emit(new HAssign(element, Coerce(value, elementType)), call.Addr);
                if (tail) Emit(new HReturn(null), call.Addr);
                return;
            }
            case HelperKind.UnboxChecked:
            {
                // The class it checks the object against is the type of the value inside.
                if (a0 == null || a1 == null || EvalKlass(a1) is not { } boxedType) break;
                if (!_castTypes.TryGetValue(a0, out List<TypeSig>? known)) _castTypes[a0] = known = [];
                if (!known.Contains(boxedType)) known.Insert(0, boxedType);
                AddCastPlace(a0, _block, call);
                if (result != null) _sem[result] = new SUnboxed(a0);
                return;
            }
            case HelperKind.SinCos:
            {
                TypeSig type = helper.IsDouble ? _double : _float;
                Node? sine = IntAt(call, IntArgPosition(0, 1)), cosine = IntAt(call, IntArgPosition(1, 1));
                HExpr? sineAt = sine != null ? LocationOf(sine, type) : null, cosineAt = cosine != null ? LocationOf(cosine, type) : null;
                if (sineAt == null || cosineAt == null) break;
                HVar x = _h.NewLocal(type, "t");
                Emit(new HAssign(new HLocal(x) { Type = type }, FloatAt(call, FloatArgPosition(0), helper.IsDouble)), call.Addr);
                Emit(new HAssign(sineAt, MathCall("Sin", helper.IsDouble, new HLocal(x) { Type = type })), call.Addr);
                Emit(new HAssign(cosineAt, MathCall("Cos", helper.IsDouble, new HLocal(x) { Type = type })), call.Addr);
                return;
            }
            case HelperKind.IsInst:
            {
                TypeSig? type = a1 != null ? EvalKlass(a1) : null;
                if (type == null || a0 == null) break;
                FinishCall(call, new HTypeExpr(HTypeOp.IsInst, type, Value(a0)) { Type = type }, ReturnKind.Integer, type, tail);
                return;
            }
            case HelperKind.InterlockedCompareExchange or HelperKind.InterlockedExchange:
            {
                // The runtime's implementation works on raw pointers; the method it stands for is generic in
                // the type of the location.
                bool compare = helper.Kind == HelperKind.InterlockedCompareExchange;
                if (a0 == null || a1 == null || (compare && a2 == null)) break;
                HExpr? location = LocationOf(a0, null);
                TypeSig? type = location?.Type;
                MethodDef? method = _m.FindType("System.Threading.Interlocked")?.Methods.FirstOrDefault(m =>
                    m.Name == (compare ? "CompareExchange" : "Exchange") && m.GenericParameters.Length == 1 && m.Parameters.Length == (compare ? 3 : 2));
                if (location == null || type == null || method == null || !IsReference(type)) break;
                HExpr[] arguments = compare
                    ? [new HAddressOf(location) { Type = _m.Sigs.ByRef(type) }, ValueFor(a1, type), ValueFor(a2!, type)]
                    : [new HAddressOf(location) { Type = _m.Sigs.ByRef(type) }, ValueFor(a1, type)];
                FinishCall(call, new HCall { Method = method, MethodArguments = [type], Arguments = arguments, Type = type }, ReturnKind.Integer, type, tail);
                return;
            }
            case HelperKind.IsAssignableFrom:
            {
                // class_is_assignable_from(K, obj->klass): "obj is K" (the object is not null: its class was read).
                if (a0 == null || a1 == null || EvalKlass(a0) is not { } type || Eval(a1) is not SObjKlass { Object: var subject }) break;
                // (Of a struct type the object is a boxed one: there is one or there is none, as with any object.)
                HExpr test = new HCompare(HCompareOp.Ne, new HTypeExpr(HTypeOp.IsInst, type, Value(subject)) { Type = type }, new HConst(null, IsReference(type) ? type : _object)) { Type = _bool };
                FinishCall(call, test, ReturnKind.Integer, _bool, tail);
                return;
            }
            case HelperKind.CxxThrow:
            {
                // In a catch handler IL2CPP passes an exception on by throwing a copy of its wrapper: the first
                // argument points at a frame slot that was just given the caught exception.
                if (a0 != null && IsFrameAddress(a0, out int copyAt) && StoredBefore(call, copyAt) is { } stored &&
                    Eval(stored) is SVal { Expr: HLocal { Variable: var thrown } } &&
                    _h.TryRegions.Values.FirstOrDefault(r => ReferenceEquals(r.Exception, thrown)) is { } caughtIn &&
                    InHandlerOf(call.Block!.Scope, caughtIn.Index))
                {
                    Emit(new HThrow(null), call.Addr);
                    return;
                }
                Problem("C++ exception thrown by native code");
                Emit(new HThrow(new HOpaque("cxx_throw")), call.Addr);
                return;
            }
            case HelperKind.CastClass:
            {
                TypeSig? type = a1 != null ? EvalKlass(a1) : null;
                if (type == null || a0 == null) break;
                FinishCall(call, new HTypeExpr(HTypeOp.CastClass, type, Value(a0)) { Type = type }, ReturnKind.Integer, type, tail);
                return;
            }
            case HelperKind.GetType:
            {
                // The MethodInfo of the Type.GetType overload is passed along: it names the method exactly.
                int bools = helper.IntArgs - 3;
                Node? descriptor = IntAt(call, 1 + bools);
                if (a0 == null || descriptor == null || Eval(descriptor) is not SMethod { Method: var getType }) break;
                var arguments = new List<HExpr> { ValueFor(a0, _string) };
                for (int i = 0; i < bools; i++)
                    if (IntAt(call, 1 + i) is { } flag) arguments.Add(ValueFor(flag, _bool));
                if (getType.Parameters.Length != arguments.Count) break;
                FinishCall(call, new HCall { Method = getType, Arguments = arguments.ToArray(), Type = getType.ReturnType }, ReturnKind.Integer, getType.ReturnType, tail);
                return;
            }
            case HelperKind.Memcpy or HelperKind.Memset:
            {
                // A struct returned through a buffer, filled last by a copy the compiler jumps to: what is
                // returned is the buffer.
                bool buffer = _abi.Return == ReturnKind.Buffer && _returnBuffer != null;
                if (tail && _abi.Return != ReturnKind.Void && !buffer) break;
                if (!TryEmitBlockOp(call)) break;
                if (result != null && a0 != null) _sem[result] = Eval(a0); // both return the destination
                if (tail) Emit(new HReturn(buffer ? new HLocal(_returnBuffer!) { Type = _returnBuffer!.Type } : null), call.Addr);
                return;
            }
            case HelperKind.InitObj:
            {
                if (a0 == null) break;
                HExpr? location = LocationOf(a0, null);
                if (location?.Type == null) break;
                Emit(new HAssign(location, new HTypeExpr(HTypeOp.Default, location.Type, null) { Type = location.Type }), call.Addr);
                if (tail) Emit(new HReturn(null), call.Addr);
                return;
            }
            case HelperKind.FakeBoxInit:
            {
                // The box header was registered before translation (FindFakeBoxes); what remains is the copy of
                // the value into the box.
                if (a0 == null || a2 == null || !IsFrameAddress(a0, out int boxAt) || !_fakeBoxes.TryGetValue(boxAt, out TypeSig? boxed)) break;
                HExpr? source = LocationOf(a2, boxed);
                if (source == null) break;
                Emit(new HAssign(new HLocal(FrameVar(boxAt + _header, boxed)) { Type = boxed }, source), call.Addr);
                if (result != null) _sem[result] = new SFrame(boxAt);
                return;
            }
            case HelperKind.RaiseProfileException:
            {
                TypeDef? exceptionType = _m.FindType("System.NotSupportedException");
                MethodDef? ctor = exceptionType?.Methods.FirstOrDefault(m => m.Name == ".ctor" && m.Parameters.Length == 1 &&
                    ReferenceEquals(m.Parameters[0].Type, _string));
                if (exceptionType == null || ctor == null) break;
                MethodDef subject = a0 != null && Eval(a0) is SMethod { Method: var m } ? m : _method;
                _h.Notes.Add("this method throws NotSupportedException when called (IL2CPP removed its body); the message text is approximate");
                Emit(new HThrow(new HNewObject { Constructor = ctor, Arguments = [new HConst(subject.FullName, _string)], Type = exceptionType.Sig }), call.Addr);
                return;
            }
            case HelperKind.Throw:
                if (a0 == null) break;
                Emit(new HThrow(Value(a0)), call.Addr);
                return;
            case HelperKind.StoreLastError:
                return; // part of calling a declaration with SetLastError, which the call itself does
            case HelperKind.Rethrow:
                // Outside a catch clause (the code after a try/finally's handler) this throws the stored exception again.
                Emit(new HThrow(a0 != null ? ValueFor(a0, _m.FindType("System.Exception")?.Sig ?? _object) : null), call.Addr);
                return;
            case HelperKind.ThrowNullReference:
                Emit(new HThrow(NewException("System.NullReferenceException")), call.Addr);
                return;
            case HelperKind.ThrowIndexOutOfRange:
                Emit(new HThrow(NewException("System.IndexOutOfRangeException")), call.Addr);
                return;
            case HelperKind.ThrowDivideByZero:
                Emit(new HThrow(NewException("System.DivideByZeroException")), call.Addr);
                return;
            case HelperKind.ThrowInvalidCast:
                Emit(new HThrow(NewException("System.InvalidCastException")), call.Addr);
                return;
            case HelperKind.GetOverflowException:
                FinishCall(call, NewException("System.OverflowException"), ReturnKind.Integer, _object, tail);
                return;
            case HelperKind.GetArrayTypeMismatchException:
                FinishCall(call, NewException("System.ArrayTypeMismatchException"), ReturnKind.Integer, _object, tail);
                return;
            case HelperKind.GetIndexOutOfRangeException:
                FinishCall(call, NewException("System.IndexOutOfRangeException"), ReturnKind.Integer, _object, tail);
                return;
            case HelperKind.VirtualInvoker:
            {
                // Invoke(slot, obj, args...) - or Invoke(&result, slot, obj, args...)
                bool buffer = helper.BufferFirst;
                Node? slotNode = buffer ? IntAt(call, 1) : a0, objectNode = buffer ? IntAt(call, 2) : a1;
                if (slotNode == null || !slotNode.IsConst || objectNode == null) break;
                HExpr receiver = Value(objectNode);
                TypeSig? receiverType = receiver.Type;
                if (_castTypes.TryGetValue(objectNode, out List<TypeSig>? casts) && casts.Count == 1) receiverType = casts[0];
                MethodDef? method = FindVirtual(receiverType, (int)slotNode.UImm);
                if (method == null) break;
                TypeSig[] classArgs = receiverType is GenericInstSig g && ReferenceEquals(g.Definition, method.DeclaringType) ? g.Arguments : [];
                BuildCall(call, method, classArgs, [], isVirtual: true, tail, null, skipFirst: false, receiverOverride: objectNode, shift: 1, bufferFirst: buffer);
                return;
            }
            case HelperKind.InterfaceInvoker:
            {
                // Invoke(slot, interfaceClass, obj, args...) - or Invoke(&result, slot, interfaceClass, obj, args...)
                bool buffer = helper.BufferFirst;
                Node? slotNode = buffer ? IntAt(call, 1) : a0, classNode = buffer ? IntAt(call, 2) : a1, objectNode = buffer ? IntAt(call, 3) : a2;
                if (slotNode == null || !slotNode.IsConst || classNode == null || objectNode == null) break;
                TypeSig? iface = EvalKlass(classNode);
                int slot = (int)slotNode.UImm;
                MethodDef? method = iface?.Definition?.Methods.FirstOrDefault(m => m.HasSlot && m.Slot == slot);
                if (method == null) break;
                TypeSig[] classArgs = iface is GenericInstSig g ? g.Arguments : [];
                BuildCall(call, method, classArgs, [], isVirtual: true, tail, null, skipFirst: false, receiverOverride: objectNode, shift: 2, bufferFirst: buffer);
                return;
            }
            case HelperKind.RgctxData:
            {
                // il2cpp_rgctx_data(rgctx, index): the entry, as a read of the table gives it.
                if (NoRgctxCalls || tail || a0 == null || a1 == null || !a1.IsConst || Eval(a0) is not SRgctx context) break;
                Sem entry = RgctxValue(context, (int)a1.UImm);
                if (entry is SJunk) break;
                if (Projections(call).TryGetValue(CallResult.IntReturn, out Node? held)) _sem[held] = entry;
                return;
            }
            case HelperKind.GenericVirtualInvoker:
            case HelperKind.GenericInterfaceInvoker:
            {
                // Invoke(method, obj, args...): which method, with which type arguments, is the value handed over.
                if (NoGenericInvokerShapes || a0 == null || a1 == null || Eval(a0) is not SMethod { Method: var generic } named) break;
                TypeSig[] ofClass = named.Inst?.ClassArguments ?? [];
                TypeSig[] ofMethod = named.Inst?.MethodArguments ?? [];
                if (generic.IsStatic || generic.GenericParameters.Length == 0 || generic.GenericParameters.Length != ofMethod.Length) break;
                BuildCall(call, generic, ofClass, ofMethod, isVirtual: true, tail, null, skipFirst: false, receiverOverride: a1, shift: 1);
                return;
            }
        }

        Problem($"runtime helper {helper.Kind} not translated");
        var args = new List<HExpr>();
        for (int i = 0; i < Math.Min(4, Math.Max(helper.IntArgs, 0)); i++)
            if (IntAt(call, i) is { } a && Eval(a) is not SJunk)
                args.Add(Value(a));
        var opaque = new HOpaque(helper.Kind.ToString(), args.ToArray()) { Type = _long };
        if (helper.NoReturn)
        {
            Emit(new HEval(opaque), call.Addr);
            Emit(new HThrow(new HOpaque("noreturn")), call.Addr);
            return;
        }
        FinishCall(call, opaque, helper.ReturnsValue ? ReturnKind.Integer : ReturnKind.Void, _long, tail);
    }
}
