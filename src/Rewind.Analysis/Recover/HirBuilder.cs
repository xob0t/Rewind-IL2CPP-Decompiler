// Modified by xob0t (2026): virtual calls through merged class pointers, gaps always marked, small structs as numbers, floating-point negation, bits read as float/double, merged struct returns, long stack slots that held a reference and a number, struct addresses typed as their target, merged statics pointers. See FORK.md.
using Rewind.Analysis.Abi;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
using Rewind.Analysis.Runtime;
using Rewind.Analysis.X64;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>
/// Translates a normalized machine-level function into typed managed operations. Each machine value is given a
/// meaning (<see cref="Sem"/>) from where it came from - a parameter, a field, a metadata slot, a call result -
/// and memory accesses and calls are resolved against the type model: an offset from an object becomes a field,
/// an indexed address becomes an array element, an address becomes the method it starts.
/// </summary>
public sealed partial class HirBuilder
{
    private readonly ProgramAnalysis _p;
    private readonly Il2CppModel _m;
    private readonly LiftedMethod _l;
    private readonly Function _fn;
    private readonly MethodDef _method;
    private readonly MethodAbi _abi;
    private readonly HMethod _h = new();
    private readonly int _ptr;
    private readonly int _header;

    private readonly Dictionary<Node, Sem> _sem = [];
    private readonly Dictionary<Node, List<Node>> _uses;
    private readonly Dictionary<Block, HBlock> _hblock = [];
    private readonly Dictionary<Node, HVar> _phiVar = [];
    private readonly HashSet<Node> _materialize = [];
    private readonly Dictionary<Node, int> _position = [];
    private readonly Dictionary<Node, List<TypeSig>> _castTypes = [];
    /// <summary>Where each object's class checks are (CastFact's At and From): a check holds only past its place.</summary>
    private readonly Dictionary<Node, List<(Block At, Node? From)>> _castPlaces = [];
    /// <summary>CastHoldsAtStart's answers, per object and block.</summary>
    private readonly Dictionary<(Node, Block), bool> _castAtStart = [];
    /// <summary>The node ProcessBlock is building: where in _block a use is.</summary>
    private Node? _node;
    private readonly Dictionary<(int Offset, string TypeKey), HVar> _frameVars = [];
    private readonly Dictionary<int, TypeSig> _frameTypes = [];
    /// <summary>Untyped stack slots accessed at overlapping ranges of different widths: start -> width (up to 8 bytes).</summary>
    private readonly Dictionary<int, int> _rawCells = [];

    /// <summary>
    /// The compiler moves small values through stack slots at whatever width suits it: a Vector3 as 8 bytes and
    /// then 4, a bool written as a byte and later reloaded with the register around it. Overlapping accesses of
    /// one untyped slot are one variable, read and written in parts; otherwise a write through one width would
    /// be invisible to a read through another.
    /// </summary>
    /// <summary>The stack offset an address denotes when it is the entry stack pointer plus constants; null otherwise.</summary>
    private int? StackOffsetOf(Node n, int depth)
    {
        if (depth > 8) return null;
        if (_fn.Params.TryGetValue(_fn.Regs.StackPointer, out Node? sp0) && ReferenceEquals(n, sp0)) return 0;
        if (n.Op == Op.Add && n.In.Length == 2)
        {
            if (n.In[1].IsConst && StackOffsetOf(n.In[0], depth + 1) is int a) return a + (int)IrBuilder.SImm(n.In[1]);
            if (n.In[0].IsConst && StackOffsetOf(n.In[1], depth + 1) is int b) return b + (int)IrBuilder.SImm(n.In[0]);
        }
        if (n.Op == Op.Sub && n.In.Length == 2 && n.In[1].IsConst && StackOffsetOf(n.In[0], depth + 1) is int c) return c - (int)IrBuilder.SImm(n.In[1]);
        return null;
    }

    private static readonly bool NoSplitCells = Environment.GetEnvironmentVariable("REWIND_NO_SPLIT_CELLS") != null;

    private void PlanRawCells()
    {
        var accesses = new List<(int Start, int End)>();
        foreach (Block b in _fn.Blocks)
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op is not (Op.Load or Op.Store)) continue;
                // Only from the shape of the address: evaluating values here, before translation, would fix their
                // meaning too early (a call's result is not known until the call is translated).
                if (StackOffsetOf(n.In[0], 0) is not int offset) continue;
                int size = n.Op == Op.Load ? n.Type.Bytes() : n.In[1].Type.Bytes();
                if (size is <= 0 or > 8) continue;
                accesses.Add((offset, offset + size));
            }
        if (accesses.Count < 2) return;
        bool Typed(int start, int end)
        {
            foreach (var (at, type) in _frameTypes)
            {
                int extent = Math.Max(1, _p.Layouts.SizeOf(type).Size);
                if (start < at + extent && at < end) return true;
            }
            return false;
        }
        accesses.Sort();
        int cellStart = accesses[0].Start, cellEnd = accesses[0].End;
        bool mixed = false;
        var cluster = new List<(int Start, int End)> { accesses[0] };
        void Close()
        {
            int width = cellEnd - cellStart;
            if (!mixed || Typed(cellStart, cellEnd)) return;
            if (width <= 8)
            {
                _rawCells[cellStart] = width <= 1 ? 1 : width <= 2 ? 2 : width <= 4 ? 4 : 8;
                return;
            }
            // Wider than any number, reached eight bytes at a time four bytes apart (a struct moved in
            // pieces): four-byte numbers side by side, every access one of them, two of them, or part of one.
            if (NoSplitCells || width > 64) return;
            foreach (var (start, end) in cluster)
            {
                int size = end - start, from = start - cellStart;
                bool fits = size >= 4 ? from % 4 == 0 && size % 4 == 0 : from / 4 == (end - 1 - cellStart) / 4;
                if (!fits) return;
            }
            for (int at = cellStart; at < cellEnd; at += 4) _frameTypes[at] = _int;
        }
        foreach (var (start, end) in accesses.Skip(1))
        {
            if (start < cellEnd)
            {
                if (start != cellStart || end != cellEnd) mixed = true;
                cellEnd = Math.Max(cellEnd, end);
                cluster.Add((start, end));
                continue;
            }
            Close();
            cellStart = start;
            cellEnd = end;
            mixed = false;
            cluster = [(start, end)];
        }
        Close();
    }
    /// <summary>Frame offsets where a value type is given an object header in place, with that value type.</summary>
    private readonly Dictionary<int, TypeSig> _fakeBoxes = [];
    private HVar? _returnBuffer;
    private Block _block = null!;
    private HBlock _cur = null!;

    private readonly TypeSig _int, _long, _float, _double, _bool, _object, _string, _nint, _byte, _sbyte, _short, _ushort, _uint, _ulong, _char, _void;

    private readonly IReadOnlyDictionary<Node, TypeSig>? _knownPhiTypes;

    /// <summary>
    /// The types merged values ended up with. A merged value's type is only known once a typed value has
    /// flowed into it, which can be after its first use (the top of a loop); building a second time with
    /// these types known from the start resolves such uses.
    /// </summary>
    public Dictionary<Node, TypeSig> PhiTypes { get; } = [];
    public bool PhiTypesRefined { get; private set; }

    /// <summary>Temporaries that hold the value a field had when they were assigned, with that field.</summary>
    private readonly Dictionary<HVar, HField> _fieldTemps = [];
    private readonly Dictionary<int, HashSet<TypeSig>> _frameVotes = [];

    /// <summary>
    /// Types of stack objects that the finished calls showed to differ from the first guess. The guess is
    /// made before anything is translated, from whichever method a call target might be; the call itself is
    /// resolved later, with the receiver's type in hand ("out" of Dictionary&lt;string, Quest&gt;.TryGetValue is a
    /// Quest, not the "object" of the shared code). Building again with these types gets the accesses right.
    /// </summary>
    public Dictionary<int, TypeSig> RefinedFrameTypes { get; } = [];
    public bool FrameTypesRefined { get; private set; }

    /// <summary>
    /// Merged code pointers of virtual methods, each way in picking another method, that are then called: per
    /// merged value, the method of each way in. The next build makes the merged value the number of the method
    /// and calls the one it names (see EmitDispatch).
    /// </summary>
    public Dictionary<Node, MethodDef[]> DispatchPhis { get; } = [];
    public bool DispatchRefined { get; private set; }
    private readonly Dictionary<Node, (HVar Which, MethodDef[] Ways, MethodDef[] Distinct)> _dispatch = [];
    private static readonly bool NoMergedDispatch = Environment.GetEnvironmentVariable("REWIND_NO_MERGED_DISPATCH") != null;

    /// <summary>
    /// Every byte of stack memory must belong to one variable. Two variables that cover the same bytes mean
    /// the method was translated with two views of one piece of memory - a write through one would be
    /// invisible through the other - so the result cannot be trusted and is marked.
    /// </summary>
    /// <summary>Stack offsets whose memory looked like two different things (for StackSplitting).</summary>
    public HashSet<int> FrameConflicts { get; } = [];

    /// <summary>Stack slots of a bool that are given or handed on as another number (a subset of FrameConflicts).</summary>
    public HashSet<int> BoolSlotConflicts { get; } = [];

    /// <summary>Slots of a number that held another kind of value for a while: a bool's, or a struct in a number's (a subset of FrameConflicts).</summary>
    public HashSet<int> ScalarSlotConflicts { get; } = [];

    /// <summary>
    /// Whether a merged value that is the address of one stack object or another becomes a reference variable
    /// (see DeclarePhis). Turned off for a build again where such a variable could not be written in C#.
    /// </summary>
    public bool MergedAddresses { get; init; } = true;

    /// <summary>The reference variables made that way.</summary>
    public HashSet<HVar> MergedAddressVariables { get; } = [];

    /// <summary>Merged objects used as a class their values do not share (for ClassMerges.SplitAt).</summary>
    public HashSet<Node> MergedObjects { get; } = [];

    /// <summary>
    /// The method each call was found to mean, with its argument layout (and by how many positions the call's
    /// arguments are shifted against it). A call's target alone may name many methods that share one body; this
    /// is the one the receiver and arguments picked.
    /// </summary>
    public Dictionary<Node, (MethodDef Method, MethodAbi Abi, int Shift)> ChosenCalls { get; } = [];

    /// <summary>
    /// A struct of one type assigned to a variable of another is never what the program did: the memory is
    /// being read as the wrong thing (a stack slot the compiler reused for another struct, typically).
    /// </summary>
    private void CheckStructAssignments()
    {
        var offsetOf = new Dictionary<HVar, int>();
        foreach (var ((offset, _), variable) in _frameVars) offsetOf.TryAdd(variable, offset);
        static bool IsStruct(TypeSig? t) => t is { IsValueType: true } && t is not PrimitiveSig && t.Definition is { IsEnum: false };
        foreach (HBlock block in _h.Blocks)
            foreach (HStmt s in block.Statements)
            {
                if (s is not HAssign { Target: var target, Value: var value } || !IsStruct(target.Type) || !IsStruct(value.Type) ||
                    target.Type!.Key == value.Type!.Key) continue;
                Problem($"a {value.Type.ShortName} stored where a {target.Type.ShortName} is");
                if (target is HLocal { Variable: var v } && offsetOf.TryGetValue(v, out int at)) FrameConflicts.Add(at);
            }
        // The same for a call handed one struct where it takes another (a Vector3 where a Quaternion is taken).
        if (!NoArgumentConflicts)
            foreach (HBlock block in _h.Blocks)
                foreach (HStmt s in block.Statements)
                    FinallyFolding.Visit(s, e =>
                    {
                        if (e is not HCall call || call.Method.Parameters.Length != call.Arguments.Length) return;
                        TypeSig[] classArgs = call.DeclaringType is GenericInstSig g ? g.Arguments : [];
                        for (int i = 0; i < call.Arguments.Length; i++)
                        {
                            TypeSig declared = call.Method.Parameters[i].Type;
                            TypeSig wanted = _m.Sigs.Substitute(declared is ByRefSig r ? r.ElementType : declared, classArgs, call.MethodArguments);
                            HExpr given = call.Arguments[i];
                            TypeSig? passed = given.Type is ByRefSig byRef ? byRef.ElementType : given.Type;
                            // (An address is typed as what the call takes; what it points to is the local's own type.)
                            if (!NoAddressTargetTypes && given is HAddressOf { Target: HLocal { Type: { } targetType } }) passed = targetType;
                            if (Open(wanted) || !IsStruct(wanted) || !IsStruct(passed) || wanted.Key == passed!.Key) continue;
                            // (One C# converts on its own, with the same bytes: a Span where a ReadOnlySpan is taken.)
                            if (SameBytesConversion(passed, wanted)) continue;
                            Problem($"a {passed.ShortName} handed where a {wanted.ShortName} is taken");
                            HExpr place = given is HAddressOf { Target: var t } ? t : given;
                            if (place is HLocal { Variable: var v } && offsetOf.TryGetValue(v, out int at))
                            {
                                FrameConflicts.Add(at);
                                // (What a call captures of the slot without taking it is no read of either struct.)
                                if (!NoAddressTargetTypes) ScalarSlotConflicts.Add(at);
                            }
                        }
                    });
        if (NoScalarConflicts) return;
        // The same with a reference kept where a small number is, or a number where a reference is: the
        // compiler used one slot for two variables, one after the other. (Nothing is reported: where the two
        // lifetimes can be told apart they are, and the next build has a variable for each.) A double counts too:
        // unlike a long, it is never what an untyped slot is taken for.
        static bool IsSmallNumber(TypeSig? t) => t switch
        {
            PrimitiveSig p => p.Element is Il2CppTypeEnum.Boolean or Il2CppTypeEnum.Char or Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or Il2CppTypeEnum.I2 or
                Il2CppTypeEnum.U2 or Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8,
            { Definition: { IsEnum: true } } => true,
            _ => false,
        };
        foreach (HBlock block in _h.Blocks)
            foreach (HStmt s in block.Statements)
            {
                if (s is not HAssign { Target: HLocal { Variable: var slot } place, Value: var held } || !offsetOf.TryGetValue(slot, out int where)) continue;
                if (place.Type == null || held.Type == null) continue;
                // (A byte is how the native code keeps a bool: one taken out of a wider value, or merged with a
                // constant 1, is typed byte and is the bool.)
                if (!NoBoolConflicts && IsBoolType(place.Type) && !IsTruthValue(held) && IsNumber(held.Type) &&
                    held.Type is not PrimitiveSig { Element: Il2CppTypeEnum.U1 or Il2CppTypeEnum.I1 })
                {
                    FrameConflicts.Add(where);
                    BoolSlotConflicts.Add(where);
                    ScalarSlotConflicts.Add(where);
                    continue;
                }
                if (held is HConst) continue;
                if ((IsSmallNumber(place.Type) && IsReference(held.Type)) || (IsReference(place.Type) && IsSmallNumber(held.Type))) FrameConflicts.Add(where);
            }
        // A long slot is what an untyped slot is taken for, so a long alone says nothing; but one given both a
        // reference and a number computed as a number (bits merged into it: the bools of one call's stack
        // arguments, then an object for the next call) held two variables as well.
        if (!NoLongSlotConflicts)
        {
            var references = new HashSet<int>();
            var numbers = new HashSet<int>();
            foreach (HBlock block in _h.Blocks)
                foreach (HStmt s in block.Statements)
                {
                    if (s is not HAssign { Target: HLocal { Variable: var slot }, Value: var held } || !offsetOf.TryGetValue(slot, out int where) ||
                        held.Type == null || held is HConst) continue;
                    if (IsReference(held.Type)) references.Add(where);
                    else if (IsNumber(held.Type) && held is not HLocal) numbers.Add(where);
                }
            // (Handed where a reference is taken counts as holding one: null is the constant 0 of the slot.)
            foreach (HBlock block in _h.Blocks)
                foreach (HStmt s in block.Statements)
                    FinallyFolding.Visit(s, e =>
                    {
                        if (e is not HCall call || call.Method.Parameters.Length != call.Arguments.Length) return;
                        for (int i = 0; i < call.Arguments.Length; i++)
                            if (call.Arguments[i] is HLocal { Variable: var v } && offsetOf.TryGetValue(v, out int at) &&
                                call.Method.Parameters[i].Type is { IsValueType: false } wanted && wanted is not ByRefSig && IsReference(wanted))
                                references.Add(at);
                    });
            foreach (int where in references)
                if (numbers.Contains(where))
                {
                    FrameConflicts.Add(where);
                    ScalarSlotConflicts.Add(where);
                }
        }
        // A struct kept in a number's slot (a struct that is one number, where an int was before): stored there,
        // or boxed from there as the struct. C# converts neither way; the slot held two variables.
        if (!NoStructSlots)
            foreach (HBlock block in _h.Blocks)
                foreach (HStmt s in block.Statements)
                {
                    if (s is HAssign { Target: HLocal { Variable: var v } place, Value: var held } && offsetOf.TryGetValue(v, out int at) &&
                        IsNumber(place.Type) && IsStruct(held.Type))
                    {
                        FrameConflicts.Add(at);
                        ScalarSlotConflicts.Add(at);
                    }
                    FinallyFolding.Visit(s, e =>
                    {
                        if (e is HTypeExpr { Op: HTypeOp.Box, Target: var boxed, Operand: HLocal { Variable: var bv } from } && IsStruct(boxed) &&
                            IsNumber(from.Type) && offsetOf.TryGetValue(bv, out int boxedAt))
                        {
                            FrameConflicts.Add(boxedAt);
                            ScalarSlotConflicts.Add(boxedAt);
                        }
                    });
                }
        if (NoBoolConflicts) return;
        // A bool slot handed where another number is taken (an enum, a char): the slot held a bool for one
        // variable and that number for another. Read through the bool, the number would come out as 0 or 1.
        foreach (HBlock block in _h.Blocks)
            foreach (HStmt s in block.Statements)
                FinallyFolding.Visit(s, e =>
                {
                    if (e is not HCall call || call.Method.Parameters.Length != call.Arguments.Length) return;
                    for (int i = 0; i < call.Arguments.Length; i++)
                        if (call.Arguments[i] is HLocal { Variable: var v } local && IsBoolType(local.Type) && offsetOf.TryGetValue(v, out int at) &&
                            call.Method.Parameters[i].Type is var wanted && !IsBoolType(wanted) && IsNumber(wanted))
                        {
                            FrameConflicts.Add(at);
                            BoolSlotConflicts.Add(at);
                            ScalarSlotConflicts.Add(at);
                        }
                });
    }

    private static bool IsBoolType(TypeSig? t) => t is PrimitiveSig { Element: Il2CppTypeEnum.Boolean };

    /// <summary>A number of any width, or an enum.</summary>
    private static bool IsNumber(TypeSig? t) => t switch
    {
        PrimitiveSig p => p.Element is Il2CppTypeEnum.Char or Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 or Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 or
            Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.I or Il2CppTypeEnum.U or
            Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8,
        { Definition: { IsEnum: true } } => true,
        _ => false,
    };

    /// <summary>What a bool can hold: a bool, or the number 0 or 1.</summary>
    private static bool IsTruthValue(HExpr e) =>
        IsBoolType(e.Type) || e is HConst { Value: false or true or 0 or 1 or 0L or 1L or (byte)0 or (byte)1 };

    private static readonly bool NoScalarConflicts = Environment.GetEnvironmentVariable("REWIND_NO_SCALAR_CONFLICTS") != null;
    private static readonly bool NoAddressTargetTypes = Environment.GetEnvironmentVariable("REWIND_NO_ADDRESS_TARGET_TYPES") != null;
    private static readonly bool NoLongSlotConflicts = Environment.GetEnvironmentVariable("REWIND_NO_LONG_SLOT_CONFLICTS") != null;
    private const string LostRegisterUsed = "a value kept in a callee-saved register is used after a caught exception";
    private static readonly bool NoLazyLostRegisters = Environment.GetEnvironmentVariable("REWIND_NO_LAZY_LOST_REGISTERS") != null;
    private static readonly bool NoStructSlots = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_SLOTS") != null;
    private static readonly bool NoBoolConflicts = Environment.GetEnvironmentVariable("REWIND_NO_BOOL_CONFLICTS") != null;

    private void CheckFrameVariables()
    {
        foreach (var (offset, votes) in _frameVotes)
            if (votes.Count(v => !ReferenceEquals(v, _long)) > 1) FrameConflicts.Add(offset);
        if (FrameTypesRefined || _frameVars.Count < 2) return; // another build with better types follows
        var spans = new List<(int Start, int End, HVar Variable)>();
        foreach (var ((offset, _), variable) in _frameVars)
        {
            int size = Math.Max(1, _p.Layouts.SizeOf(variable.Type).Size);
            spans.Add((offset, offset + size, variable));
        }
        spans.Sort((a, b) => a.Start.CompareTo(b.Start));
        bool reported = false;
        for (int i = 1; i < spans.Count; i++)
            if (spans[i].Start < spans[i - 1].End)
            {
                FrameConflicts.Add(spans[i - 1].Start);
                FrameConflicts.Add(spans[i].Start);
                if (reported) continue;
                reported = true;
                Problem($"stack memory seen as two different objects ({spans[i - 1].Variable.Type.ShortName} and {spans[i].Variable.Type.ShortName})" +
                        (Environment.GetEnvironmentVariable("REWIND_FRAME_DEBUG") != null ? $" [{spans[i - 1].Variable.Name} @{spans[i - 1].Start} and {spans[i].Variable.Name} @{spans[i].Start}]" : ""));
            }
    }

    private void RefineFrameTypes()
    {
        foreach (var (offset, votes) in _frameVotes)
        {
            if (votes.Count != 1 || _fakeBoxes.ContainsKey(offset - _header)) continue;
            TypeSig voted = votes.First();
            if (!Nameable(voted)) continue;
            if (_frameTypes.TryGetValue(offset, out TypeSig? current) && ReferenceEquals(current, voted)) continue;
            if (current == null && ReferenceEquals(voted, _long)) continue; // what an untyped slot already is
            RefinedFrameTypes[offset] = voted;
            FrameTypesRefined = true;
        }
        // Stack memory copied out as one struct type, and only one: that struct, in the next build.
        foreach (var (start, votes) in _copyVotes)
        {
            if (votes.Count != 1 || _frameTypes.ContainsKey(start) || RefinedFrameTypes.ContainsKey(start)) continue;
            TypeSig copied = votes.First();
            int end = start + _p.Layouts.SizeOf(copied).Size;
            // (Not where a struct already known covers some of those bytes from elsewhere.)
            if (_frameTypes.Any(kv => kv.Key < end && start < kv.Key + Math.Max(1, _p.Layouts.SizeOf(kv.Value).Size) && IsStructType(kv.Value))) continue;
            RefinedFrameTypes[start] = copied;
            FrameTypesRefined = true;
        }
        if (DropInnerTypes(RefinedFrameTypes) && RefinedFrameTypes.Count == 0) FrameTypesRefined = false;
    }

    /// <summary>
    /// A type learned for bytes that lie inside a struct known to start earlier is one of the struct's fields,
    /// seen before the struct was: the struct covers it. True when anything was dropped.
    /// </summary>
    private bool DropInnerTypes(Dictionary<int, TypeSig> types)
    {
        var structs = types.Where(kv => kv.Value is { IsValueType: true } && kv.Value is not PrimitiveSig && kv.Value.Definition is { IsEnum: false })
                           .Select(kv => (Start: kv.Key, End: kv.Key + _p.Layouts.SizeOf(kv.Value).Size)).ToList();
        var inner = types.Keys.Where(o => structs.Any(s => s.Start < o && o < s.End)).ToList();
        foreach (int o in inner) types.Remove(o);
        return inner.Count != 0;
    }

    public HirBuilder(ProgramAnalysis program, LiftedMethod lifted, IReadOnlyDictionary<Node, TypeSig>? knownPhiTypes = null,
        IReadOnlyDictionary<int, TypeSig>? knownFrameTypes = null, IReadOnlyDictionary<Node, MethodDef[]>? knownDispatch = null)
    {
        if (knownDispatch != null)
            foreach (var (phi, ways) in knownDispatch)
                DispatchPhis[phi] = ways;
        if (knownFrameTypes != null)
            foreach (var (offset, type) in knownFrameTypes)
            {
                _frameTypes[offset] = type;
                RefinedFrameTypes[offset] = type;
            }
        _knownPhiTypes = knownPhiTypes;
        _p = program;
        _m = program.Model;
        _l = lifted;
        _fn = lifted.Function;
        _method = lifted.Method;
        _abi = lifted.Abi;
        _ptr = _m.Image.PointerSize;
        _header = 2 * _ptr;
        _uses = DeadCode.Uses(_fn);
        _h.Method = _method;

        TypeSig Prim(Il2CppTypeEnum e) => _m.Sigs.Primitive(e);
        _int = Prim(Il2CppTypeEnum.I4);
        _uint = Prim(Il2CppTypeEnum.U4);
        _long = Prim(Il2CppTypeEnum.I8);
        _ulong = Prim(Il2CppTypeEnum.U8);
        _float = Prim(Il2CppTypeEnum.R4);
        _double = Prim(Il2CppTypeEnum.R8);
        _bool = Prim(Il2CppTypeEnum.Boolean);
        _object = Prim(Il2CppTypeEnum.Object);
        _string = Prim(Il2CppTypeEnum.String);
        _nint = Prim(Il2CppTypeEnum.I);
        _byte = Prim(Il2CppTypeEnum.U1);
        _sbyte = Prim(Il2CppTypeEnum.I1);
        _short = Prim(Il2CppTypeEnum.I2);
        _ushort = Prim(Il2CppTypeEnum.U2);
        _char = Prim(Il2CppTypeEnum.Char);
        _void = Prim(Il2CppTypeEnum.Void);
    }

    private Cfg _cfg = null!;
    private readonly Dictionary<Block, List<(Node Object, TypeSig Type)>> _typeFacts = [];

    /// <summary>
    /// The type an object is known to have here because a type test on every way to this point succeeded.
    /// (After "if (o is Goblin)" the compiled code keeps using o itself, as a Goblin.)
    /// </summary>
    /// <summary>
    /// Whether a class check of obj that a guard removed holds at the node being built: every way from the entry to it
    /// passes a check. A method that checks this's class on one path only (a field of a subclass read when a level
    /// number says so) uses this unchecked everywhere else, and a cast there would throw; a read in the check's own
    /// block before the check would throw before what the native code did first. A check the CFG no longer reaches
    /// (a constant-false arm) proves nothing. Outside the building of blocks (the planning passes): true.
    /// </summary>
    private bool CastHoldsHere(Node obj)
    {
        if (_cfg == null || _block == null) return true;
        if (!_castPlaces.TryGetValue(obj, out List<(Block At, Node? From)>? places) || !_cfg.IsReachable(_block)) return false;
        foreach (var (at, from) in places)
        {
            if (!ReferenceEquals(at, _block) || _node == null || !_position.TryGetValue(_node, out int here)) continue;
            // From null, or a node a later pass took out of the block: the check is at the block's end at the latest.
            if (from != null && !ReferenceEquals(from.Block, _block)) continue;
            int checkAt = from != null && _position.TryGetValue(from, out int fromAt) ? fromAt : _block.Nodes.Count;
            // Past the check; or before it with nothing between that the cast's throw would skip: the compiler loads
            // fields before the class test it doesn't depend on, and the source's cast came first.
            if (checkAt <= here || !EffectBetween(_block, here, checkAt)) return true;
        }
        return CastHoldsAtStart(obj, _block, places);
    }

    /// <summary>Whether a store or a call (an effect the native code performed) is between two nodes of block.</summary>
    private static bool EffectBetween(Block block, int after, int before)
    {
        for (int i = after + 1; i < before && i < block.Nodes.Count; i++)
            if (!block.Nodes[i].Dead && block.Nodes[i].Op is Op.Store or Op.Call)
                return true;
        return false;
    }

    /// <summary>Whether every way from the entry to block's first node passes the end of a block that checks obj.</summary>
    private bool CastHoldsAtStart(Node obj, Block block, List<(Block At, Node? From)> places)
    {
        if (_castAtStart.TryGetValue((obj, block), out bool known)) return known;
        var checks = new HashSet<Block>();
        foreach (var (at, _) in places)
            if (_cfg.IsReachable(at)) checks.Add(at);
        var seen = new HashSet<Block> { _fn.Entry };
        var pending = new Stack<Block>();
        pending.Push(_fn.Entry);
        bool reached = false;
        while (pending.Count > 0 && !reached)
        {
            Block b = pending.Pop();
            if (ReferenceEquals(b, block)) reached = true;
            else if (!checks.Contains(b))
                foreach (Block s in b.Succs)
                    if (seen.Add(s)) pending.Push(s);
        }
        return _castAtStart[(obj, block)] = !reached;
    }

    /// <summary>A class check found while building (an unboxing's): it holds from node on.</summary>
    private void AddCastPlace(Node obj, Block at, Node? from)
    {
        if (!_castPlaces.TryGetValue(obj, out List<(Block At, Node? From)>? places)) _castPlaces[obj] = places = [];
        places.Add((at, from));
        foreach (var key in _castAtStart.Keys.Where(k => ReferenceEquals(k.Item1, obj)).ToList()) _castAtStart.Remove(key);
    }

    private TypeSig? TestedType(Node obj)
    {
        int guard = 0;
        for (Block? b = _block; b != null && guard++ < 4096; b = _cfg.ImmediateDominator(b))
            if (_typeFacts.TryGetValue(b, out List<(Node Object, TypeSig Type)>? facts))
                foreach (var (o, t) in facts)
                    if (ReferenceEquals(o, obj))
                        return t;
        return null;
    }

    /// <summary>When a branch condition is a type test: the object, the type, and which way means "is an instance".</summary>
    private (Node Object, TypeSig Type, bool WhenTrue)? InstanceTestOf(Node condition)
    {
        if (condition.Op is not (Op.CmpEq or Op.CmpNe)) return null;
        bool equal = condition.Op == Op.CmpEq;
        Node x = condition.In[0], y = condition.In[1];
        // (obj as T) compared with null, where "as" is still in its machine form.
        if (y.IsConstValue(0) && x.Op == Op.Select && TypeTestSelect(x) is SVal { Expr: HTypeExpr { Op: HTypeOp.IsInst } cast })
        {
            Node selected = x.In[0].Op == Op.CmpEq ? x.In[1] : x.In[2];
            return (selected, cast.Target, !equal);
        }
        Sem a = Eval(x), b = Eval(y);
        if (a is SObjKlass oa && b is SKlass kb) return (oa.Object, kb.Type, equal);
        if (b is SObjKlass ob && a is SKlass ka) return (ob.Object, ka.Type, equal);
        if (a is SHierarchyEntry ea && b is SKlass kc && ReferenceEquals(ea.Type, kc.Type)) return (ea.Object, ea.Type, equal);
        if (b is SHierarchyEntry eb && a is SKlass kd && ReferenceEquals(eb.Type, kd.Type)) return (eb.Object, eb.Type, equal);
        return null;
    }

    private static readonly string? ProblemTrace = Environment.GetEnvironmentVariable("REWIND_PROBLEM_TRACE");

    /// <summary>
    /// Above zero while values are only looked at to decide something (which of several methods a call means):
    /// a register captured at a call may hold anything when the callee takes fewer arguments, and what cannot
    /// be said about such a value is no defect of the method - unless the value is then used. Problems met
    /// while looking are held with the value and reported when it is evaluated for use.
    /// </summary>
    private int _peeking;
    /// <summary>In a constructor: the call of the base class's (or a sibling) constructor has been translated.</summary>
    private bool _baseConstructorCalled;
    private Node? _computing;
    /// <summary>The value being looked at when no computation is under way (its expression is being formed).</summary>
    private Node? _peekSubject;
    private readonly Dictionary<Node, List<string>> _heldProblems = [];
    /// <summary>Values computed (while looking) as part of computing the key: their held problems go with it.</summary>
    private readonly Dictionary<Node, List<Node>> _heldUnder = [];

    /// <summary>
    /// Merged values something reads. A register that holds leftovers on every path is still "merged" where the
    /// paths meet, and a call lifted before its signature was known still "takes" it; when nothing translated
    /// ever reads the merged value, the copies into it are no part of the program (see SettlePhis).
    /// </summary>
    private readonly HashSet<Node> _phiRead = [];
    /// <summary>Merged values read while computing the key during a look (they count once the key is used).</summary>
    private readonly Dictionary<Node, List<Node>> _heldPhiReads = [];
    /// <summary>The values each merged value is given, one per way in.</summary>
    private readonly Dictionary<Node, List<Node>> _phiInputs = [];

    /// <summary>Merged values declared as reference variables: the address of one stack object or another (see DeclarePhis).</summary>
    private readonly HashSet<Node> _mergedAddresses = [];

    /// <summary>Values given a temporary while only looked at, with the assignment that gives it (see Materialize).</summary>
    private readonly Dictionary<Node, (HBlock Block, HAssign Assign)> _lookedAt = [];
    private static readonly bool NoHeldTemps = Environment.GetEnvironmentVariable("REWIND_NO_HELD_TEMPS") != null;
    private static readonly bool NoParamHalves = Environment.GetEnvironmentVariable("REWIND_NO_PARAM_HALVES") != null;
    private static readonly bool NoRefParamHalves = Environment.GetEnvironmentVariable("REWIND_NO_REF_PARAM_HALVES") != null;
    private static readonly bool NoStaticRefs = Environment.GetEnvironmentVariable("REWIND_NO_STATIC_REFS") != null;
    private static readonly bool NoMergedStructBits = Environment.GetEnvironmentVariable("REWIND_NO_MERGED_STRUCT_BITS") != null;
    private static readonly bool NoArgumentConflicts = Environment.GetEnvironmentVariable("REWIND_NO_ARGUMENT_CONFLICTS") != null;
    private static readonly bool NoWideSwitches = Environment.GetEnvironmentVariable("REWIND_NO_WIDE_SWITCHES") != null;

    /// <summary>
    /// Whether C# turns one struct into the other by itself (an implicit operator of either type) and the two are
    /// the same size: handing over the one where the other is taken is then what the source did.
    /// </summary>
    private bool SameBytesConversion(TypeSig from, TypeSig to)
    {
        if (_p.Layouts.SizeOf(from) is not { Known: true } a || _p.Layouts.SizeOf(to) is not { Known: true } b || a.Size != b.Size) return false;
        TypeSig[] Args(TypeSig t) => t is GenericInstSig g ? g.Arguments : [];
        foreach (TypeSig owner in new[] { from, to })
            if (owner.Definition is { } definition)
                foreach (MethodDef m in definition.Methods)
                {
                    if (m.Name != "op_Implicit" || !m.IsStatic || m.Parameters.Length != 1) continue;
                    TypeSig parameter = _m.Sigs.Substitute(m.Parameters[0].Type, Args(owner), []);
                    TypeSig result = _m.Sigs.Substitute(m.ReturnType, Args(owner), []);
                    if (parameter.Key == from.Key && result.Key == to.Key) return true;
                }
        return false;
    }

    /// <summary>A reference argument read in halves: the expression its halves are halves of, and back.</summary>
    private readonly Dictionary<SRef, HExpr> _refHalfMarks = [];
    private readonly Dictionary<HExpr, SRef> _halvedRefs = [];

    /// <summary>Is something still held for the value: it was looked at and has not been used since?</summary>
    private bool Held(Node n) => _heldProblems.ContainsKey(n) || _heldUnder.ContainsKey(n) || _heldPhiReads.ContainsKey(n);

    /// <summary>A computed value (no read of memory, no call) whose only users are merged values.</summary>
    private bool OnlyMerged(Node n)
    {
        if (NoHeldTemps || n.IsEffect || n.Op is Op.Load or Op.Proj or Op.Phi or Op.Call or Op.TailCall) return false;
        if (!_uses.TryGetValue(n, out List<Node>? users) || users.Count == 0) return false;
        // (Or the top half of two halves joined: read when the joined value is, and not when only its bottom
        // half is taken.)
        foreach (Node user in users)
            if (user.Op != Op.Phi && !(user.Op == Op.Concat && ReferenceEquals(user.In[0], n) && !ReferenceEquals(user.In[1], n))) return false;
        return true;
    }

    /// <summary>Arithmetic on variables and numbers only: nothing is read from memory and nothing can fail.</summary>
    private static bool Plain(HExpr e) => e switch
    {
        HConst or HLocal or HArg or HOpaque => true,
        HUnary u => Plain(u.Operand),
        HBinary b => IsPure(b) && Plain(b.Left) && Plain(b.Right),
        HCompare c => Plain(c.Left) && Plain(c.Right),
        HConv c => c.Kind < HConvKind.OvfI1 && Plain(c.Operand),
        _ => false,
    };

    private void Release(Node n)
    {
        if (_heldProblems.Remove(n, out List<string>? held))
            foreach (string text in held) Problem(text);
        if (_heldPhiReads.Remove(n, out List<Node>? reads))
            foreach (Node phi in reads) _phiRead.Add(phi);
        if (_heldUnder.Remove(n, out List<Node>? inner))
            foreach (Node part in inner) Release(part);
    }

    /// <summary>
    /// Decides which merged values are read at all - directly, or by being given to one that is - and removes
    /// the copies into the others. What those copies would have read is never looked at, so whatever could not
    /// be said about it does not count.
    /// </summary>
    private void SettlePhis()
    {
        var settled = new HashSet<Node>();
        void Settle()
        {
            var work = new Queue<Node>(_phiRead.Where(read => !settled.Contains(read)));
            while (work.Count > 0)
            {
                Node phi = work.Dequeue();
                if (!settled.Add(phi)) continue;
                // (What its copies could not say counts now: see PhiCopies.)
                Release(phi);
                if (!_phiInputs.TryGetValue(phi, out List<Node>? inputs)) continue;
                foreach (Node input in inputs)
                {
                    if (input.Op == Op.Phi) _phiRead.Add(input);
                    Release(input);
                }
                foreach (Node read in _phiRead)
                    if (!settled.Contains(read)) work.Enqueue(read);
            }
        }
        Settle();
        // Values given a temporary while only looked at (Materialize): one no merged value that is read takes
        // is no part of the program, and its assignment goes - unless computing it does something a program
        // would notice, where it stays and whatever could not be said about it counts after all.
        while (_lookedAt.Count > 0)
        {
            bool released = false;
            foreach (var (n, (_, assign)) in _lookedAt.ToList())
            {
                if (!Held(n)) _lookedAt.Remove(n);
                else if (!Plain(assign.Value))
                {
                    Release(n);
                    _lookedAt.Remove(n);
                    released = true;
                }
            }
            if (!released) break;
            Settle();
        }
        var unread = new HashSet<HVar>();
        void FindUnread()
        {
            unread.Clear();
            foreach (var (phi, variable) in _phiVar)
                if (!_phiRead.Contains(phi)) unread.Add(variable);
        }
        FindUnread();
        // (To be sure of it: a temporary that a statement which stays still names stays as well, and what was
        // held for it counts.)
        while (_lookedAt.Count > 0)
        {
            var temps = new Dictionary<HVar, Node>();
            foreach (var (n, (_, assign)) in _lookedAt)
                if (assign.Target is HLocal { Variable: var temp }) temps[temp] = n;
            var named = new HashSet<Node>();
            foreach (HBlock block in _h.Blocks)
                foreach (HStmt s in block.Statements)
                {
                    if (s is HAssign { Target: HLocal { Variable: var target } } &&
                        (unread.Contains(target) || (temps.TryGetValue(target, out Node? own) && ReferenceEquals(_lookedAt[own].Assign, s)))) continue;
                    FinallyFolding.Visit(s, e =>
                    {
                        if (e is HLocal l && temps.TryGetValue(l.Variable, out Node? of)) named.Add(of);
                    });
                }
            if (named.Count == 0) break;
            foreach (Node n in named)
            {
                Release(n);
                _lookedAt.Remove(n);
            }
            Settle();
            FindUnread();
        }
        foreach (var (_, (block, assign)) in _lookedAt) block.Statements.Remove(assign);
        _lookedAt.Clear();
        if (unread.Count == 0) return;
        foreach (HBlock block in _h.Blocks)
            block.Statements.RemoveAll(s => s is HAssign { Target: HLocal { Variable: var target } } && unread.Contains(target));
    }

    /// <summary>
    /// The marker standing in for what <paramref name="problem"/> (just reported) is about: when the marker is not
    /// in the finished method, neither is the problem (see HMethod.SiteProblems).
    /// </summary>
    private HOpaque Site(HOpaque marker, string problem)
    {
        marker.Problem = problem;
        _h.SiteProblems.Add(problem);
        return marker;
    }

    private void Problem(string text)
    {
        if (_peeking > 0 && (_computing ?? _peekSubject) is { } subject)
        {
            if (!_heldProblems.TryGetValue(subject, out List<string>? held)) _heldProblems[subject] = held = [];
            held.Add(text);
            return;
        }
        if (_h.Problems.Count < 64) _h.Problems.Add(text);
        // Debugging aid: where a problem of this kind is raised from.
        if (ProblemTrace != null && text.Contains(ProblemTrace, StringComparison.Ordinal))
        {
            Console.Error.WriteLine("[problem] " + text);
            foreach (string frame in Environment.StackTrace.Split((char)10).Skip(2).Take(18)) Console.Error.WriteLine("    " + frame.Trim());
        }
    }

    // ---- driver ------------------------------------------------------------------------------------------------

    public HMethod Build()
    {
        foreach (string p in _fn.Problems) Problem("lift: " + p);
        // Code that only runs when an exception is caught is not part of the function's ordinary flow; unless the
        // lifter rebuilt the try regions (or said why not), what was recovered is the no-exception path only.
        if (_p.ExceptionInfo(_fn.Address) is { TryBlocks.Count: > 0 } regions && _fn.TryRegions.Count == 0 &&
            !_fn.Problems.Any(p => p.StartsWith("exception handling", StringComparison.Ordinal)))
            Problem($"exception handling not reconstructed ({regions.TryBlocks.Count} try region(s))");
        if (_fn.Blocks.Count == 0)
        {
            Problem("no code");
            return _h;
        }

        foreach (Block b in _fn.Blocks)
        {
            var hb = new HBlock { Id = _h.Blocks.Count, Scope = b.Scope };
            _h.Blocks.Add(hb);
            _hblock[b] = hb;
            for (int i = 0; i < b.Nodes.Count; i++) _position[b.Nodes[i]] = i;
        }

        // A check in a block the CFG no longer reaches (or no longer has) was on a path that is gone: no fact at all,
        // neither a cast type nor a place.
        var reach = new Cfg(_fn);
        foreach (CastFact cast in _l.Normalization.Casts)
        {
            if (!reach.IsReachable(cast.At) || EvalKlass(cast.Klass) is not { } type) continue;
            if (!_castTypes.TryGetValue(cast.Object, out List<TypeSig>? list)) _castTypes[cast.Object] = list = [];
            if (!list.Contains(type)) list.Add(type);
            AddCastPlace(cast.Object, cast.At, cast.From);
        }

        BindParameters();
        FindFakeBoxes();
        InferFrameTypes();
        PlanRawCells();
        PlanStackBuffers();
        DecideMaterialization();

        var cfg = new Cfg(_fn);
        _cfg = cfg;
        PlanAddressSpills();
        PlanSameAddressPhis();
        PlanCaughtSlots();
        FindPieceCopies();
        FindPieceFills();
        foreach (Block b in cfg.ReversePostOrder) DeclarePhis(b);
        foreach (Block b in cfg.ReversePostOrder) ProcessBlock(b);
        SettlePhis();
        RefineFloatPhis();
        RefinePhiJoins();
        RefinePhiStructs();
        RefineFrameTypes();
        foreach (PendingCopy copy in _pendingCopies) Problem($"only part of a {copy.Type.ShortName} was copied");
        DeclareStackBuffers();
        CheckFrameVariables();
        CheckStructAssignments();
        foreach (var (offset, type) in _frameTypes) _h.FrameTypes[offset] = type;
        HirCleanup.Run(_h);
        if (HirCleanup.CheckTryRegions(_h) is { } broken) Problem("exception handling not reconstructed: " + broken);
        return _h;
    }

    /// <summary>The record of try region <paramref name="index"/>, made on first use.</summary>
    private HTryRegion RegionFor(int index)
    {
        if (_h.TryRegions.TryGetValue(index, out HTryRegion? region)) return region;
        TypeSig exceptionType = _m.FindType("System.Exception")?.Sig ?? _object;
        region = new HTryRegion { Index = index, Exception = _h.NewLocal(exceptionType, "e") };
        _h.TryRegions[index] = region;
        return region;
    }

    // ---- parameters --------------------------------------------------------------------------------------------

    private static readonly bool NoOwnMethod = Environment.GetEnvironmentVariable("REWIND_NO_OWN_METHOD") != null;

    private void BindParameters()
    {
        foreach (AbiParam p in _abi.Params)
        {
            Sem sem;
            switch (p.Role)
            {
                case ParamRole.This:
                {
                    TypeSig type = p.Type!;
                    var arg = new HArg(-1) { Type = type };
                    sem = type.Definition is { IsValueType: true } ? new SRef(arg, type) : new SVal(arg);
                    break;
                }
                case ParamRole.Argument:
                {
                    var arg = new HArg(p.ArgumentIndex) { Type = p.Type };
                    if (p.Pass == PassKind.Indirect) sem = new SRef(arg, p.Type!);
                    else if (p.Type is ByRefSig byRef) sem = new SRef(new HDeref(arg) { Type = byRef.ElementType }, byRef.ElementType);
                    else sem = new SVal(arg);
                    break;
                }
                case ParamRole.ReturnBuffer:
                    _returnBuffer = _h.NewLocal(p.Type!, "result");
                    _returnBuffer.AddressTaken = true;
                    sem = new SRef(new HLocal(_returnBuffer) { Type = p.Type }, p.Type!);
                    break;
                case ParamRole.MethodInfo when !NoOwnMethod:
                    // The record the runtime keeps of this method, handed to it like to every method. Code of
                    // a generic class reaches its class through it, and through that what the class knows of
                    // its type arguments (the methods it calls on them, the types it makes of them).
                    sem = new SMethod(_method, _l.ClassArguments.Length != 0 || _l.MethodArguments.Length != 0
                        ? new MethodInst { SpecIndex = -1, Method = _method, ClassArguments = _l.ClassArguments, MethodArguments = _l.MethodArguments }
                        : null);
                    break;
                default:
                    sem = SJunk.Instance;
                    break;
            }

            if (!_fn.Regs.IsStackPosition(p.Position) && p.Pass is PassKind.IntegerPair or PassKind.FloatAggregate)
            {
                if (sem is SVal { Expr: var structArg }) BindRegisterStruct(p, structArg);
            }
            else if (!_fn.Regs.IsStackPosition(p.Position))
            {
                if (p.Pass == PassKind.Float)
                {
                    int lane0 = _fn.Regs.FloatLane(_fn.Regs.FloatRegisterOf(p.Position), 0);
                    HExpr whole = ((SVal)sem).Expr;
                    if (p.IsDouble)
                    {
                        if (_fn.Params.TryGetValue(lane0, out Node? lo)) _sem[lo] = new SHalf(whole, false, null);
                        if (_fn.Params.TryGetValue(lane0 + 1, out Node? hi)) _sem[hi] = new SHalf(whole, true, null);
                    }
                    else if (_fn.Params.TryGetValue(lane0, out Node? lane)) _sem[lane] = sem;
                }
                else if (_fn.Regs.IntRegisterOf(p.Position) is int ir and >= 0 && _fn.Params.TryGetValue(_fn.Regs.IntArgs[ir], out Node? reg)) _sem[reg] = sem;
            }
            else
            {
                // Stack arguments sit above the return address and the 32-byte home area (Win64), at the entry stack pointer (AArch64).
                int offset = _fn.Regs.StackOffsetOf(p.Position);
                bool byValueStruct = sem is SVal { Expr: { } whole } && p.Pass != PassKind.Indirect && p.Type is { IsValueType: true } &&
                                     p.Type is not PrimitiveSig && p.Type.Definition is { IsEnum: false };
                // A struct passed by value on the stack (AArch64: one that found no registers left) fills as many
                // eight-byte slots as it needs.
                int structSize = byValueStruct ? _p.Layouts.SizeOf(p.Type!).Size : 0;
                int extent = Math.Max(8, (structSize + 7) & ~7);
                for (int part = 0; part < extent; part++)
                {
                    if (!_fn.StackParams.TryGetValue(offset + part, out Node? slot)) continue;
                    int size = slot.Type.Bytes();
                    if (byValueStruct && size < structSize)
                    {
                        // A struct read in pieces: each piece is the field at that place, or (a whole slot) the
                        // fields it holds.
                        HExpr structArg = ((SVal)sem).Expr;
                        if (FieldPlace(structArg, p.Type!, part, size) is PLocation field) _sem[slot] = new SVal(field.Location);
                        else if (size == 8 && part % 8 == 0 && StructLeaves(structArg, p.Type!, part, Math.Min(8, structSize - part)) is { } leaves)
                            _sem[slot] = new SParts(leaves, 8);
                        else _sem[slot] = SJunk.Instance;
                        continue;
                    }
                    // An eight-byte argument (a reference, a long, a double) whose slot the code also reaches four
                    // bytes at a time: each cell holds a half of it, and the two joined again are the argument.
                    if (!byValueStruct && !NoParamHalves && size == 4 && part is 0 or 4 && sem is SVal { Expr: var whole8 } &&
                        p.Type is { } wide && (IsReference(wide) || wide is PointerSig || BitsOf(wide) == 64))
                    {
                        _sem[slot] = new SHalf(whole8, part == 4, null);
                        continue;
                    }
                    // A struct handed over as the address of a copy, or a by-reference argument: an address, eight
                    // bytes, that the code reads four at a time. The two halves joined again are the reference.
                    if (!byValueStruct && !NoParamHalves && !NoRefParamHalves && size == 4 && part is 0 or 4 && sem is SRef reference)
                    {
                        if (!_refHalfMarks.TryGetValue(reference, out HExpr? mark))
                        {
                            mark = new HAddressOf(reference.Location) { Type = _m.Sigs.ByRef(reference.Type) };
                            _refHalfMarks[reference] = mark;
                            _halvedRefs[mark] = reference;
                        }
                        _sem[slot] = new SHalf(mark, part == 4, null);
                        continue;
                    }
                    if (part == 0) _sem[slot] = sem;
                }
            }
        }
    }

    // ---- materialization ---------------------------------------------------------------------------------------

    private static bool IsOrdered(Node n) => n.Op is Op.Store or Op.Call;

    /// <summary>
    /// Decides which values get a variable. A value can be folded into its single use when that use is in the
    /// same block and nothing that could change what the value means happens in between.
    /// </summary>
    private void DecideMaterialization()
    {
        foreach (Block b in _fn.Blocks)
        {
            // Position at which each node's value is finally consumed by something with a fixed position.
            var consumedAt = new Dictionary<Node, int>();
            for (int i = b.Nodes.Count - 1; i >= 0; i--)
            {
                Node n = b.Nodes[i];
                if (n.Dead || n.Type == VT.None) continue;
                _uses.TryGetValue(n, out List<Node>? uses);
                int useCount = uses?.Count ?? 0;
                if (useCount == 0) continue;
                if (useCount > 1)
                {
                    _materialize.Add(n);
                    continue;
                }
                Node user = uses![0];
                if (user.Op == Op.Phi || !ReferenceEquals(user.Block, b))
                {
                    _materialize.Add(n);
                    continue;
                }
                int at = user.IsEffect || _materialize.Contains(user) || user.Op == Op.Proj
                    ? _position[user]
                    : consumedAt.GetValueOrDefault(user, _position[user]);
                consumedAt[n] = at;

                if (n.Op == Op.Load)
                {
                    for (int k = i + 1; k < at; k++)
                        if (!b.Nodes[k].Dead && IsOrdered(b.Nodes[k]))
                        {
                            _materialize.Add(n);
                            break;
                        }
                }
                else if (n.Op == Op.Proj)
                {
                    // A call result may be folded into its consumer only when nothing else happens in between.
                    for (int k = i + 1; k < at; k++)
                    {
                        Node between = b.Nodes[k];
                        if (between.Dead) continue;
                        if (IsOrdered(between) || (between.Op == Op.Load && _materialize.Contains(between)))
                        {
                            _materialize.Add(n);
                            break;
                        }
                    }
                }
            }
        }
    }

    // ---- types -------------------------------------------------------------------------------------------------

    private TypeSig TypeForBits(VT type) => type switch
    {
        VT.I1 => _bool,
        VT.I8 => _byte,
        VT.I16 => _short,
        VT.I32 => _int,
        VT.I64 => _long,
        VT.F32 => _float,
        VT.F64 => _double,
        _ => _int,
    };

    /// <summary>
    /// The type parameters of the generic definition being recovered from the body its reference-type
    /// instantiations share: there, each stands for a reference type. (Of the recovery under way on this
    /// thread: each thread recovers its own methods.)
    /// </summary>
    [ThreadStatic] internal static HashSet<GenericParam>? OwnParameters;

    /// <summary>
    /// Whether nothing can be known of a type because it names a type parameter - other than the own ones of the
    /// definition being recovered, which are types like any other there.
    /// </summary>
    internal static bool Open(TypeSig? t) => t != null && t.ContainsGenericParameter && !OnlyOwnParameters(t);

    /// <summary>Whether a type names no type parameters but those.</summary>
    internal static bool OnlyOwnParameters(TypeSig? t) => t switch
    {
        null => true,
        GenericParamSig p => OwnParameters != null && OwnParameters.Contains(p.Parameter),
        GenericInstSig g => g.Arguments.All(OnlyOwnParameters),
        SzArraySig s => OnlyOwnParameters(s.ElementType),
        ArraySig a => OnlyOwnParameters(a.ElementType),
        PointerSig p => OnlyOwnParameters(p.ElementType),
        ByRefSig r => OnlyOwnParameters(r.ElementType),
        _ => !t.ContainsGenericParameter,
    };

    /// <summary>
    /// What is known of a type: for a type parameter of the definition being recovered, the class it is declared
    /// to derive from ("where T : Creature") - its fields and virtual methods are that class's.
    /// </summary>
    internal static TypeSig Declared(TypeSig type)
    {
        if (type is not GenericParamSig p || OwnParameters == null || !OwnParameters.Contains(p.Parameter)) return type;
        foreach (TypeSig constraint in p.Parameter.Constraints)
            if (constraint is not GenericParamSig && constraint.Definition is { IsInterface: false, IsValueType: false })
                return constraint;
        return type;
    }

    private static bool IsReference(TypeSig? t) => t switch
    {
        null => false,
        GenericParamSig own => OwnParameters != null && OwnParameters.Contains(own.Parameter),
        PrimitiveSig p => p.Element is Il2CppTypeEnum.String or Il2CppTypeEnum.Object,
        SzArraySig or ArraySig => true,
        TypeDefSig or GenericInstSig => !t.IsValueType,
        _ => false,
    };

    private static bool IsPointerLike(Sem s) => s switch
    {
        SRef or SKlass or SObjKlass or SStatics or SFrame or SUnboxed or SNewObject or SHierarchy or SInterfaceEntry or SNativeCode => true,
        SMethod or SRgctx => true,
        SVal v => IsReference(v.Type) || v.Type is PointerSig or ByRefSig || v.Type is PrimitiveSig { Element: Il2CppTypeEnum.I or Il2CppTypeEnum.U },
        _ => false,
    };

    private static bool IsFloat(TypeSig? t) => t is PrimitiveSig { Element: Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8 };

    private static bool IsUnsigned(TypeSig? t) => t is PrimitiveSig
    {
        Element: Il2CppTypeEnum.U1 or Il2CppTypeEnum.U2 or Il2CppTypeEnum.U4 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.U
            or Il2CppTypeEnum.Char or Il2CppTypeEnum.Boolean
    };

    private TypeSig? EvalKlass(Node n) => Eval(n) is SKlass k ? k.Type : null;

    // ---- emission helpers --------------------------------------------------------------------------------------

    private void Emit(HStmt s, ulong address = 0)
    {
        // Evaluating something that has no effect and whose value nobody uses is not a statement.
        if (s is HEval eval && IsPure(eval.Expression)) return;
        // Neither is putting something where it already is (a struct moved between two places that turned out
        // to be one).
        if (s is HAssign { Target: var into, Value: var held } && IsPure(into) && HirCleanup.Same(into, held)) return;
        s.Address = address;
        _cur.Statements.Add(s);
    }

    /// <summary>True when evaluating the expression can neither change anything nor fail in a way IL would notice.</summary>
    private static bool IsFloating(TypeSig? type) => type is PrimitiveSig { Element: Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8 };

    internal static bool IsPure(HExpr e) => e switch
    {
        HConst or HLocal or HArg or HMethodPointer or HMemberToken => true,
        HField f => f.Object == null || IsPure(f.Object),
        HArrayLength l => IsPure(l.Array),
        HAddressOf a => IsPure(a.Target),
        // Reading what a pointer points at is reading a field without the object around it.
        HDeref d => IsPure(d.Pointer),
        HUnary u => IsPure(u.Operand),
        // Division of whole numbers can fail (by zero); of floating-point numbers it cannot.
        HBinary { Op: HBinaryOp.Div or HBinaryOp.Rem } b when IsFloating(b.Type) && IsFloating(b.Left.Type) && IsFloating(b.Right.Type) => IsPure(b.Left) && IsPure(b.Right),
        HBinary b => b.Op is not (HBinaryOp.Div or HBinaryOp.DivUn or HBinaryOp.Rem or HBinaryOp.RemUn or HBinaryOp.AddOvf
            or HBinaryOp.AddOvfUn or HBinaryOp.SubOvf or HBinaryOp.SubOvfUn or HBinaryOp.MulOvf or HBinaryOp.MulOvfUn) && IsPure(b.Left) && IsPure(b.Right),
        HCompare c => IsPure(c.Left) && IsPure(c.Right),
        HConv c => c.Kind < HConvKind.OvfI1 && IsPure(c.Operand),
        HSelect s => IsPure(s.Condition) && IsPure(s.WhenTrue) && IsPure(s.WhenFalse),
        HTypeExpr t => t.Op is HTypeOp.IsInst or HTypeOp.Default or HTypeOp.SizeOf or HTypeOp.TypeToken && (t.Operand == null || IsPure(t.Operand)),
        HOpaque o => o.Text is "undefined" or "frame" && o.Operands.All(IsPure),
        // The same bits read as another type (BitsOfValue, ValueFromBits): a way of writing a value, not an action.
        HCall { This: null, Method: { Name: "SingleToInt32Bits" or "Int32BitsToSingle" or "DoubleToInt64Bits" or "Int64BitsToDouble", DeclaringType: { Name: "BitConverter", Namespace: "System" } } } c =>
            c.Arguments.All(IsPure),
        // The same through the value's bytes, where the class library has no call for it (SingleBits, SingleFromBits).
        HCall { This: null, Method: { Name: "ToInt32" or "ToSingle", DeclaringType: { Name: "BitConverter", Namespace: "System" } } } c
            when IsReinterpreted(c, "", c.Method.Name, out HExpr original) => IsPure(original),
        _ => false,
    };

    private HExpr Null() => new HConst(null, _object);

    /// <summary>The managed value of a node, or an opaque placeholder (with a recorded problem) when it has none.</summary>
    private HExpr Value(Node n)
    {
        Sem s = Eval(n);
        switch (s)
        {
            case SVal v:
                return v.Expr;
            case SRef r:
                return new HAddressOf(r.Location) { Type = _m.Sigs.ByRef(r.Type) };
            case SNewObject o:
                return new HLocal(o.Variable) { Type = o.Type };
            case SType t:
                return new HTypeExpr(HTypeOp.TypeToken, t.Type, null) { Type = _m.FindType("System.RuntimeTypeHandle")?.Sig };
            case SMethod method:
                return new HMethodPointer
                {
                    Method = method.Method,
                    DeclaringType = method.Inst is { ClassArguments.Length: > 0 } inst ? _m.Sigs.GenericInst(method.Method.DeclaringType, inst.ClassArguments) : null,
                    MethodArguments = method.Inst?.MethodArguments ?? [],
                    Type = _nint,
                };
            case SPair p:
                return CombineParts([new Part(0, 4, p.Low), new Part(4, 4, p.High)], 8);
            case SParts ps:
                return CombineParts(ps.Parts, ps.Size);
            case SHalf h when h.Part != null:
                return h.Part;
            case SHalf h:
            {
                // Half of a 64-bit quantity used on its own: a genuine bit-level operation. (Half of a
                // reference is no number C# could make of it.)
                if (IsReference(h.Whole.Type) || h.Whole.Type is ByRefSig) Problem("half of a reference used on its own");
                HExpr bits = IsFloat(h.Whole.Type) ? FloatBits(h.Whole) : h.Whole;
                if (h.High) bits = new HBinary(HBinaryOp.Shr, bits, new HConst(32, _int)) { Type = _long };
                return new HConv(HConvKind.I4, bits) { Type = _int };
            }
            case SFrame f when BufferAddress(f.Offset) is { } buffer:
                // An address in a stackalloc'd buffer: the buffer's pointer plus an offset.
                return buffer;
            case SFrame f when _fakeBoxes.TryGetValue(f.Offset, out TypeSig? boxed):
                // A value given an object header on the stack so that it can be passed as an object: a box.
                return new HTypeExpr(HTypeOp.Box, boxed, new HLocal(FrameVar(f.Offset + _header, boxed)) { Type = boxed }) { Type = _object };
            case SVTable entry when VirtualPointer(entry) is { } virtualPointer:
                return virtualPointer;
            case SLostRegister:
                Problem(LostRegisterUsed);
                return new HOpaque("undefined") { Type = TypeForBits(n.Type) };
            case SJunk:
                return new HOpaque("undefined") { Type = TypeForBits(n.Type) };
            default:
                // A piece of a stack struct that did not turn out to be part of a struct copy: the bytes are
                // likely other data in a reused slot (see StackSplitting).
                if (s is SChunk && n.Op == Op.Load && IsFrameAddress(n.In[0], out int pieceAt)) FrameConflicts.Add(pieceAt);
                string asData = $"{s.GetType().Name[1..]} value used as data (%{n.Id} {n.Op})";
                Problem(asData);
                return Site(new HOpaque(s.GetType().Name[1..].ToLowerInvariant()) { Type = TypeForBits(n.Type) }, asData);
        }
    }

    private HVar Temp(TypeSig? type, VT bits) => _h.NewLocal(type ?? TypeForBits(bits), "t");

    // ---- phis --------------------------------------------------------------------------------------------------

    private void DeclarePhis(Block b)
    {
        foreach (Node phi in b.Phis)
        {
            if (phi.Dead || phi.Type == VT.Flags) continue;
            // A merged code pointer of virtual methods: the number of the one each way in picks.
            if (!NoMergedDispatch && DispatchPhis.TryGetValue(phi, out MethodDef[]? ways))
            {
                HVar which = _h.NewLocal(_int, "which");
                _phiVar[phi] = which;
                _phiOfVar[which] = phi;
                _sem[phi] = new SVal(new HLocal(which) { Type = _int });
                _dispatch[phi] = (which, ways, ways.Distinct().ToArray());
                continue;
            }
            if (_framePhis.TryGetValue(phi, out int frameAt))
            {
                _sem[phi] = new SFrame(frameAt);
                continue;
            }
            if (_refPhis.TryGetValue(phi, out Node? bound) && _sem.TryGetValue(bound, out Sem? boundSem))
            {
                _sem[phi] = boundSem;
                continue;
            }
            // One class's static data whichever way in: the compiler merged the paths after each read the
            // pointer (tail merging), and the field reads after the merge are of that class's statics.
            if (!NoMergedStatics && MergedStatics(phi) is { } statics)
            {
                _sem[phi] = statics;
                continue;
            }
            // The address of one stack object or another, by the way in: a reference variable.
            if (MergedPointee(phi) is { } pointee)
            {
                TypeSig reference = _m.Sigs.ByRef(pointee);
                HVar merged = _h.NewLocal(reference, "m");
                _phiVar[phi] = merged;
                _phiOfVar[merged] = phi;
                _mergedAddresses.Add(phi);
                MergedAddressVariables.Add(merged);
                _sem[phi] = new SVal(new HLocal(merged) { Type = reference });
                continue;
            }
            // Type from the first input that already has a meaning; refined when inputs are assigned.
            TypeSig? type = null;
            for (int way = 0; way < phi.In.Length; way++)
            {
                Node input = phi.In[way];
                // What a way in gives where it was just found to be null ("a?.b") says nothing about the type.
                if (way < b.Preds.Count && ZeroOnEdge(b.Preds[way], b, input) && !NoStructZero) continue;
                if (_sem.TryGetValue(input, out Sem? s) && s is SVal v && v.Type != null)
                {
                    type = v.Type;
                    break;
                }
            }
            if (_knownPhiTypes != null && _knownPhiTypes.TryGetValue(phi, out TypeSig? known)) type = known;
            HVar variable = _h.NewLocal(type ?? TypeForBits(phi.Type), "m");
            _phiVar[phi] = variable;
            _phiOfVar[variable] = phi;
            _sem[phi] = new SVal(new HLocal(variable) { Type = type });
            if (type != null) PhiTypes[phi] = type;
        }
    }

    private static readonly bool NoMergedStatics = Environment.GetEnvironmentVariable("REWIND_NO_MERGED_STATICS") != null;

    /// <summary>The static data of one class, when every way into the merge gives that pointer; null otherwise.</summary>
    private SStatics? MergedStatics(Node phi)
    {
        SStatics? found = null;
        foreach (Node input in phi.In)
        {
            if (ReferenceEquals(input, phi)) continue;
            // (Only a read of a class's static data pointer is looked at here, before the blocks are built: the
            // class, a constant of the image, and the offset of its static data.)
            Sem? s = input.Op == Op.Phi ? _sem.GetValueOrDefault(input)
                : input.Op == Op.Load && input.In[0] is { Op: Op.Add } address && address.In[1].IsConst &&
                  address.In[1].Imm == _p.Klass.StaticFields && address.In[0].Op is Op.SlotValue or Op.Load &&
                  Peek(address.In[0]) is SKlass klass ? new SStatics(klass.Type) : null;
            if (s is not SStatics statics) return null;
            if (found == null) found = statics;
            else if (found.Type.Key != statics.Type.Key) return null;
        }
        return found;
    }

    /// <summary>Assignments that give a successor's merged values their value along the edge from this block.</summary>
    private List<HAssign> PhiCopies(Block from, Block to)
    {
        var copies = new List<HAssign>();
        int index = to.Preds.IndexOf(from);
        if (index < 0) return copies;
        foreach (Node phi in to.Phis)
        {
            if (!_phiVar.TryGetValue(phi, out HVar? variable) || index >= phi.In.Length) continue;
            Node input = phi.In[index];
            if (ReferenceEquals(input, phi)) continue;
            // "a?.b": on the way in where a was just found to be null, the merged value is given a itself -
            // which there is null, whatever a's type. It says nothing about the merged value's type.
            if (ZeroOnEdge(from, to, input))
            {
                copies.Add(new HAssign(new HLocal(variable) { Type = variable.Type }, Coerce(new HConst(0L, _long), variable.Type)));
                continue;
            }
            // A reference variable that on this way in refers to a static field at the very start of its class's
            // statics ("Vector3.zero" inlined to the address of Vector3.zeroVector): the field.
            if (!NoStaticRefs && variable.Type is ByRefSig { ElementType: var staticElement } && Peek(input) is SStatics &&
                _p.Layouts.SizeOf(staticElement) is { Known: true, Size: > 0 } staticSize &&
                ResolvePlace(input, staticSize.Size) is PLocation { Location: HField { Object: null } staticField } staticPlace &&
                staticPlace.Type.Key == staticElement.Key)
            {
                copies.Add(new HAssign(new HLocal(variable) { Type = variable.Type }, new HAddressOf(staticField) { Type = variable.Type }));
                continue;
            }
            // The number of the method this way in picks (see DeclarePhis).
            if (_dispatch.TryGetValue(phi, out var dispatch))
            {
                int number = Array.IndexOf(dispatch.Distinct, dispatch.Ways[index]);
                copies.Add(new HAssign(new HLocal(variable) { Type = _int }, new HConst(number, _int)));
                continue;
            }
            // A reference variable (see DeclarePhis): on this way in it refers to this stack object. (Also where
            // other ways in give it something else, a field's address: the variable is then known as a reference
            // from the first build on.)
            if ((_mergedAddresses.Contains(phi) || !NoMixedMerges) && variable.Type is ByRefSig { ElementType: var element } && IsFrameAddress(input, out int objectAt) &&
                MergedPlace(objectAt, element) is { } referred)
            {
                copies.Add(new HAssign(new HLocal(variable) { Type = variable.Type }, new HAddressOf(referred) { Type = variable.Type }));
                continue;
            }
            // What a way in gives the merged value is only looked at here: it is read for real when the merged
            // value is (SettlePhis).
            if (!_phiInputs.TryGetValue(phi, out List<Node>? given)) _phiInputs[phi] = given = [];
            given.Add(input);
            Sem s;
            HExpr value;
            Node? subject = _peekSubject;
            _peeking++;
            _peekSubject = input;
            try
            {
                s = Eval(input);
                if (s is SJunk) continue;
                // What cannot be said about the value as the merged value's copy (a class pointer is no data) is
                // held with the merged value: it counts when that is read, not when the value itself is used
                // for what it is (the class's methods read through it, the merge given back to each way in).
                if (!NoCopyProblemsOnPhi) _peekSubject = phi;
                // A merged struct that travels in a register (a struct of 8 bytes returned in RAX): what a way in
                // gives as the register's bits is the struct those bits are, not a number made into it.
                value = !NoMergedStructBits && IsStructType(variable.Type) && input.Type is VT.I32 or VT.I64 &&
                    (s is SPair || s is SVal { Expr: not HConst, Type: PrimitiveSig bits } && !IsReference(bits) && BitsOf(bits) is > 0 and <= 64) &&
                    _p.Layouts.Of(variable.Type) is { Known: true, Size: > 0 and <= 8 }
                    ? StructFromBits(input, variable.Type)
                    : Value(input);
            }
            finally
            {
                _peekSubject = subject;
                _peeking--;
            }
            if (value is HLocal l && ReferenceEquals(l.Variable, variable)) continue;
            // Adopt a more specific type once a typed input shows up.
            if (value.Type != null && IsWeakType(variable.Type) && !IsWeakType(value.Type))
            {
                variable.Type = value.Type;
                PhiTypes[phi] = value.Type;
                PhiTypesRefined = true;
                // Uses translated from here on see the type; earlier ones need the second build.
                if (_sem.TryGetValue(phi, out Sem? current) && current is SVal { Expr: HLocal local } && local.Type == null) local.Type = value.Type;
            }
            // A merged reference holds whatever any way in gives it, so its type must be one that every such
            // value fits: the nearest common base, not the type of whichever value came first. (A value the
            // code has checked to be of a class counts as that class.)
            if (value is not HConst && IsStructType(value.Type) && IsStructType(variable.Type) && !Open(value.Type))
                _phiStructs[phi] = _phiStructs.TryGetValue(phi, out TypeSig? seen) && (seen == null || seen.Key != value.Type!.Key) ? null : value.Type;
            TypeSig? incoming = _castTypes.TryGetValue(input, out List<TypeSig>? checkedAs) && checkedAs.Count == 1 ? checkedAs[0] : value.Type;
            if (value is not HConst && incoming != null && IsReference(incoming) && !Open(incoming))
                _phiJoins[phi] = _phiJoins.TryGetValue(phi, out TypeSig? soFar) ? JoinTypes(soFar, incoming) : incoming;
            if (value is not HConst && incoming != null && IsReference(incoming) && IsReference(variable.Type) && !Open(incoming) &&
                !Open(variable.Type) && !IsAssignable(incoming, variable.Type))
            {
                TypeSig joined = JoinTypes(variable.Type, incoming);
                if (!ReferenceEquals(joined, variable.Type))
                {
                    variable.Type = joined;
                    PhiTypes[phi] = joined;
                    PhiTypesRefined = true;
                    if (_sem.TryGetValue(phi, out Sem? merged) && merged is SVal { Expr: HLocal mergedLocal }) mergedLocal.Type = joined;
                }
            }
            copies.Add(new HAssign(new HLocal(variable) { Type = variable.Type }, Coerce(value, variable.Type)));
        }
        return Sequentialize(copies);
    }

    /// <summary>True when <paramref name="value"/> is known to be zero along the edge: the branch that leads there tested it.</summary>
    private static bool ZeroOnEdge(Block from, Block to, Node value)
    {
        if (from.Terminator is not { Op: Op.Branch } term || from.Succs.Count != 2 || ReferenceEquals(from.Succs[0], from.Succs[1])) return false;
        Node cond = term.In[0];
        // The low half of what was found to be zero is zero as well (a merged value of 32 bits).
        if (value.Op == Op.Trunc && value.In[0].Type == VT.I64 && !NoStructZero) value = value.In[0];
        if (cond.Op is not (Op.CmpEq or Op.CmpNe) || cond.In.Length != 2 || !cond.In[1].IsConstValue(0) || !ReferenceEquals(cond.In[0], value)) return false;
        if (value.Type != VT.I64) return false;
        return ReferenceEquals(to, from.Succs[cond.Op == Op.CmpEq ? 0 : 1]);
    }

    private static readonly bool NoCopyProblemsOnPhi = Environment.GetEnvironmentVariable("REWIND_NO_COPY_PROBLEMS_ON_PHI") != null;

    private readonly Dictionary<HVar, Node> _phiOfVar = [];
    /// <summary>The nearest common type of the references each merged value was given in this build.</summary>
    private readonly Dictionary<Node, TypeSig> _phiJoins = [];

    /// <summary>
    /// A merged reference typed wider than what it is given (in an earlier build one of its values was known
    /// only as "object", say) takes the common type of its values as they are known now.
    /// </summary>
    private void RefinePhiJoins()
    {
        foreach (var (phi, joined) in _phiJoins)
        {
            if (!_phiVar.TryGetValue(phi, out HVar? variable) || !IsReference(variable.Type) || Open(variable.Type)) continue;
            if (ReferenceEquals(joined, variable.Type) || joined.Key == variable.Type.Key || !IsAssignable(joined, variable.Type)) continue;
            PhiTypes[phi] = joined;
            PhiTypesRefined = true;
        }
    }
    /// <summary>The struct type all values a merged struct was given in this build have (null where they differ).</summary>
    private readonly Dictionary<Node, TypeSig?> _phiStructs = [];

    /// <summary>
    /// A merged struct typed as something none of its values is: the type was taken over from an earlier build,
    /// before the stack object its values come from was found to be another struct of that size (two methods
    /// folded into one body, each of its own struct). It takes the type its values have now.
    /// </summary>
    private void RefinePhiStructs()
    {
        foreach (var (phi, type) in _phiStructs)
        {
            if (type == null || !_phiVar.TryGetValue(phi, out HVar? variable) || type.Key == variable.Type.Key) continue;
            if (_p.Layouts.SizeOf(type).Size != _p.Layouts.SizeOf(variable.Type).Size) continue;
            PhiTypes[phi] = type;
            PhiTypesRefined = true;
        }
    }

    /// <summary>How often a merged value of integer type was used where a float is expected, and as which float type.</summary>
    private readonly Dictionary<Node, (int Count, TypeSig Type)> _floatUses = [];

    /// <summary>
    /// A merged value all of whose uses want a float is a float: the machine merely moved its bits around in
    /// a general register. Typed that way on the next build, its uses need no reinterpretation.
    /// </summary>
    private void RefineFloatPhis()
    {
        foreach (var (phi, (count, type)) in _floatUses)
        {
            if (!_uses.TryGetValue(phi, out List<Node>? users) || users.Count == 0 || count < users.Count) continue;
            if (PhiTypes.TryGetValue(phi, out TypeSig? known) && ReferenceEquals(known, type)) continue;
            PhiTypes[phi] = type;
            PhiTypesRefined = true;
        }
    }

    /// <summary>The bit pattern of a float (as int) or of a double (as long).</summary>
    private HExpr FloatBits(HExpr e)
    {
        if (ReferenceEquals(e.Type, _float))
        {
            if (e is HConst { Value: float f }) return new HConst(BitConverter.SingleToInt32Bits(f), _int);
            if ((SingleBits(e) ?? BitCast(e, _int)) is { } asInt) return asInt;
            Problem("float reinterpreted as bits (no BitConverter in this build)");
            return new HOpaque("float_bits", e) { Type = _int };
        }
        if (e is HConst { Value: double d }) return new HConst(BitConverter.DoubleToInt64Bits(d), _long);
        if (BitConverterMethod("DoubleToInt64Bits", _double) is { } toLong) return new HCall { Method = toLong, Arguments = [e], Type = _long };
        if (BitCast(e, _long) is { } asLong) return asLong;
        Problem("double reinterpreted as bits (no BitConverter in this build)");
        return new HOpaque("double_bits", e) { Type = _long };
    }

    private bool IsWeakType(TypeSig t) => ReferenceEquals(t, _int) || ReferenceEquals(t, _long) || ReferenceEquals(t, _bool) || ReferenceEquals(t, _byte) || ReferenceEquals(t, _short);

    private static bool Mentions(HExpr e, HVar v)
    {
        switch (e)
        {
            case HLocal l: return ReferenceEquals(l.Variable, v);
            case HField f: return f.Object != null && Mentions(f.Object, v);
            case HElement el: return Mentions(el.Array, v) || Mentions(el.Index, v);
            case HArrayLength len: return Mentions(len.Array, v);
            case HAddressOf a: return Mentions(a.Target, v);
            case HDeref d: return Mentions(d.Pointer, v);
            case HUnary u: return Mentions(u.Operand, v);
            case HBinary b: return Mentions(b.Left, v) || Mentions(b.Right, v);
            case HCompare c: return Mentions(c.Left, v) || Mentions(c.Right, v);
            case HConv c: return Mentions(c.Operand, v);
            case HCall call: return (call.This != null && Mentions(call.This, v)) || call.Arguments.Any(a => Mentions(a, v));
            case HNewObject n: return n.Arguments.Any(a => Mentions(a, v));
            case HNewArray na: return Mentions(na.Length, v);
            case HTypeExpr t: return t.Operand != null && Mentions(t.Operand, v);
            case HSelect s: return Mentions(s.Condition, v) || Mentions(s.WhenTrue, v) || Mentions(s.WhenFalse, v);
            case HOpaque o: return o.Operands.Any(a => Mentions(a, v));
            default: return false;
        }
    }

    /// <summary>Orders parallel assignments so none reads a variable another has already overwritten.</summary>
    private List<HAssign> Sequentialize(List<HAssign> copies)
    {
        if (copies.Count < 2) return copies;
        var result = new List<HAssign>();
        var pending = new List<HAssign>(copies);
        while (pending.Count > 0)
        {
            // Emit a copy whose destination no other pending copy still needs to read.
            int pick = pending.FindIndex(c =>
            {
                HVar dest = ((HLocal)c.Target).Variable;
                return !pending.Any(o => !ReferenceEquals(o, c) && Mentions(o.Value, dest));
            });
            if (pick < 0)
            {
                // A cycle (a swap): save one destination's old value first.
                HAssign c = pending[0];
                HVar dest = ((HLocal)c.Target).Variable;
                HVar saved = _h.NewLocal(dest.Type, "s");
                result.Add(new HAssign(new HLocal(saved) { Type = dest.Type }, new HLocal(dest) { Type = dest.Type }));
                for (int i = 1; i < pending.Count; i++)
                    pending[i] = new HAssign(pending[i].Target, Substitute(pending[i].Value, dest, saved));
                pick = 0;
            }
            result.Add(pending[pick]);
            pending.RemoveAt(pick);
        }
        return result;
    }

    /// <summary>
    /// "t = x + 1; ...; x = t" at the end of a block is "x = x + 1" when nothing in between looks at x: the
    /// temporary only exists because the machine computed the next value before the loop came around. Assigning
    /// straight to the merged variable gives back the statement the source had.
    /// </summary>
    private List<HAssign> CoalesceCopies(List<HAssign> copies)
    {
        if (copies.Count == 0) return copies;
        List<HStmt> statements = _cur.Statements;
        var remaining = new List<HAssign>(copies);

        int DefinitionOf(HVar temp)
        {
            for (int i = statements.Count - 1; i >= 0; i--)
                if (statements[i] is HAssign { Target: HLocal l } && ReferenceEquals(l.Variable, temp))
                    return i;
            return -1;
        }
        bool StatementMentions(HStmt s, HVar v) => s switch
        {
            HAssign a => Mentions(a.Target, v) || Mentions(a.Value, v),
            HEval e => Mentions(e.Expression, v),
            HReturn r => r.Value != null && Mentions(r.Value, v),
            HThrow t => t.Exception != null && Mentions(t.Exception, v),
            HBranch br => Mentions(br.Condition, v),
            HSwitch sw => Mentions(sw.Value, v),
            _ => false,
        };

        // Latest definition first, so that an earlier rewrite never has to look past a later one's effect.
        foreach (HAssign copy in copies.OrderByDescending(c => c.Value is HLocal l ? DefinitionOf(l.Variable) : -1).ToList())
        {
            if (copy.Value is not HLocal { Variable: var temp } || copy.Target is not HLocal { Variable: var merged }) continue;
            if (!_singleUseTemps.Contains(temp) || temp.AddressTaken || merged.AddressTaken) continue;
            int at = DefinitionOf(temp);
            if (at < 0) continue;
            bool safe = true;
            for (int i = at + 1; i < statements.Count && safe; i++)
                if (StatementMentions(statements[i], merged) || StatementMentions(statements[i], temp)) safe = false;
            foreach (HAssign other in remaining)
                if (!ReferenceEquals(other, copy) && Mentions(other.Value, merged)) safe = false;
            if (!safe) continue;
            var definition = (HAssign)statements[at];
            statements[at] = new HAssign(new HLocal(merged) { Type = merged.Type }, definition.Value) { Address = definition.Address };
            remaining.Remove(copy);
        }
        return remaining;
    }

    /// <summary>Temporaries whose value is read exactly once.</summary>
    private readonly HashSet<HVar> _singleUseTemps = [];

    private static HExpr Substitute(HExpr e, HVar from, HVar to)
    {
        if (e is HLocal l && ReferenceEquals(l.Variable, from)) return new HLocal(to) { Type = l.Type };
        return e; // sources of phi copies are locals or constants once materialized
    }

    // ---- blocks ------------------------------------------------------------------------------------------------

    private void ProcessBlock(Block b)
    {
        _block = b;
        _cur = _hblock[b];
        foreach (Node n in b.Nodes)
        {
            if (n.Dead) continue;
            _node = n;
            switch (n.Op)
            {
                case Op.Store:
                    // A piece of a struct copy: the copy stands where its last piece is stored.
                    if (_pieceMembers.Contains(n))
                    {
                        if (_pieceCopies.TryGetValue(n, out PieceCopy? copy)) EmitPieceCopy(copy);
                        break;
                    }
                    // A piece of a struct being cleared: the fill stands where its first piece is stored.
                    if (_fillMembers.Contains(n))
                    {
                        if (!_pieceFills.TryGetValue(n, out PieceFill? fill)) break;
                        if (CutsAcrossFields(fill) && TryEmitFill(fill.To, fill.Size, fill.Address, quiet: true)) break;
                        // Not one thing cleared, as far as can be told: each store as the code has it.
                        foreach (Node member in fill.Members) _fillMembers.Remove(member);
                    }
                    EmitStore(n);
                    break;
                case Op.Call:
                    EmitCall(n, tail: false);
                    break;
                case Op.TailCall:
                    EmitCall(n, tail: true);
                    break;
                case Op.Jump or Op.Branch or Op.Switch or Op.Return or Op.Unreachable:
                    EmitTerminator(b, n);
                    break;
                case Op.Proj:
                    break; // given a meaning when its call is processed
                default:
                    if (_pieceMembers.Contains(n)) break; // read where the copy it is a piece of stands
                    if (_materialize.Contains(n)) Materialize(n);
                    break;
            }
        }
    }

    private void Materialize(Node n)
    {
        if (_sem.ContainsKey(n)) return;
        // A value only merged values take is only looked at here, as what a way in gives a merged value is
        // (PhiCopies): an outgoing-argument slot keeps what the last call was handed, the slot is "merged" where
        // paths meet, and nothing may ever read it. What cannot be said about it counts when it is read.
        bool looked = OnlyMerged(n);
        Sem s;
        if (looked)
        {
            Node? outer = _computing, subject = _peekSubject;
            _peeking++;
            _computing = n;
            _peekSubject = n;
            try
            {
                s = Compute(n);
            }
            finally
            {
                _computing = outer;
                _peekSubject = subject;
                _peeking--;
            }
        }
        else s = Compute(n);
        switch (s)
        {
            case SVal v when v.Expr is not (HConst or HLocal or HArg):
            {
                HVar t = Temp(v.Type, n.Type);
                if (_uses.TryGetValue(n, out List<Node>? users) && users.Count == 1) _singleUseTemps.Add(t);
                if (v.Expr is HField) _fieldTemps[t] = (HField)v.Expr;
                var assign = new HAssign(new HLocal(t) { Type = t.Type }, v.Expr);
                Emit(assign, n.Addr);
                if (looked && Held(n)) _lookedAt[n] = (_cur, assign);
                _sem[n] = new SVal(new HLocal(t) { Type = t.Type });
                break;
            }
            case SPair p when n.Op == Op.Load:
            {
                // Read both halves now so later stores cannot change what they mean.
                HVar lo = Temp(p.Low.Type, VT.I32), hi = Temp(p.High.Type, VT.I32);
                Emit(new HAssign(new HLocal(lo) { Type = lo.Type }, p.Low), n.Addr);
                Emit(new HAssign(new HLocal(hi) { Type = hi.Type }, p.High), n.Addr);
                _sem[n] = new SPair(new HLocal(lo) { Type = lo.Type }, new HLocal(hi) { Type = hi.Type });
                break;
            }
            default:
                _sem[n] = s;
                break;
        }
    }

    private int _evalDepth;
    private const int MaxEvalDepth = 20_000;

    private Sem Eval(Node n)
    {
        if (_sem.TryGetValue(n, out Sem? s))
        {
            if (n.Op == Op.Phi)
            {
                if (_peeking == 0) _phiRead.Add(n);
                else if (_computing != null)
                {
                    if (!_heldPhiReads.TryGetValue(_computing, out List<Node>? reads)) _heldPhiReads[_computing] = reads = [];
                    reads.Add(n);
                }
            }
            if (_peeking == 0 && (_heldProblems.Count != 0 || _heldUnder.Count != 0 || _heldPhiReads.Count != 0)) Release(n);
            // Looked at as part of computing another value: what is held for it goes with that value.
            else if (_peeking > 0 && _computing != null && !ReferenceEquals(_computing, n) && !NoHeldTemps &&
                     (_heldProblems.Count != 0 || _heldUnder.Count != 0 || _heldPhiReads.Count != 0) && Held(n))
            {
                if (!_heldUnder.TryGetValue(_computing, out List<Node>? parts)) _heldUnder[_computing] = parts = [];
                if (!parts.Contains(n)) parts.Add(n);
            }
            return s;
        }
        // A value that (through a defect upstream) depends on itself would recurse forever; fail cleanly instead.
        if (++_evalDepth > MaxEvalDepth)
        {
            _evalDepth = 0;
            throw new InvalidOperationException($"value %{n.Id} ({n.Op}) is nested too deeply or depends on itself");
        }
        Node? outer = _computing;
        _computing = n;
        try
        {
            s = Compute(n);
        }
        finally
        {
            _computing = outer;
            if (_evalDepth > 0) _evalDepth--;
        }
        if (_peeking > 0 && outer != null && (_heldProblems.ContainsKey(n) || _heldUnder.ContainsKey(n) || _heldPhiReads.ContainsKey(n)))
        {
            if (!_heldUnder.TryGetValue(outer, out List<Node>? parts)) _heldUnder[outer] = parts = [];
            parts.Add(n);
        }
        _sem[n] = s;
        return s;
    }

    private void EmitTerminator(Block b, Node term)
    {
        HBlock Target(int i) => _hblock[b.Succs[i]];

        // An edge needs its own block when it must carry copies but the source has other successors.
        HBlock Edge(int i)
        {
            Block to = b.Succs[i];
            List<HAssign> copies = PhiCopies(b, to);
            if (copies.Count == 0) return _hblock[to];
            var edge = new HBlock { Id = _h.Blocks.Count, Scope = b.Scope };
            _h.Blocks.Add(edge);
            foreach (HAssign c in copies) edge.Statements.Add(c);
            edge.Statements.Add(new HJump(_hblock[to]));
            return edge;
        }

        switch (term.Op)
        {
            case Op.Jump:
                if (b.Succs.Count != 1)
                {
                    Emit(new HThrow(new HOpaque("no_successor")), term.Addr);
                    break;
                }
                foreach (HAssign c in CoalesceCopies(PhiCopies(b, b.Succs[0]))) Emit(c, term.Addr);
                Emit(new HJump(Target(0)), term.Addr);
                break;
            case Op.Branch when Function.IsTryEntry(term.In[0]) && b.Succs.Count == 2:
            {
                // The gate of a try region: the ordinary way continues into the protected code; the handler is
                // reached only by an exception.
                HTryRegion region = RegionFor((int)term.In[0].Aux!);
                region.Outer = b.Scope;
                region.Entry = _hblock[b.Succs[1]];
                region.HandlerEntry = _hblock[b.Succs[0]];
                Emit(new HJump(Edge(1)), term.Addr);
                break;
            }
            case Op.Branch:
            {
                if (b.Succs.Count == 2 && InstanceTestOf(term.In[0]) is var (tested, testedType, whenTrue))
                {
                    Block instanceSide = b.Succs[whenTrue ? 0 : 1];
                    if (instanceSide.Preds.Count == 1 && !ReferenceEquals(instanceSide, b))
                    {
                        if (!_typeFacts.TryGetValue(instanceSide, out List<(Node Object, TypeSig Type)>? facts)) _typeFacts[instanceSide] = facts = [];
                        facts.Add((tested, testedType));
                    }
                }
                HExpr condition = Condition(term.In[0]);
                if (b.Succs.Count != 2)
                {
                    Problem("branch without two successors");
                    Emit(new HThrow(new HOpaque("bad_branch")), term.Addr);
                    break;
                }
                Emit(new HBranch(condition, Edge(0), Edge(1)), term.Addr);
                break;
            }
            case Op.Switch:
            {
                // A jump table is indexed by a 64-bit copy of the 32-bit value ("movsxd rax, ecx"): the switch is on
                // the value itself, which is what it was in C#. (The C# decompiler follows an iterator's state into
                // a switch on the state, but not through a copy made wider: it then takes the state for an ordinary
                // variable, drops the writes that advance it, and the iterator yields its first item for ever.)
                Node index = term.In[0];
                if (!NoWideSwitches && index.Op is Op.SExt or Op.ZExt && index.In[0].Type == VT.I32) index = index.In[0];
                HExpr value = Value(index);
                var targets = new HBlock[b.Succs.Count];
                for (int i = 0; i < targets.Length; i++) targets[i] = Edge(i);
                // The native table only covers in-range values; the range check before it supplies the default.
                Emit(new HSwitch(value, targets, targets.Length > 0 ? targets[^1] : _cur), term.Addr);
                break;
            }
            case Op.Return:
                EmitReturn(term);
                break;
            case Op.Unreachable:
                // Reached only after a call that does not return; if nothing was emitted for it, say so.
                if (_cur.Statements.Count == 0 || _cur.Statements[^1] is not (HThrow or HReturn))
                    Emit(new HThrow(new HOpaque("unreachable")), term.Addr);
                break;
        }
    }

    private void EmitReturn(Node ret)
    {
        switch (_abi.Return)
        {
            case ReturnKind.Void:
                Emit(new HReturn(null), ret.Addr);
                return;
            case ReturnKind.Buffer:
                Emit(new HReturn(new HLocal(_returnBuffer!) { Type = _returnBuffer!.Type }), ret.Addr);
                return;
            case ReturnKind.Double:
            {
                if (ret.In.Length == 2 && Eval(ret.In[0]) is SHalf { High: false } lo && Eval(ret.In[1]) is SHalf { High: true } hi &&
                    ReferenceEquals(lo.Whole, hi.Whole))
                {
                    Emit(new HReturn(lo.Whole), ret.Addr);
                    return;
                }
                if (ret.In.Length == 2 && SignedLanes(ret.In[0], ret.In[1]) is { } signed)
                {
                    Emit(new HReturn(signed), ret.Addr);
                    return;
                }
                // The two halves come from different places: the double is whatever those 64 bits spell.
                HExpr bits = CombineParts([new Part(0, 4, HalfBits(ret.In[0])), new Part(4, 4, ret.In.Length > 1 ? HalfBits(ret.In[1]) : new HConst(0, _int))], 8);
                Emit(new HReturn(ValueFromBits(bits, _double, 8)), ret.Addr);
                return;
            }
            case ReturnKind.StructInRegister:
                Emit(new HReturn(StructFromBits(ret.In[0], _abi.ReturnType)), ret.Addr);
                return;
            case ReturnKind.StructInRegisterPair:
                Emit(new HReturn(StructFromRegisters(ret.In, _abi.ReturnType, Carried.Words, ret.Addr)), ret.Addr);
                return;
            case ReturnKind.FloatAggregate:
                Emit(new HReturn(StructFromRegisters(ret.In, _abi.ReturnType, _abi.ReturnIsDouble ? Carried.Doubles : Carried.Floats, ret.Addr)), ret.Addr);
                return;
            default:
                Emit(new HReturn(ValueFor(ret.In[0], _abi.ReturnType)), ret.Addr);
                return;
        }
    }

    /// <summary>A branch condition as a boolean expression.</summary>
    private HExpr Condition(Node n)
    {
        HExpr e = Value(n);
        if (e.Type == null) e.Type = _bool;
        return e;
    }

    private bool IsBool(TypeSig? t) => ReferenceEquals(t, _bool);

    /// <summary>
    /// Makes the narrowing explicit when a wider value lands in a location of a small integer type, as a cast
    /// in the source would have.
    /// </summary>
    private HExpr Narrow(HExpr e, TypeSig target)
    {
        if (target is not PrimitiveSig || IsBool(target)) return e;
        int bits = BitsOf(target);
        if (bits is not (8 or 16) || e is HConst) return e;
        bool signed = IsSignedSmall(target);
        HConvKind kind = (bits, signed) switch
        {
            (8, true) => HConvKind.I1,
            (8, false) => HConvKind.U1,
            (16, true) => HConvKind.I2,
            _ => HConvKind.U2,
        };
        if (e is HConv { Kind: HConvKind.I1 or HConvKind.U1 or HConvKind.I2 or HConvKind.U2 } c)
        {
            int had = c.Kind is HConvKind.I1 or HConvKind.U1 ? 8 : 16;
            if (had == bits) return c.Kind == kind && ReferenceEquals(c.Type, target) ? c : new HConv(kind, c.Operand) { Type = target };
        }
        if (BitsOf(e.Type) == bits) return e; // already of that width: the store keeps exactly these bits
        return new HConv(kind, e) { Type = target };
    }

    private static readonly bool NoStructZero = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_ZERO") != null;

    /// <summary>Adjusts an expression to the type a consumer declares, where IL would need an explicit step.</summary>
    private HExpr Coerce(HExpr e, TypeSig target)
    {
        if (e is HConst { Value: int or long } c)
        {
            long v = Convert.ToInt64(c.Value);
            if (IsReference(target)) return v == 0 ? new HConst(null, target) : e;
            if (ReferenceEquals(target, _bool)) return new HConst(v != 0, _bool);
            // A struct all of whose bits are zero is its default value.
            if (v == 0 && IsStructType(target) && !NoStructZero) return new HTypeExpr(HTypeOp.Default, target, null) { Type = target };
            // An integer constant arriving where a float lives is the float's bit pattern (vector lanes are raw bits).
            if (ReferenceEquals(target, _float)) return new HConst(BitConverter.Int32BitsToSingle((int)v), _float);
            if (ReferenceEquals(target, _double)) return new HConst(BitConverter.Int64BitsToDouble(v), _double);
            if (target is PrimitiveSig or { Definition.IsEnum: true })
            {
                // A constant takes the width of where it goes: registers hold "15" as 64 bits, an int parameter does not.
                int bits = BitsOf(target);
                if (bits == 64 && !IsFloat(target)) return new HConst(v, target);
                if (bits is 8 or 16 or 32 && !IsFloat(target)) return new HConst((int)v, target);
            }
            return e;
        }
        // The machine moves floats through general registers as plain bits. A value known only as an integer
        // that arrives where a float lives is that float's bit pattern, and the other way round.
        TypeSig? from = e.Type ?? (e as HLocal)?.Variable.Type;
        if (from == null || e is HConst) return e;
        // A struct that only wraps one object reference, arriving where an object reference is expected: the
        // register holds the reference, so the reference is what is meant.
        for (int depth = 0; depth < 4 && IsReference(target) && IsReferenceWrapper(from) && _p.Layouts.FieldAt(from, 0) is { } wrapped; depth++)
        {
            e = new HField { Object = e, Field = wrapped.Field, DeclaringType = from, Type = wrapped.Type };
            from = wrapped.Type;
        }
        bool toFloat = ReferenceEquals(target, _float), toDouble = ReferenceEquals(target, _double);
        if ((toFloat && (ReferenceEquals(from, _int) || ReferenceEquals(from, _uint))) ||
            (toDouble && (ReferenceEquals(from, _long) || ReferenceEquals(from, _ulong))))
        {
            if (e is HLocal { Variable: var merged } && _phiOfVar.TryGetValue(merged, out Node? phi))
                _floatUses[phi] = (_floatUses.GetValueOrDefault(phi).Count + 1, target);
            return ValueFromBits(e, target, toFloat ? 4 : 8);
        }
        if (ReferenceEquals(from, _float) && (ReferenceEquals(target, _int) || ReferenceEquals(target, _uint)))
        {
            HExpr bits = FloatBits(e);
            return ReferenceEquals(target, _uint) ? new HConv(HConvKind.U4, bits) { Type = _uint } : bits;
        }
        if (ReferenceEquals(from, _double) && (ReferenceEquals(target, _long) || ReferenceEquals(target, _ulong)))
        {
            HExpr bits = FloatBits(e);
            return ReferenceEquals(target, _ulong) ? new HConv(HConvKind.U8, bits) { Type = _ulong } : bits;
        }
        // A number where a struct goes, or a struct where a number goes, with nothing above that told which
        // fields the bits are: no conversion IL has. (A struct that is one number is that number.)
        if (IsStructType(target) && from is PrimitiveSig && !IsStructType(from)) return NumberAsStruct(e, target);
        if (IsStructType(from) && target is PrimitiveSig)
        {
            HExpr scalar = ScalarOf(e, BitsOf(target));
            return IsStructType(scalar.Type) ? StructAsNumber(e, target) : scalar;
        }
        return e;
    }
}
