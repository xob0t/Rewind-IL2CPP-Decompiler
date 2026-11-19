// Modified by xob0t (2026): inlined constructor folding, bits read as float/double. See FORK.md.
using Mono.Cecil;
using Mono.Cecil.Cil;
using Mono.Cecil.Rocks;
using Rewind.Analysis.Hir;
using Rewind.Model;
using Rewind.Runtime;
using MethodBody = Mono.Cecil.Cil.MethodBody;

namespace Rewind.Output;

/// <summary>
/// Writes a recovered method body as IL into the rebuilt assembly. The body is already expressed in managed
/// terms (fields, calls, typed locals, basic blocks), so this is a direct, statement-by-statement translation;
/// turning the result into structured C# is left to an IL decompiler.
///
/// Whatever the recovery could not express stays visible: it becomes a call to a marker method whose string
/// argument describes the missing piece, instead of being dropped or guessed.
/// </summary>
public sealed class BodyEmitter
{
    private readonly AssemblyEmitter _emitter;
    private readonly Il2CppModel _model;
    private readonly Dictionary<ModuleDefinition, Markers> _markers = [];

    /// <summary>
    /// How to make an object without running a constructor (and Type.GetTypeFromHandle, which it needs): the
    /// form an inlined constructor takes when its statements could not be put back into a "new" expression.
    /// </summary>
    public MethodDef? RawAllocator, TypeFromHandle;

    private sealed class Markers
    {
        public MethodDefinition Opaque = null!, Effect = null!, Note = null!;
    }

    public BodyEmitter(AssemblyEmitter emitter, Il2CppModel model)
    {
        _emitter = emitter;
        _model = model;
    }

    /// <summary>Thrown when a construct has no IL form yet; the method then keeps its placeholder body.</summary>
    private sealed class CannotEmit(string why) : Exception(why);

    /// <summary>Replaces the placeholder body of <paramref name="method"/>. Returns null on success, else why not.</summary>
    public string? Emit(MethodDef method, HMethod h)
    {
        MethodDefinition target = _emitter[method];
        MethodBody saved = target.Body;
        try
        {
            var body = new MethodBody(target) { InitLocals = true };
            new Writer(this, method, h, target, body).Run();
            body.OptimizeMacros();
            target.Body = body;
            return null;
        }
        catch (CannotEmit e)
        {
            target.Body = saved;
            return e.Message;
        }
    }

    // ---- marker methods ----------------------------------------------------------------------------------------

    private Markers MarkersFor(ModuleDefinition module)
    {
        if (_markers.TryGetValue(module, out Markers? known)) return known;
        TypeDef? objectType = _model.FindType("System.Object");
        TypeDef? exceptionType = _model.FindType("System.NotSupportedException") ?? _model.FindType("System.Exception");
        MethodDef? exceptionCtor = exceptionType?.Methods.FirstOrDefault(m =>
            m.Name == ".ctor" && m.Parameters.Length == 1 && m.Parameters[0].Type is PrimitiveSig { Element: Il2CppTypeEnum.String });
        if (objectType == null || exceptionCtor == null) throw new CannotEmit("the class library lacks the types the markers need");

        TypeReference voidType = _emitter.Import(module, _model.Sigs.Primitive(Il2CppTypeEnum.Void));
        TypeReference stringType = _emitter.Import(module, _model.Sigs.Primitive(Il2CppTypeEnum.String));
        var holder = new TypeDefinition("", "__Rewind",
            TypeAttributes.NotPublic | TypeAttributes.Abstract | TypeAttributes.Sealed | TypeAttributes.BeforeFieldInit,
            _emitter.Import(module, objectType));
        module.Types.Add(holder);

        MethodDefinition Define(string name, bool generic, bool throws)
        {
            var m = new MethodDefinition(name, MethodAttributes.Assembly | MethodAttributes.Static | MethodAttributes.HideBySig, voidType);
            if (generic)
            {
                var t = new GenericParameter("T", m);
                m.GenericParameters.Add(t);
                m.ReturnType = t;
            }
            m.Parameters.Add(new ParameterDefinition("what", ParameterAttributes.None, stringType));
            m.Body = new MethodBody(m);
            ILProcessor il = m.Body.GetILProcessor();
            if (throws)
            {
                il.Emit(OpCodes.Ldarg_0);
                il.Emit(OpCodes.Newobj, _emitter.ImportMethod(module, exceptionCtor));
                il.Emit(OpCodes.Throw);
            }
            else il.Emit(OpCodes.Ret);
            holder.Methods.Add(m);
            return m;
        }

        var markers = new Markers
        {
            Opaque = Define("Opaque", generic: true, throws: true),
            Effect = Define("Effect", generic: false, throws: true),
            Note = Define("Note", generic: false, throws: false),
        };
        _markers[module] = markers;
        return markers;
    }

    // ---- one method --------------------------------------------------------------------------------------------

    private sealed class Writer
    {
        private readonly BodyEmitter _owner;
        private readonly AssemblyEmitter _e;
        private readonly Il2CppModel _model;
        private readonly MethodDef _method;
        private readonly HMethod _h;
        private readonly ModuleDefinition _module;
        private readonly MethodBody _body;
        private readonly ILProcessor _il;
        private readonly Dictionary<HVar, VariableDefinition> _locals = [];
        private readonly Dictionary<HBlock, Instruction> _labels = [];
        /// <summary>The try region scope of the block being written (see HBlock.Scope).</summary>
        private int _scope = -1;
        /// <summary>Inside try regions a return stores its value and leaves to this shared epilogue.</summary>
        private Instruction? _epilogue;
        private VariableDefinition? _returnLocal;

        /// <summary>One step of the layout: a block, or the start of a try region, of its handler, or the end of the handler.</summary>
        private readonly record struct Item(HBlock? Block, int Mark, HTryRegion? Region);

        public Writer(BodyEmitter owner, MethodDef method, HMethod h, MethodDefinition target, MethodBody body)
        {
            _owner = owner;
            _e = owner._emitter;
            _model = owner._model;
            _method = method;
            _h = h;
            _module = target.Module;
            _body = body;
            _il = body.GetILProcessor();
        }

        private TypeReference Ref(TypeSig? sig) => _e.Import(_module, sig ?? _model.Sigs.Primitive(Il2CppTypeEnum.I4));

        /// <summary>A type parameter of the method being written, or of its class: one it can name. Null for anything else.</summary>
        private GenericParamSig? Own(TypeSig? t) =>
            t is GenericParamSig p && (Array.IndexOf(_method.DeclaringType.GenericParameters, p.Parameter) >= 0 || Array.IndexOf(_method.GenericParameters, p.Parameter) >= 0) ? p : null;

        private static bool OpenOnlyIn(TypeSig? t, MethodDef method) => t switch
        {
            null => true,
            GenericParamSig p => Array.IndexOf(method.DeclaringType.GenericParameters, p.Parameter) >= 0 || Array.IndexOf(method.GenericParameters, p.Parameter) >= 0,
            GenericInstSig g => g.Arguments.All(a => OpenOnlyIn(a, method)),
            SzArraySig s => OpenOnlyIn(s.ElementType, method),
            ArraySig a => OpenOnlyIn(a.ElementType, method),
            PointerSig p => OpenOnlyIn(p.ElementType, method),
            ByRefSig r => OpenOnlyIn(r.ElementType, method),
            _ => !t.ContainsGenericParameter,
        };

        public void Run()
        {
            foreach (HVar v in _h.Locals)
            {
                // A type parameter of the method's own, or of its class, is a type like any other here.
                if (v.Type.ContainsGenericParameter && !OpenOnlyIn(v.Type, _method)) throw new CannotEmit("local of an open generic type");
                var local = new VariableDefinition(Ref(v.Type));
                _body.Variables.Add(local);
                _locals[v] = local;
            }
            foreach (HBlock b in _h.Blocks) _labels[b] = Instruction.Create(OpCodes.Nop);

            if (_h.Problems.Count != 0)
            {
                string note = $"{_h.Problems.Count} part(s) of this method were not recovered: " + string.Join("; ", _h.Problems.Distinct().Take(4));
                _il.Emit(OpCodes.Ldstr, note);
                _il.Emit(OpCodes.Call, _owner.MarkersFor(_module).Note);
            }

            if (_h.TryRegions.Count != 0)
            {
                _epilogue = Instruction.Create(OpCodes.Nop);
                if (!_method.ReturnType.IsVoid)
                {
                    _returnLocal = new VariableDefinition(Ref(_method.ReturnType));
                    _body.Variables.Add(_returnLocal);
                }
            }

            List<Item> items = Layout();
            var tryStart = new Dictionary<HTryRegion, Instruction>();
            var handlerStart = new Dictionary<HTryRegion, Instruction>();
            var handlerEnd = new Dictionary<HTryRegion, int>();
            for (int i = 0; i < items.Count; i++)
            {
                Item item = items[i];
                if (item.Block is not { } block)
                {
                    HTryRegion region = item.Region!;
                    switch (item.Mark)
                    {
                        case 0:
                            tryStart[region] = _labels[region.Entry];
                            break;
                        case 1:
                        {
                            if (region.Finally)
                            {
                                // A finally handler is entered with nothing on the stack.
                                Instruction enter = Instruction.Create(OpCodes.Nop);
                                _il.Append(enter);
                                handlerStart[region] = enter;
                                break;
                            }
                            // The handler starts with the caught exception on the stack.
                            Instruction store = Instruction.Create(OpCodes.Stloc, _locals[region.Exception]);
                            _il.Append(store);
                            handlerStart[region] = store;
                            break;
                        }
                        default:
                            handlerEnd[region] = _body.Instructions.Count;
                            break;
                    }
                    continue;
                }
                _scope = block.Scope;
                _il.Append(_labels[block]);
                // Control may fall into the next block, and into the start of a try region, but never out of one.
                HBlock? next = i + 1 < items.Count ? items[i + 1].Block : null;
                if (next == null && i + 2 < items.Count && items[i + 1].Mark == 0 && items[i + 2].Block is { } entry &&
                    ReferenceEquals(entry, items[i + 1].Region!.Entry))
                    next = entry;
                bool terminated = false;
                foreach (HStmt s in block.Statements) terminated = Statement(s, next);
                if (!terminated)
                {
                    // A block that simply ends continues nowhere defined; make that explicit and verifiable.
                    if (next == null || block.Statements.Count == 0 || block.Statements[^1] is not HJump)
                    {
                        _il.Emit(OpCodes.Ldstr, "control reaches the end of a block");
                        _il.Emit(OpCodes.Call, _owner.MarkersFor(_module).Effect);
                        EmitDefaultReturn();
                    }
                }
            }

            if (_epilogue != null)
            {
                _il.Append(_epilogue);
                if (_returnLocal != null) _il.Emit(OpCodes.Ldloc, _returnLocal);
                _il.Emit(OpCodes.Ret);
                // Nested regions come before the regions around them.
                foreach (HTryRegion region in _h.TryRegions.Values.OrderByDescending(r => Depth(r.Outer)))
                {
                    if (!tryStart.ContainsKey(region) || !handlerStart.ContainsKey(region) || !handlerEnd.ContainsKey(region))
                        throw new CannotEmit("try region not laid out");
                    var clause = new ExceptionHandler(region.Finally ? ExceptionHandlerType.Finally : ExceptionHandlerType.Catch)
                    {
                        TryStart = tryStart[region],
                        TryEnd = handlerStart[region],
                        HandlerStart = handlerStart[region],
                        HandlerEnd = _body.Instructions[handlerEnd[region]],
                    };
                    if (!region.Finally) clause.CatchType = Ref(region.Exception.Type);
                    _body.ExceptionHandlers.Add(clause);
                }
            }
        }

        private int Depth(int scope)
        {
            int depth = 0;
            for (int s = scope; s >= 0 && depth < 64; s = _h.OuterOf(s)) depth++;
            return depth;
        }

        /// <summary>
        /// The order blocks are written in. Without try regions it is the method's own. With them, each region is
        /// written in one piece right after the block that enters it - its protected code from its first block,
        /// then its handler - as IL requires.
        /// </summary>
        private List<Item> Layout()
        {
            var items = new List<Item>();
            if (_h.TryRegions.Count == 0)
            {
                foreach (HBlock b in _h.Blocks) items.Add(new Item(b, -1, null));
                return items;
            }
            var placed = new HashSet<HBlock>();
            var placedRegions = new HashSet<HTryRegion>();
            void Scope(int scope, HBlock first)
            {
                foreach (HBlock b in _h.Blocks.Where(b => ReferenceEquals(b, first)).Concat(_h.Blocks.Where(b => !ReferenceEquals(b, first))))
                {
                    if (b.Scope != scope || !placed.Add(b)) continue;
                    items.Add(new Item(b, -1, null));
                    if (b.Statements.Count == 0 || b.Statements[^1] is not HJump jump) continue;
                    foreach (HTryRegion r in _h.TryRegions.Values)
                        if (r.Outer == scope && ReferenceEquals(r.Entry, jump.Target) && placedRegions.Add(r))
                        {
                            items.Add(new Item(null, 0, r));
                            Scope(2 * r.Index, r.Entry);
                            items.Add(new Item(null, 1, r));
                            Scope(2 * r.Index + 1, r.HandlerEntry);
                            items.Add(new Item(null, 2, r));
                        }
                }
            }
            Scope(-1, _h.Blocks[0]);
            if (placed.Count != _h.Blocks.Count) throw new CannotEmit("try regions could not be laid out");
            return items;
        }

        /// <summary>True when going from the current block to <paramref name="target"/> leaves a try region or handler.</summary>
        private bool Leaves(HBlock target)
        {
            if (target.Scope == _scope) return false;
            foreach (HTryRegion r in _h.TryRegions.Values)
                if (ReferenceEquals(r.Entry, target) && r.Outer == _scope)
                    return false; // entering a region at its start
            return true;
        }

        /// <summary>Continues at <paramref name="target"/>: falls through, branches, or leaves the region it is in.</summary>
        private void Transfer(HBlock target, HBlock? next)
        {
            if (Leaves(target)) _il.Emit(OpCodes.Leave, _labels[target]);
            else if (!ReferenceEquals(target, next)) _il.Emit(OpCodes.Br, _labels[target]);
        }

        private bool InHandler()
        {
            for (int s = _scope, guard = 0; s >= 0 && guard < 64; guard++, s = _h.OuterOf(s))
                if ((s & 1) == 1 && !(_h.TryRegions.TryGetValue(s >> 1, out HTryRegion? region) && region.Finally)) return true;
            return false;
        }

        /// <summary>Returns the value on the stack (if any): directly, or through the epilogue from inside a try region.</summary>
        private void EmitReturn()
        {
            if (_scope < 0 || _epilogue == null)
            {
                _il.Emit(OpCodes.Ret);
                return;
            }
            if (_returnLocal != null) _il.Emit(OpCodes.Stloc, _returnLocal);
            _il.Emit(OpCodes.Leave, _epilogue);
        }

        private void EmitDefaultReturn()
        {
            if (!_method.ReturnType.IsVoid) Default(_method.ReturnType);
            EmitReturn();
        }

        // ---- statements ----------------------------------------------------------------------------------------

        /// <summary>Emits one statement; returns true when control cannot continue past it.</summary>
        private bool Statement(HStmt s, HBlock? next)
        {
            switch (s)
            {
                case HAssign a:
                    Assign(a.Target, a.Value);
                    return false;
                case HEval e:
                    if (e.Expression is HOpaque opaque)
                    {
                        _il.Emit(OpCodes.Ldstr, opaque.Remark ? opaque.Problem ?? Describe(opaque) : Describe(opaque));
                        _il.Emit(OpCodes.Call, opaque.Remark ? _owner.MarkersFor(_module).Note : _owner.MarkersFor(_module).Effect);
                        return false;
                    }
                    Value(e.Expression);
                    if (!IsVoid(e.Expression)) _il.Emit(OpCodes.Pop);
                    return false;
                case HReturn r:
                    if (r.Value != null && !_method.ReturnType.IsVoid) ValueAs(r.Value, _method.ReturnType);
                    else if (!_method.ReturnType.IsVoid) Default(_method.ReturnType);
                    EmitReturn();
                    return true;
                case HThrow t:
                    if (t.Exception == null)
                    {
                        if (!InHandler()) throw new CannotEmit("rethrow outside a catch clause");
                        _il.Emit(OpCodes.Rethrow);
                    }
                    else if (t.Exception is HOpaque marker)
                    {
                        _il.Emit(OpCodes.Ldstr, Describe(marker));
                        _il.Emit(OpCodes.Call, _owner.MarkersFor(_module).Effect);
                        EmitDefaultReturn();
                    }
                    else
                    {
                        Value(t.Exception);
                        _il.Emit(OpCodes.Throw);
                    }
                    return true;
                case HEndFinally:
                    _il.Emit(OpCodes.Endfinally);
                    return true;
                case HJump j:
                    Transfer(j.Target, next);
                    return true;
                case HBranch b:
                    Value(b.Condition);
                    if (!Leaves(b.WhenTrue)) _il.Emit(OpCodes.Brtrue, _labels[b.WhenTrue]);
                    else
                    {
                        Instruction otherwise = Instruction.Create(OpCodes.Nop);
                        _il.Emit(OpCodes.Brfalse, otherwise);
                        _il.Emit(OpCodes.Leave, _labels[b.WhenTrue]);
                        _il.Append(otherwise);
                    }
                    Transfer(b.WhenFalse, next);
                    return true;
                case HSwitch sw:
                {
                    Value(sw.Value);
                    if (Bits(sw.Value.Type) == 64) _il.Emit(OpCodes.Conv_U4);
                    // Cases that leave the region go through a stub that does.
                    var stubs = new List<(Instruction Stub, HBlock Target)>();
                    Instruction[] labels = sw.Targets.Select(t =>
                    {
                        if (!Leaves(t)) return _labels[t];
                        Instruction stub = Instruction.Create(OpCodes.Leave, _labels[t]);
                        stubs.Add((stub, t));
                        return stub;
                    }).ToArray();
                    _il.Emit(OpCodes.Switch, labels);
                    Transfer(sw.Default, null);
                    foreach (var (stub, _) in stubs) _il.Append(stub);
                    return true;
                }
                default:
                    throw new CannotEmit("statement " + s.GetType().Name);
            }
        }

        private void Assign(HExpr target, HExpr value)
        {
            switch (target)
            {
                case HLocal l:
                    ValueAs(value, l.Variable.Type);
                    _il.Emit(OpCodes.Stloc, _locals[l.Variable]);
                    return;
                case HArg a when a.Index >= 0:
                    ValueAs(value, ParameterType(a.Index));
                    _il.Emit(OpCodes.Starg, _body.Method.Parameters[a.Index]);
                    return;
                case HField f:
                {
                    FieldReference field = _e.ImportField(_module, f.Field, f.DeclaringType);
                    if (f.Object == null)
                    {
                        ValueAs(value, f.Type ?? f.Field.Type);
                        _il.Emit(OpCodes.Stsfld, field);
                        return;
                    }
                    Owner(f.Object);
                    ValueAs(value, f.Type ?? f.Field.Type);
                    _il.Emit(OpCodes.Stfld, field);
                    return;
                }
                case HElement el:
                    Value(el.Array);
                    Index(el.Index);
                    ValueAs(value, el.Type);
                    _il.Emit(OpCodes.Stelem_Any, Ref(el.Type));
                    return;
                case HDeref d:
                    Value(d.Pointer);
                    ValueAs(value, d.Type);
                    _il.Emit(OpCodes.Stobj, Ref(d.Type));
                    return;
                case HArg a when a.Index < 0 && a.Type is { IsValueType: true }:
                    // "this = value" in a struct method.
                    _il.Emit(OpCodes.Ldarg_0);
                    ValueAs(value, a.Type);
                    _il.Emit(OpCodes.Stobj, Ref(a.Type));
                    return;
                default:
                    throw new CannotEmit("assignment to " + target.GetType().Name);
            }
        }

        // ---- expressions ---------------------------------------------------------------------------------------

        private static bool IsVoid(HExpr e) => e switch
        {
            HCall c => c.Type == null ? c.Method.ReturnType.IsVoid : c.Type.IsVoid,
            _ => false,
        };

        private static bool IsValueType(TypeSig? t) => t is { IsValueType: true } and not PrimitiveSig && t.Definition is not { IsEnum: true };

        private static int Bits(TypeSig? t) => t switch
        {
            PrimitiveSig p => p.Element switch
            {
                Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.R8 or Il2CppTypeEnum.I or Il2CppTypeEnum.U => 64,
                Il2CppTypeEnum.Void => 0,
                _ => 32,
            },
            { Definition: { IsEnum: true, EnumUnderlyingType: { } u } } => Bits(u),
            PointerSig or ByRefSig => 64,
            _ => 0,
        };

        private static bool IsFloat(TypeSig? t) => t is PrimitiveSig { Element: Il2CppTypeEnum.R4 or Il2CppTypeEnum.R8 };

        private static bool IsUnsigned(TypeSig? t) => t is PrimitiveSig
        {
            Element: Il2CppTypeEnum.U1 or Il2CppTypeEnum.U2 or Il2CppTypeEnum.U4 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.U or Il2CppTypeEnum.Char
        } or PointerSig;

        private TypeSig ParameterType(int index) =>
            index >= 0 && index < _method.Parameters.Length ? _method.Parameters[index].Type : _model.Sigs.Primitive(Il2CppTypeEnum.I4);

        private string Describe(HExpr e) => HirPrinter.Print(e, _h);

        /// <summary>The integer width an expression has on the IL stack: 64 for long and native int, else 32.</summary>
        private static int StackBits(HExpr e) => Bits(e.Type) == 64 ? 64 : 32;

        /// <summary>Pushes a value and adapts integer width to what the destination holds.</summary>
        private void ValueAs(HExpr e, TypeSig? target)
        {
            // "null" given to a T is T's nothing: null only where T is a class.
            if (Own(target) != null && e is HConst { Value: null })
            {
                Default(target);
                return;
            }
            Value(e);
            // The address of a local handed over as an unmanaged pointer: "&local" (ldloca, conv.u).
            if (target is PointerSig && (e is HAddressOf || e.Type is ByRefSig))
            {
                _il.Emit(OpCodes.Conv_U);
                return;
            }
            // A T handed on as something else - an object, the class or interface it is declared to be - is
            // boxed, which leaves a reference what it is; something else handed on as a T is taken out likewise.
            if (Own(e.Type) is { } from)
            {
                if (target != null && !ReferenceEquals(target, from) && target is not (GenericParamSig or ByRefSig or PointerSig) && !target.IsValueType)
                    _il.Emit(OpCodes.Box, Ref(from));
                return;
            }
            if (Own(target) is { } to)
            {
                if (e.Type != null && e.Type is not (ByRefSig or PointerSig) && !e.Type.IsValueType) _il.Emit(OpCodes.Unbox_Any, Ref(to));
                return;
            }
            if (target == null || IsFloat(target) || IsFloat(e.Type)) return;
            int want = Bits(target), have = Bits(e.Type);
            if (want == 64 && have == 32 && target is PrimitiveSig or { Definition.IsEnum: true })
                _il.Emit(IsUnsigned(e.Type) ? OpCodes.Conv_U8 : OpCodes.Conv_I8);
            else if (want == 32 && have == 64 && e.Type is PrimitiveSig)
                _il.Emit(OpCodes.Conv_I4);
        }

        private void Index(HExpr e)
        {
            // A constant is the 32-bit number the instruction takes, whatever width the machine code had it in:
            // "new T[5] { ... }" is known by it.
            long? constant = e is HConst { Value: var value } ? value switch
            {
                long n => n,
                ulong n when n <= int.MaxValue => (long)n,
                _ => null,
            } : null;
            if (!WideIndexConstants && constant is >= int.MinValue and <= int.MaxValue)
            {
                _il.Emit(OpCodes.Ldc_I4, (int)constant.Value);
                return;
            }
            Value(e);
            if (Bits(e.Type) == 64) _il.Emit(OpCodes.Conv_I4);
        }

        private static readonly bool WideIndexConstants = Environment.GetEnvironmentVariable("REWIND_WIDE_INDEX_CONSTANTS") != null;

        /// <summary>
        /// Pushes what a field access or instance call needs as its receiver: the reference for classes, the
        /// address for structs.
        /// </summary>
        private void Owner(HExpr e)
        {
            if (IsValueType(e.Type) && IsAddressable(e)) Address(e);
            else Value(e);
            // A field of a T is a field of the class T is declared to derive from: reached through the box.
            if (Own(e.Type) is { } open) _il.Emit(OpCodes.Box, Ref(open));
        }

        private static bool IsAddressable(HExpr e) => e is HLocal or HArg or HField or HElement or HDeref;

        /// <summary>Pushes the address of a location.</summary>
        private void Address(HExpr location)
        {
            switch (location)
            {
                case HLocal l:
                    _il.Emit(OpCodes.Ldloca, _locals[l.Variable]);
                    return;
                case HArg a when a.Index < 0:
                    _il.Emit(OpCodes.Ldarg_0); // "this" of a struct method is already its address
                    return;
                case HArg a:
                    if (a.Index >= _body.Method.Parameters.Count) throw new CannotEmit("argument index out of range");
                    _il.Emit(OpCodes.Ldarga, _body.Method.Parameters[a.Index]);
                    return;
                case HField f:
                {
                    FieldReference field = _e.ImportField(_module, f.Field, f.DeclaringType);
                    if (f.Object == null)
                    {
                        _il.Emit(OpCodes.Ldsflda, field);
                        return;
                    }
                    Owner(f.Object);
                    _il.Emit(OpCodes.Ldflda, field);
                    return;
                }
                case HElement el:
                    Value(el.Array);
                    Index(el.Index);
                    _il.Emit(OpCodes.Ldelema, Ref(el.Type));
                    return;
                case HDeref d:
                    Value(d.Pointer);
                    return;
                default:
                {
                    // A value without a home: give it one.
                    TypeSig type = location.Type ?? throw new CannotEmit("address of an untyped value");
                    var temp = new VariableDefinition(Ref(type));
                    _body.Variables.Add(temp);
                    Value(location);
                    _il.Emit(OpCodes.Stloc, temp);
                    _il.Emit(OpCodes.Ldloca, temp);
                    return;
                }
            }
        }

        private void Default(TypeSig type)
        {
            if (IsValueType(type) || type is GenericParamSig)
            {
                var temp = new VariableDefinition(Ref(type));
                _body.Variables.Add(temp);
                _il.Emit(OpCodes.Ldloca, temp);
                _il.Emit(OpCodes.Initobj, Ref(type));
                _il.Emit(OpCodes.Ldloc, temp);
                return;
            }
            if (type is PrimitiveSig p)
            {
                switch (p.Element)
                {
                    case Il2CppTypeEnum.R4: _il.Emit(OpCodes.Ldc_R4, 0f); return;
                    case Il2CppTypeEnum.R8: _il.Emit(OpCodes.Ldc_R8, 0d); return;
                    case Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8: _il.Emit(OpCodes.Ldc_I8, 0L); return;
                    case Il2CppTypeEnum.I or Il2CppTypeEnum.U: _il.Emit(OpCodes.Ldc_I4_0); _il.Emit(OpCodes.Conv_I); return;
                    case Il2CppTypeEnum.String or Il2CppTypeEnum.Object: _il.Emit(OpCodes.Ldnull); return;
                    default: _il.Emit(OpCodes.Ldc_I4_0); return;
                }
            }
            if (type.Definition is { IsEnum: true }) { if (Bits(type) == 64) _il.Emit(OpCodes.Ldc_I8, 0L); else _il.Emit(OpCodes.Ldc_I4_0); return; }
            if (type is PointerSig or ByRefSig) { _il.Emit(OpCodes.Ldc_I4_0); _il.Emit(OpCodes.Conv_U); return; }
            _il.Emit(OpCodes.Ldnull);
        }

        private void Constant(HConst c)
        {
            switch (c.Value)
            {
                case null: _il.Emit(OpCodes.Ldnull); return;
                case string s: _il.Emit(OpCodes.Ldstr, s); return;
                case bool b: _il.Emit(b ? OpCodes.Ldc_I4_1 : OpCodes.Ldc_I4_0); return;
                case float f: _il.Emit(OpCodes.Ldc_R4, f); return;
                case double d: _il.Emit(OpCodes.Ldc_R8, d); return;
                case long l:
                    if (c.Type is PrimitiveSig { Element: Il2CppTypeEnum.I or Il2CppTypeEnum.U } or PointerSig or ByRefSig)
                    {
                        _il.Emit(OpCodes.Ldc_I8, l);
                        _il.Emit(OpCodes.Conv_I);
                    }
                    else _il.Emit(OpCodes.Ldc_I8, l);
                    return;
                case int i: _il.Emit(OpCodes.Ldc_I4, i); return;
                default: throw new CannotEmit("constant of type " + c.Value.GetType().Name);
            }
        }

        private void Value(HExpr e)
        {
            switch (e)
            {
                case HConst c:
                    Constant(c);
                    return;
                case HLocal l:
                    _il.Emit(OpCodes.Ldloc, _locals[l.Variable]);
                    return;
                case HArg a when a.Index < 0:
                    _il.Emit(OpCodes.Ldarg_0);
                    if (_method.DeclaringType.IsValueType) _il.Emit(OpCodes.Ldobj, Ref(_method.DeclaringType.Sig));
                    return;
                case HArg a:
                    if (a.Index >= _body.Method.Parameters.Count) throw new CannotEmit("argument index out of range");
                    _il.Emit(OpCodes.Ldarg, _body.Method.Parameters[a.Index]);
                    return;
                case HField f:
                {
                    FieldReference field = _e.ImportField(_module, f.Field, f.DeclaringType);
                    if (f.Object == null)
                    {
                        _il.Emit(OpCodes.Ldsfld, field);
                        return;
                    }
                    Owner(f.Object);
                    _il.Emit(OpCodes.Ldfld, field);
                    return;
                }
                case HElement el:
                    Value(el.Array);
                    Index(el.Index);
                    _il.Emit(OpCodes.Ldelem_Any, Ref(el.Type));
                    return;
                case HArrayLength len:
                    Value(len.Array);
                    _il.Emit(OpCodes.Ldlen);
                    _il.Emit(OpCodes.Conv_I4);
                    return;
                case HAddressOf addr:
                    Address(addr.Target);
                    return;
                case HDeref d when d.IsBitCast(out HExpr bits) && bits is not (HLocal or HArg):
                {
                    // Bits read as another type: from a local of their own (in C# the address of a local needs
                    // no pinning, that of a field or an element would).
                    var temp = new VariableDefinition(Ref(bits.Type));
                    _body.Variables.Add(temp);
                    Value(bits);
                    _il.Emit(OpCodes.Stloc, temp);
                    _il.Emit(OpCodes.Ldloca, temp);
                    _il.Emit(OpCodes.Ldobj, Ref(d.Type));
                    return;
                }
                case HDeref d:
                    Value(d.Pointer);
                    _il.Emit(OpCodes.Ldobj, Ref(d.Type));
                    return;
                case HUnary u:
                    Value(u.Operand);
                    switch (u.Op)
                    {
                        case HUnaryOp.Neg: _il.Emit(OpCodes.Neg); break;
                        case HUnaryOp.Not: _il.Emit(OpCodes.Not); break;
                        default:
                            _il.Emit(OpCodes.Ldc_I4_0);
                            _il.Emit(OpCodes.Ceq);
                            break;
                    }
                    return;
                case HBinary b:
                    Binary(b);
                    return;
                case HCompare c:
                    Compare(c);
                    return;
                case HConv c:
                    Value(c.Operand);
                    _il.Emit(c.Kind switch
                    {
                        HConvKind.I1 => OpCodes.Conv_I1, HConvKind.U1 => OpCodes.Conv_U1, HConvKind.I2 => OpCodes.Conv_I2,
                        HConvKind.U2 => OpCodes.Conv_U2, HConvKind.I4 => OpCodes.Conv_I4, HConvKind.U4 => OpCodes.Conv_U4,
                        HConvKind.I8 => OpCodes.Conv_I8, HConvKind.U8 => OpCodes.Conv_U8, HConvKind.R4 => OpCodes.Conv_R4,
                        HConvKind.R8 => OpCodes.Conv_R8, HConvKind.RUn => OpCodes.Conv_R_Un, HConvKind.I => OpCodes.Conv_I,
                        HConvKind.U => OpCodes.Conv_U, HConvKind.OvfI1 => OpCodes.Conv_Ovf_I1, HConvKind.OvfU1 => OpCodes.Conv_Ovf_U1,
                        HConvKind.OvfI2 => OpCodes.Conv_Ovf_I2, HConvKind.OvfU2 => OpCodes.Conv_Ovf_U2, HConvKind.OvfI4 => OpCodes.Conv_Ovf_I4,
                        HConvKind.OvfU4 => OpCodes.Conv_Ovf_U4, HConvKind.OvfI8 => OpCodes.Conv_Ovf_I8, _ => OpCodes.Conv_Ovf_U8,
                    });
                    return;
                case HCall call:
                    Call(call);
                    return;
                case HNewObject n:
                {
                    MethodReference ctor = _e.ImportMethod(_module, n.Constructor, n.DeclaringType);
                    Arguments(n.Constructor, n.DeclaringType, n.Arguments);
                    _il.Emit(OpCodes.Newobj, ctor);
                    return;
                }
                case HNewArray na:
                    Index(na.Length);
                    _il.Emit(OpCodes.Newarr, Ref(na.ElementType));
                    return;
                case HCachedDelegate cached:
                {
                    // The compiler's own sequence, which is what a C# decompiler knows a lambda by.
                    FieldReference cache = _e.ImportField(_module, cached.Cache.Field, cached.Cache.DeclaringType);
                    Instruction have = Instruction.Create(OpCodes.Nop);
                    _il.Emit(OpCodes.Ldsfld, cache);
                    _il.Emit(OpCodes.Dup);
                    _il.Emit(OpCodes.Brtrue, have);
                    _il.Emit(OpCodes.Pop);
                    Value(cached.Creation);
                    _il.Emit(OpCodes.Dup);
                    _il.Emit(OpCodes.Stsfld, cache);
                    _il.Append(have);
                    return;
                }
                case HTypeExpr t:
                    TypeOperation(t);
                    return;
                case HSelect s:
                {
                    Instruction otherwise = Instruction.Create(OpCodes.Nop), end = Instruction.Create(OpCodes.Nop);
                    Value(s.Condition);
                    _il.Emit(OpCodes.Brfalse, otherwise);
                    ValueAs(s.WhenTrue, s.Type);
                    _il.Emit(OpCodes.Br, end);
                    _il.Append(otherwise);
                    ValueAs(s.WhenFalse, s.Type);
                    _il.Append(end);
                    return;
                }
                case HMethodPointer p:
                {
                    MethodReference target = _e.ImportMethod(_module, p.Method, p.DeclaringType);
                    if (p.VirtualOn != null)
                    {
                        Value(p.VirtualOn);
                        _il.Emit(OpCodes.Ldvirtftn, Instantiate(target, p.MethodArguments));
                    }
                    else _il.Emit(OpCodes.Ldftn, Instantiate(target, p.MethodArguments));
                    return;
                }
                case HMemberToken t:
                    if (t.Method != null) _il.Emit(OpCodes.Ldtoken, Instantiate(_e.ImportMethod(_module, t.Method, t.DeclaringType), t.MethodArguments));
                    else _il.Emit(OpCodes.Ldtoken, _e.ImportField(_module, t.Field!, t.DeclaringType));
                    return;
                case HOpaque o:
                {
                    TypeSig type = o.Type is { IsVoid: false } known ? known : _model.Sigs.Primitive(Il2CppTypeEnum.I4);
                    var marker = new GenericInstanceMethod(_owner.MarkersFor(_module).Opaque);
                    marker.GenericArguments.Add(Ref(type));
                    _il.Emit(OpCodes.Ldstr, Describe(o));
                    _il.Emit(OpCodes.Call, marker);
                    return;
                }
                default:
                    throw new CannotEmit("expression " + e.GetType().Name);
            }
        }

        private void Binary(HBinary b)
        {
            bool shift = b.Op is HBinaryOp.Shl or HBinaryOp.Shr or HBinaryOp.ShrUn;
            bool wide = StackBits(b.Left) == 64 || (!shift && StackBits(b.Right) == 64);
            Value(b.Left);
            if (wide && StackBits(b.Left) == 32 && !IsFloat(b.Left.Type)) _il.Emit(IsUnsigned(b.Left.Type) ? OpCodes.Conv_U8 : OpCodes.Conv_I8);
            Value(b.Right);
            if (shift)
            {
                if (StackBits(b.Right) == 64) _il.Emit(OpCodes.Conv_I4);
                // IL leaves shifts by the width or more undefined; C# (and the CPU) use the low bits of the count.
                if (b.Right is not HConst)
                {
                    _il.Emit(OpCodes.Ldc_I4, wide ? 63 : 31);
                    _il.Emit(OpCodes.And);
                }
            }
            else if (wide && StackBits(b.Right) == 32 && !IsFloat(b.Right.Type))
                _il.Emit(IsUnsigned(b.Right.Type) ? OpCodes.Conv_U8 : OpCodes.Conv_I8);

            _il.Emit(b.Op switch
            {
                HBinaryOp.Add => OpCodes.Add, HBinaryOp.Sub => OpCodes.Sub, HBinaryOp.Mul => OpCodes.Mul, HBinaryOp.Div => OpCodes.Div,
                HBinaryOp.DivUn => OpCodes.Div_Un, HBinaryOp.Rem => OpCodes.Rem, HBinaryOp.RemUn => OpCodes.Rem_Un, HBinaryOp.And => OpCodes.And,
                HBinaryOp.Or => OpCodes.Or, HBinaryOp.Xor => OpCodes.Xor, HBinaryOp.Shl => OpCodes.Shl, HBinaryOp.Shr => OpCodes.Shr,
                HBinaryOp.ShrUn => OpCodes.Shr_Un, HBinaryOp.AddOvf => OpCodes.Add_Ovf, HBinaryOp.AddOvfUn => OpCodes.Add_Ovf_Un,
                HBinaryOp.SubOvf => OpCodes.Sub_Ovf, HBinaryOp.SubOvfUn => OpCodes.Sub_Ovf_Un, HBinaryOp.MulOvf => OpCodes.Mul_Ovf,
                _ => OpCodes.Mul_Ovf_Un,
            });
        }

        private void Compare(HCompare c)
        {
            bool isFloat = IsFloat(c.Left.Type) || IsFloat(c.Right.Type);
            // ("x as long" is an object or null, not a number of 64 bits: nothing to widen the other side to.)
            bool tested = c.Left is HTypeExpr { Op: HTypeOp.IsInst } || c.Right is HTypeExpr { Op: HTypeOp.IsInst };
            bool wide = !isFloat && !tested && (StackBits(c.Left) == 64 || StackBits(c.Right) == 64);
            Value(c.Left);
            if (wide && StackBits(c.Left) == 32 && c.Left.Type is PrimitiveSig) _il.Emit(IsUnsigned(c.Left.Type) ? OpCodes.Conv_U8 : OpCodes.Conv_I8);
            // A T is compared (with null, with another reference) as the object it is when boxed.
            if (Own(c.Left.Type) is { } openLeft) _il.Emit(OpCodes.Box, Ref(openLeft));
            Value(c.Right);
            if (wide && StackBits(c.Right) == 32 && c.Right.Type is PrimitiveSig) _il.Emit(IsUnsigned(c.Right.Type) ? OpCodes.Conv_U8 : OpCodes.Conv_I8);
            if (Own(c.Right.Type) is { } openRight) _il.Emit(OpCodes.Box, Ref(openRight));

            void Not()
            {
                _il.Emit(OpCodes.Ldc_I4_0);
                _il.Emit(OpCodes.Ceq);
            }
            bool unsigned = IsUnsigned(c.Left.Type) && (IsUnsigned(c.Right.Type) || c.Right is HConst);
            switch (c.Op)
            {
                case HCompareOp.Eq: _il.Emit(OpCodes.Ceq); break;
                case HCompareOp.Ne: _il.Emit(OpCodes.Ceq); Not(); break;
                case HCompareOp.Lt: _il.Emit(unsigned ? OpCodes.Clt_Un : OpCodes.Clt); break;
                case HCompareOp.Gt: _il.Emit(unsigned ? OpCodes.Cgt_Un : OpCodes.Cgt); break;
                case HCompareOp.LtUn: _il.Emit(OpCodes.Clt_Un); break;
                case HCompareOp.GtUn: _il.Emit(OpCodes.Cgt_Un); break;
                // "a <= b" is "not (a > b)"; for floats the inner test must also be true for NaN so that the
                // whole comparison is false for NaN, which is what the unordered form does.
                case HCompareOp.Le: _il.Emit(isFloat || unsigned ? OpCodes.Cgt_Un : OpCodes.Cgt); Not(); break;
                case HCompareOp.Ge: _il.Emit(isFloat || unsigned ? OpCodes.Clt_Un : OpCodes.Clt); Not(); break;
                case HCompareOp.LeUn: _il.Emit(OpCodes.Cgt_Un); Not(); break;
                default: _il.Emit(OpCodes.Clt_Un); Not(); break;
            }
        }

        private MethodReference Instantiate(MethodReference method, TypeSig[] methodArguments)
        {
            if (methodArguments.Length == 0) return method;
            var instance = new GenericInstanceMethod(method);
            foreach (TypeSig a in methodArguments) instance.GenericArguments.Add(Ref(a));
            return instance;
        }

        private void Arguments(MethodDef method, TypeSig? declaringType, HExpr[] arguments)
        {
            for (int i = 0; i < arguments.Length; i++)
            {
                HExpr? a = arguments[i];
                if (a == null) throw new CannotEmit("missing call argument");
                TypeSig parameter = i < method.Parameters.Length ? method.Parameters[i].Type : _model.Sigs.Primitive(Il2CppTypeEnum.Object);
                if (declaringType is GenericInstSig g) parameter = _model.Sigs.Substitute(parameter, g.Arguments, []);
                if (parameter is ByRefSig && a is not HAddressOf && a.Type is not ByRefSig && IsAddressable(a)) Address(a);
                else ValueAs(a, parameter);
            }
        }

        private void Call(HCall call)
        {
            MethodDef m = call.Method;
            MethodReference target = Instantiate(_e.ImportMethod(_module, m, call.DeclaringType), call.MethodArguments);
            if (call.Constrained != null)
            {
                // An interface method called on a struct where it is: the struct's address, and its type for the
                // runtime to find the implementation by.
                if (call.This == null) throw new CannotEmit("constrained call without a receiver");
                Address(call.This);
                Arguments(m, call.DeclaringType, call.Arguments);
                _il.Emit(OpCodes.Constrained, Ref(call.Constrained));
                _il.Emit(OpCodes.Callvirt, target);
                return;
            }
            // A method called on a T: on the T where it is, with its type for the runtime to find the method by
            // (right for a class and for a struct alike).
            if (!m.IsStatic && m.Name != ".ctor" && Own(call.This?.Type) is { } receiver)
            {
                Address(call.This);
                Arguments(m, call.DeclaringType, call.Arguments);
                _il.Emit(OpCodes.Constrained, Ref(receiver));
                _il.Emit(OpCodes.Callvirt, target);
                return;
            }
            bool structReceiver = m.DeclaringType.IsValueType;
            if (!m.IsStatic)
            {
                if (call.This == null) throw new CannotEmit("instance call without a receiver");
                if (structReceiver) Address(call.This);
                else Value(call.This);
            }
            Arguments(m, call.DeclaringType, call.Arguments);

            // Calls on objects check the receiver for null, as "callvirt" does; a direct "call" is for struct
            // methods, constructors, and "base.Method()".
            bool direct = m.IsStatic || structReceiver || m.Name == ".ctor" || (m.IsVirtual && !call.Virtual);
            _il.Emit(direct ? OpCodes.Call : OpCodes.Callvirt, target);
        }

        private void TypeOperation(HTypeExpr t)
        {
            TypeReference type = Ref(t.Target);
            switch (t.Op)
            {
                case HTypeOp.Box:
                    Value(t.Operand!);
                    _il.Emit(OpCodes.Box, type);
                    return;
                case HTypeOp.UnboxAny:
                    Value(t.Operand!);
                    _il.Emit(OpCodes.Unbox_Any, type);
                    return;
                case HTypeOp.IsInst:
                    Value(t.Operand!);
                    if (Own(t.Operand!.Type) is { } tested) _il.Emit(OpCodes.Box, Ref(tested));
                    _il.Emit(OpCodes.Isinst, type);
                    // "x as T": the object, or null, as a T.
                    if (Own(t.Target) != null) _il.Emit(OpCodes.Unbox_Any, type);
                    return;
                case HTypeOp.CastClass:
                    Value(t.Operand!);
                    if (Own(t.Operand!.Type) is { } cast) _il.Emit(OpCodes.Box, Ref(cast));
                    // "(T)x" is a cast where T is a class and an unboxing where it is not: one instruction says both.
                    _il.Emit(Own(t.Target) != null ? OpCodes.Unbox_Any : OpCodes.Castclass, type);
                    return;
                case HTypeOp.Default:
                    Default(t.Target);
                    return;
                case HTypeOp.SizeOf:
                    _il.Emit(OpCodes.Sizeof, type);
                    return;
                case HTypeOp.StackAlloc:
                    // "stackalloc T[n]": the byte count, unsigned native, then localloc (zeroed: the body says localsinit).
                    Value(t.Operand!);
                    _il.Emit(OpCodes.Conv_U);
                    if (Bits(t.Target) is int bits and > 8)
                    {
                        _il.Emit(OpCodes.Sizeof, type);
                        _il.Emit(OpCodes.Mul_Ovf_Un);
                    }
                    _il.Emit(OpCodes.Localloc);
                    return;
                case HTypeOp.Allocate:
                    if (_owner.RawAllocator == null || _owner.TypeFromHandle == null)
                        throw new CannotEmit("the class library has no way to allocate an object without a constructor");
                    _il.Emit(OpCodes.Ldtoken, type);
                    _il.Emit(OpCodes.Call, _e.ImportMethod(_module, _owner.TypeFromHandle));
                    _il.Emit(OpCodes.Call, _e.ImportMethod(_module, _owner.RawAllocator));
                    _il.Emit(OpCodes.Castclass, type);
                    return;
                default:
                    _il.Emit(OpCodes.Ldtoken, type);
                    return;
            }
        }
    }
}
