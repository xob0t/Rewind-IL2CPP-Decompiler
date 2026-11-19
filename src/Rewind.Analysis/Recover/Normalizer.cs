using Rewind.Model;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
using Rewind.Analysis.Runtime;
using Rewind.Binary;

namespace Rewind.Analysis.Recover;

public enum ThrowKind { None, NullReference, IndexOutOfRange, DivideByZero, InvalidCast, Overflow, ArrayTypeMismatch, StackCheck }

/// <summary>A type check the native code performed with "throw InvalidCastException" on failure: a castclass.</summary>
public sealed record CastFact(Block At, Node Object, Node Klass);

public sealed class NormalizeResult
{
    public List<CastFact> Casts = [];
    /// <summary>(operation, left, right) triples whose overflow is checked.</summary>
    public HashSet<(Op, Node, Node)> CheckedArithmetic = [];
    public int GuardsRemoved, HelpersRemoved, RegionsRemoved;
}

/// <summary>
/// Strips what IL2CPP adds around the program's own logic and what has no IL counterpart: lazy metadata
/// initialization, static-constructor triggers, GC write barriers, and the explicit null / bounds / cast /
/// divide checks that IL instructions perform implicitly. What remains maps directly onto IL.
/// </summary>
public sealed partial class Normalizer(ProgramAnalysis program)
{
    private Function _fn = null!;
    private NormalizeResult _result = null!;
    private IrBuilder _b = null!;
    private readonly Dictionary<Node, Node> _replace = [];

    public NormalizeResult Run(Function fn)
    {
        _fn = fn;
        _b = new IrBuilder(fn);
        _result = new NormalizeResult();
        _replace.Clear();

        _slotValues.Clear();
        _lazyTargets.Clear();
        if (ExpandLookupTables()) ApplyReplacements();
        CanonicalizeSlotLoads();
        RemoveNoOpHelpers();
        RemoveInitFlagStores();
        AssumeClassesInitialized();
        ApplyReplacements();

        bool changed = true;
        for (int round = 0; changed && round < 16; round++)
        {
            changed = RemoveGuards();
            changed |= RemoveInlineBarriers();
            changed |= Structure();
            changed |= CollapseInterfaceLookups();
            changed |= CollapseLazyTargets();
            changed |= RemoveUnusedLookups();
            changed |= MergeInterfaceTailCalls();
            changed |= CollapseDelegateInits();
            changed |= CollapseDelegateGuards();
            changed |= CollapsePInvokeTargets();
        }
        return _result;
    }

    /// <summary>
    /// IL2CPP pastes its delegate constructor in place. After storing the method, the target and the code
    /// pointer, it picks the invoke stub by whether the method is static and how many parameters it takes - and
    /// for an instance method without a target it throws ArgumentException, as the CLR's delegate constructor
    /// does. That choice is the runtime's bookkeeping, not the program's: the region from the MethodIsStatic test
    /// to the stores of the chosen stub (invoke_impl, extra_arg) goes. The stores naming the method and the
    /// target stay; the high-level form turns them back into "new D(target, method)" (DelegateFolding).
    /// </summary>
    private bool CollapseDelegateInits()
    {
        bool changed = false;
        foreach (Block s in _fn.Blocks.ToList())
        {
            if (!_fn.Blocks.Contains(s) || s.Terminator is not { Op: Op.Branch } term || s.Succs.Count != 2) continue;
            Node? test = s.Nodes.LastOrDefault(n => !n.Dead && HelperOf(n) == HelperKind.MethodIsStatic);
            if (test == null || IntArg(test, 0) is not { } method) continue;
            method = Resolve(method);
            // The delegate: the object the method is stored into, in this block, before the test.
            Node? obj = null;
            foreach (Node n in s.Nodes)
            {
                if (ReferenceEquals(n, test)) break;
                if (!n.Dead && n.Op == Op.Store && ReferenceEquals(Resolve(n.In[1]), method) && n.In[0] is { Op: Op.Add } a && a.In[1].IsConst)
                    obj = Resolve(a.In[0]);
            }
            if (obj == null) continue;
            bool OnObject(Node address, Node baseNode) => address.Op == Op.Add && address.In[1].IsConst && ReferenceEquals(Resolve(address.In[0]), baseNode);

            // The join: the first block, breadth first, that every way out of the test reaches (or throws before).
            var bfs = new List<Block>();
            var seen = new HashSet<Block> { s };
            var queue = new Queue<Block>(s.Succs);
            while (queue.Count > 0 && bfs.Count < 24)
            {
                Block b = queue.Dequeue();
                if (!seen.Add(b)) continue;
                bfs.Add(b);
                foreach (Block next in b.Succs) queue.Enqueue(next);
            }
            Block? join = null;
            HashSet<Block>? region = null;
            foreach (Block j in bfs)
            {
                var inside = new HashSet<Block>();
                var work = new Stack<Block>(s.Succs.Where(b => !ReferenceEquals(b, j)));
                bool bounded = true;
                while (work.Count > 0 && bounded)
                {
                    Block b = work.Pop();
                    if (ReferenceEquals(b, s) || inside.Count > 24) { bounded = false; break; }
                    if (!inside.Add(b)) continue;
                    foreach (Block next in b.Succs)
                        if (!ReferenceEquals(next, j)) work.Push(next);
                }
                if (!bounded) continue;
                bool closed = inside.All(b => b.Preds.All(p => inside.Contains(p) || ReferenceEquals(p, s))) &&
                              inside.All(b => b.Succs.Count != 0 || b.Terminator?.Op == Op.Unreachable) &&
                              j.Preds.All(p => inside.Contains(p) || ReferenceEquals(p, s));
                if (!closed) continue;
                join = j;
                region = inside;
                break;
            }
            if (join == null || region == null) continue;

            // Only the delegate's bookkeeping may happen in between.
            bool clean = true;
            foreach (Block b in region)
                foreach (Node n in b.Nodes)
                {
                    if (n.Dead) continue;
                    bool fine = n.Op switch
                    {
                        Op.Store => OnObject(n.In[0], obj),
                        Op.Load => OnObject(n.In[0], obj) || OnObject(n.In[0], method),
                        Op.Call => HelperOf(n) is HelperKind.GetArgumentException or HelperKind.Throw && b.Terminator?.Op == Op.Unreachable,
                        Op.Proj or Op.Jump or Op.Branch or Op.Unreachable or Op.Const or Op.Add or Op.Trunc or Op.ZExt or Op.SExt
                            or Op.CmpEq or Op.CmpNe or Op.And or Op.Or or Op.Xor or Op.Select or Op.Flags => true,
                        _ => false,
                    };
                    if (!fine) { clean = false; break; }
                }
            if (!clean) continue;
            // At the join: the stores of the chosen stub, of values from the region or constants.
            var stubStores = new List<Node>();
            foreach (Node n in join.Nodes)
            {
                if (n.Dead || n.Op is Op.Add or Op.Const) continue;
                if (n.Op == Op.Store && OnObject(n.In[0], obj) && (n.In[1].IsConst || join.Phis.Contains(n.In[1]))) { stubStores.Add(n); continue; }
                break;
            }
            var uses = DeadCode.Uses(_fn);
            bool phisLocal = join.Phis.All(phi => !uses.TryGetValue(phi, out List<Node>? users) || users.All(stubStores.Contains));
            if (stubStores.Count == 0 || !phisLocal) continue;

            foreach (Node n in stubStores)
            {
                n.Dead = true;
                join.Nodes.Remove(n);
            }
            foreach (Node phi in join.Phis) phi.Dead = true;
            join.Phis.Clear();
            foreach (Block b in region)
            {
                foreach (Node n in b.Nodes) n.Dead = true;
                b.Preds.Clear();
                b.Succs.Clear();
                _fn.Blocks.Remove(b);
            }
            join.Preds.Clear();
            test.Dead = true;
            // The code pointer the constructor reads out of the method's runtime record goes with the rest: the
            // store it feeds becomes part of "new D(target, method)".
            foreach (Node n in s.Nodes)
                if (!n.Dead && n.Op == Op.Store && OnObject(n.In[0], obj) && n.In[1] is { Op: Op.Load } read && OnObject(read.In[0], method))
                    n.In[1] = method;
            MakeJump(s, join);
            join.Preds.Add(s);
            for (int i = 0; i < _fn.Blocks.Count; i++) _fn.Blocks[i].Id = i;
            DeadCode.Run(_fn);
            _result.RegionsRemoved++;
            changed = true;
        }
        return changed;
    }

    /// <summary>
    /// Unity 2020's delegate constructor, pasted in place, is shorter: a guard, "if (target == null &amp;&amp;
    /// !MethodIsStatic(method)) throw new ArgumentException(...)", and then the stores of the code pointer, the
    /// method and the target. The guard is the runtime's check, as above, and goes; the code pointer read out of
    /// the method's record becomes the method, as above (DelegateFolding makes "new D(target, method)" of it).
    /// </summary>
    private bool CollapseDelegateGuards()
    {
        bool changed = false;
        foreach (Block guard in _fn.Blocks.ToList())
        {
            if (!_fn.Blocks.Contains(guard) || guard.Terminator is not { Op: Op.Branch } || guard.Succs.Count != 2) continue;
            Node? test = guard.Nodes.LastOrDefault(n => !n.Dead && HelperOf(n) == HelperKind.MethodIsStatic);
            if (test == null || IntArg(test, 0) is not { } method) continue;
            method = Resolve(method);

            // One way out only throws the ArgumentException; the other goes on to the stores.
            bool OnlyThrows(Block b) =>
                b.Preds.Count == 1 && b.Phis.Count == 0 && b.Terminator?.Op == Op.Unreachable &&
                b.Nodes.Any(n => !n.Dead && HelperOf(n) == HelperKind.GetArgumentException) &&
                b.Nodes.All(n => n.Dead || n.Op is Op.Proj or Op.Const or Op.Unreachable ||
                                 (n.Op == Op.Call && HelperOf(n) is HelperKind.GetArgumentException or HelperKind.Throw));
            Block? thrower = guard.Succs.FirstOrDefault(OnlyThrows);
            if (thrower == null) continue;
            Block next = ReferenceEquals(guard.Succs[0], thrower) ? guard.Succs[1] : guard.Succs[0];
            if (ReferenceEquals(next, thrower) || ReferenceEquals(next, guard)) continue;

            // The delegate: the object the method is stored into where the guard lets through.
            bool OnObject(Node address, Node baseNode) => address.Op == Op.Add && address.In[1].IsConst && ReferenceEquals(Resolve(address.In[0]), baseNode);
            Node? obj = null;
            foreach (Node n in next.Nodes)
                if (!n.Dead && n.Op == Op.Store && ReferenceEquals(Resolve(n.In[1]), method) && n.In[0] is { Op: Op.Add } a && a.In[1].IsConst)
                    obj = Resolve(a.In[0]);
            if (obj == null) continue;
            // The test's answer decides the guard and nothing else.
            var uses = DeadCode.Uses(_fn);
            bool local = true;
            var pending = new Stack<Node>();
            pending.Push(test);
            var seen = new HashSet<Node>();
            while (pending.Count > 0 && local)
            {
                Node n = pending.Pop();
                if (!seen.Add(n) || !uses.TryGetValue(n, out List<Node>? users)) continue;
                foreach (Node user in users)
                {
                    if (ReferenceEquals(user, guard.Terminator)) continue;
                    if (!ReferenceEquals(user.Block, guard) || user.Op is Op.Store or Op.Call or Op.Phi) { local = false; break; }
                    pending.Push(user);
                }
            }
            if (!local) continue;

            foreach (Node n in thrower.Nodes) n.Dead = true;
            thrower.Preds.Clear();
            thrower.Succs.Clear();
            _fn.Blocks.Remove(thrower);
            test.Dead = true;
            // (methodPointer is the first word of the record: read at the record's own address.)
            foreach (Node n in next.Nodes)
                if (!n.Dead && n.Op == Op.Store && OnObject(n.In[0], obj) && n.In[1] is { Op: Op.Load } read &&
                    (ReferenceEquals(Resolve(read.In[0]), method) || OnObject(read.In[0], method)))
                    n.In[1] = method;
            MakeJump(guard, next);
            for (int i = 0; i < _fn.Blocks.Count; i++) _fn.Blocks[i].Id = i;
            DeadCode.Run(_fn);
            _result.RegionsRemoved++;
            changed = true;
        }
        return changed;
    }

    /// <summary>One round of the structural cleanups; true when anything changed.</summary>
    private bool Structure()
    {
        // Merges of one value (left behind when a lookup collapsed into the value it looked up) are that value.
        foreach (Block b in _fn.Blocks.ToList()) SimplifyPhis(b);
        bool changed = CollapsePhiCycles();
        changed |= RefoldTruncations();
        changed |= RejoinSplitMerges();
        changed |= UseKnownZeros();
        changed |= FoldKnownBranches();
        changed |= RemoveUnreachable();
        DeadCode.Run(_fn);
        changed |= MergeFloatBranches();
        changed |= MergeReturnBlocks();
        changed |= CollapseEmptyConditionals();
        changed |= FoldBooleanReturns();
        changed |= MergeLinearBlocks();
        return changed;
    }

    /// <summary>
    /// Re-runs the structural cleanups. Call after another pass (stack promotion, dead code removal) has made
    /// more blocks empty.
    /// </summary>
    public void Cleanup(Function fn)
    {
        _fn = fn;
        _b = new IrBuilder(fn);
        _result ??= new NormalizeResult();
        _replace.Clear();
        bool changed = true;
        for (int round = 0; changed && round < 16; round++) changed = Structure();
    }

    // ---- value replacement ---------------------------------------------------------------------------------

    private Node Resolve(Node n)
    {
        while (_replace.TryGetValue(n, out Node? next)) n = next;
        return n;
    }

    private void ApplyReplacements()
    {
        if (_replace.Count == 0) return;
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node n in b.Phis)
                for (int i = 0; i < n.In.Length; i++) n.In[i] = Resolve(n.In[i]);
            foreach (Node n in b.Nodes)
                for (int i = 0; i < n.In.Length; i++) n.In[i] = Resolve(n.In[i]);
        }
        _replace.Clear();
    }

    private static Node? Arg(Node call, ArgSlotKind kind, int index)
    {
        if (call.Aux is not CallInfo info) return null;
        for (int i = 0; i < info.Slots.Count && i < call.In.Length; i++)
            if (info.Slots[i].Kind == kind && info.Slots[i].Index == index)
                return call.In[i];
        return null;
    }

    public static Node? IntArg(Node call, int position) => Arg(call, ArgSlotKind.IntReg, position);

    private HelperKind HelperOf(Node n) =>
        n.Op == Op.Call && n.Aux is CallInfo { Indirect: false, Intrinsic: null } ci ? program.Helpers.KindAt(ci.Target) : HelperKind.None;

    // ---- metadata slots -----------------------------------------------------------------------------------

    private readonly Dictionary<ulong, Node> _slotValues = [];

    private bool IsMetadataSlot(ulong va) =>
        program.Defaults.Slots.ContainsKey(va) || program.Model.ResolveUsageSlot(va) != null;

    private Node SlotValue(ulong va)
    {
        if (!_slotValues.TryGetValue(va, out Node? node))
        {
            node = _fn.NewNode(Op.SlotValue, VT.I64, null);
            node.Imm = (long)va;
            _slotValues[va] = node;
        }
        return node;
    }

    /// <summary>
    /// A metadata slot holds one fixed value for the life of the program (a class, a method, a string literal).
    /// Every read of the same slot therefore denotes the same value; giving them one shared node lets later
    /// passes see that.
    /// </summary>
    private void CanonicalizeSlotLoads()
    {
        // A read through a choice of slots (a select or phi of their addresses) reads the chosen slot's value.
        var chosen = new List<Node>();
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node n in b.Nodes)
            {
                if (n.Op != Op.Load || n.Type != VT.I64) continue;
                if (!n.In[0].IsConst)
                {
                    if (!n.Dead && IsSlotChoice(Resolve(n.In[0]), 0, [])) chosen.Add(n);
                    continue;
                }
                ulong va = (ulong)n.In[0].Imm;
                if (!IsMetadataSlot(va)) continue;
                _replace[n] = SlotValue(va);
                n.Dead = true;
            }
            b.Nodes.RemoveAll(n => n.Dead);
        }
        if (chosen.Count == 0) return;
        var made = new Dictionary<Node, Node>();
        foreach (Node n in chosen)
        {
            _replace[n] = SlotRead(Resolve(n.In[0]), made);
            n.Dead = true;
        }
        foreach (Block b in _fn.Blocks) b.Nodes.RemoveAll(n => n.Dead);
    }

    // ---- helpers with no managed meaning -------------------------------------------------------------------

    /// <summary>
    /// A function that ends by jumping into a helper with no managed meaning (typically the write barrier after
    /// the last field store) simply returns there. Only void functions can end that way.
    /// </summary>
    private void RemoveNoOpTailCalls()
    {
        foreach (Block b in _fn.Blocks)
            if (b.Terminator is { Op: Op.Return } r && r.In.Length != 0)
                return;
        foreach (Block b in _fn.Blocks)
        {
            Node? tail = b.Terminator;
            if (tail?.Op != Op.TailCall || tail.Aux is not CallInfo { Indirect: false, Intrinsic: null } info) continue;
            if (program.Helpers.KindAt(info.Target) is not (HelperKind.WriteBarrier or HelperKind.WriteBarrierForClass
                or HelperKind.WriteBarrierForType or HelperKind.NullCheck or HelperKind.MetadataInit or HelperKind.ClassInit
                or HelperKind.ArrayElementTypeCheck or HelperKind.MemoryBarrier)) continue;
            tail.Op = Op.Return;
            tail.Aux = null;
            tail.In = [];
            _result.HelpersRemoved++;
        }
    }

    private void RemoveNoOpHelpers()
    {
        RemoveNoOpTailCalls();
        foreach (Block b in _fn.Blocks)
        {
            for (int i = 0; i < b.Nodes.Count; i++)
            {
                Node call = b.Nodes[i];
                HelperKind kind = HelperOf(call);
                if (kind == HelperKind.None) continue;

                Node? result = null;
                bool remove = true;
                switch (kind)
                {
                    case HelperKind.MetadataInit:
                    case HelperKind.ClassInit:
                    case HelperKind.WriteBarrier:
                    case HelperKind.WriteBarrierForClass:
                    case HelperKind.WriteBarrierForType:
                    case HelperKind.NullCheck:
                    case HelperKind.ArrayElementTypeCheck:
                    case HelperKind.CheckStack:
                    case HelperKind.MemoryBarrier:
                        break;
                    case HelperKind.ClassInitSlow:
                    case HelperKind.RgctxInitSlow:
                        result = IntArg(call, 0); // returns its argument once initialized
                        break;
                    case HelperKind.MetadataInitInline:
                    {
                        // Returns the initialized content of the slot whose address it was given.
                        Node? slot = IntArg(call, 0);
                        int count = b.Nodes.Count;
                        if (slot != null && !slot.IsConst && !_fn.Regs.SharedPositions && SlotChoice(slot) is { } choice)
                        {
                            // One call for two slots, the compiler having merged two ways that differed in it
                            // alone: the content of the slot each way brings. (Selects of the contents go next
                            // to the selects of the addresses, before the call.)
                            i += b.Nodes.Count - count;
                            result = choice;
                            break;
                        }
                        if (slot == null || !slot.IsConst) { remove = false; break; }
                        result = SlotValue((ulong)slot.Imm);
                        break;
                    }
                    case HelperKind.StaticFieldsFor:
                    {
                        Node? klass = IntArg(call, 0);
                        if (klass == null) { remove = false; break; }
                        Node offset = _fn.NewNode(Op.Const, VT.I64, null);
                        offset.Imm = program.Klass.StaticFields;
                        Node address = NewNodeAt(b, i, Op.Add, VT.I64, call.Addr, klass, offset);
                        result = NewNodeAt(b, i + 1, Op.Load, VT.I64, call.Addr, address);
                        i += 2;
                        break;
                    }
                    case HelperKind.MethodVirtualCallPointer:
                    {
                        // What later Unity versions do in place: read virtualMethodPointer, the second word of
                        // the method's record.
                        Node? method = IntArg(call, 0);
                        if (method == null) { remove = false; break; }
                        Node offset = _fn.NewNode(Op.Const, VT.I64, null);
                        offset.Imm = program.Model.Image.PointerSize;
                        Node address = NewNodeAt(b, i, Op.Add, VT.I64, call.Addr, method, offset);
                        result = NewNodeAt(b, i + 1, Op.Load, VT.I64, call.Addr, address);
                        i += 2;
                        break;
                    }
                    default:
                        remove = false;
                        break;
                }
                if (!remove) continue;

                call.Dead = true;
                _result.HelpersRemoved++;
                // Results are the projections that directly follow the call.
                for (int k = i + 1; k < b.Nodes.Count && b.Nodes[k].Op == Op.Proj && ReferenceEquals(b.Nodes[k].In[0], call); k++)
                {
                    Node proj = b.Nodes[k];
                    proj.Dead = true;
                    if (proj.Imm == CallResult.IntReturn && result != null) _replace[proj] = result;
                    else
                    {
                        Node undef = _fn.NewNode(Op.Undef, proj.Type, null);
                        _replace[proj] = undef;
                    }
                }
            }
            b.Nodes.RemoveAll(n => n.Dead);
        }
    }

    private Node NewNodeAt(Block b, int index, Op op, VT type, ulong address, params Node[] inputs)
    {
        Node n = _fn.NewNode(op, type, b, inputs);
        n.Addr = address;
        b.Nodes.Insert(index, n);
        return n;
    }

    /// <summary>
    /// Generated functions keep a "metadata initialized" byte per method. Once the initialization calls are gone
    /// the flag has no purpose; removing the store lets the guarded block fold away.
    /// </summary>
    private void RemoveInitFlagStores()
    {
        NativeImage image = program.Model.Image;
        HashSet<ulong>? flags = null;
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node n in b.Nodes)
            {
                if (n.Op != Op.Store || !n.In[0].IsConst || !n.In[1].IsConstValue(1) || n.In[1].Type != VT.I8) continue;
                ulong va = (ulong)n.In[0].Imm;
                if (image.SectionAt(va) is not { IsWritable: true }) continue;
                if (program.Model.ResolveUsageSlot(va) != null) continue;
                n.Dead = true;
                (flags ??= []).Add(va);
            }
            b.Nodes.RemoveAll(n => n.Dead);
        }
        if (flags == null) return;
        // Reading the flag decides between "initialize first" and "go on": with the initialization no part of
        // the program, the function is the "go on" path. The flag reads as set.
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op != Op.Load || n.Type != VT.I8 || !n.In[0].IsConst || !flags.Contains((ulong)n.In[0].Imm)) continue;
                _replace[n] = _b.Const(VT.I8, 1);
                n.Dead = true;
            }
            b.Nodes.RemoveAll(n => n.Dead);
        }
    }

    /// <summary>
    /// Before touching a class's statics, generated code checks whether the class's static constructor has run
    /// ("if (!klass->cctor_finished) run it"). Managed code has no such check - the runtime sees to it - and the
    /// call that would run the constructor is already gone, so the check reads as "it has run".
    /// </summary>
    private void AssumeClassesInitialized()
    {
        int flag = program.Klass.CctorFinished;
        if (flag <= 0) return;
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op != Op.Load || n.Type != VT.I32 || n.In[0] is not { Op: Op.Add } address || !address.In[1].IsConst ||
                    IrBuilder.SImm(address.In[1]) != flag)
                    continue;
                // The class: named directly, or read out of a method's record (a generic method's own class) - or
                // a merge of such, the slot read again after the call that would have run the constructor.
                if (!NamedClass(Resolve(address.In[0]), 0)) continue;
                _replace[n] = _b.Const(VT.I32, 1);
                n.Dead = true;
            }
            b.Nodes.RemoveAll(n => n.Dead);
        }
    }

    private bool NamedClass(Node klass, int depth)
    {
        if (klass.Op == Op.SlotValue) return true;
        if (klass.Op == Op.Load && klass.In[0] is { Op: Op.Add } from && from.In[1].IsConst && Resolve(from.In[0]).Op == Op.SlotValue) return true;
        // (A slot load the canonicalization has turned into the slot's value, not yet replaced in the merge.)
        if (klass.Op == Op.Load && klass.In[0].IsConst && IsMetadataSlot(klass.In[0].UImm)) return true;
        if (NoMergedClasses || klass.Op != Op.Phi || depth >= 4 || klass.In.Length == 0) return false;
        foreach (Node input in klass.In)
        {
            Node value = Resolve(input);
            if (ReferenceEquals(value, klass)) continue;
            if (!NamedClass(value, depth + 1)) return false;
        }
        return true;
    }

    private static readonly bool NoMergedClasses = Environment.GetEnvironmentVariable("REWIND_NO_MERGED_CCTOR_CLASSES") != null;

    /// <summary>
    /// A narrowing is folded when it is built; its operand may only later become something it folds into. The
    /// usual case: a byte register set to a constant ("mov al, 1") is the old register with its low byte
    /// replaced, and once the paths that do this are merged, the low byte of that is the constant.
    /// </summary>
    private bool RefoldTruncations()
    {
        bool changed = false;
        foreach (Block b in _fn.Blocks)
        {
            for (int i = 0; i < b.Nodes.Count; i++)
            {
                Node n = b.Nodes[i];
                if (n.Dead) continue;
                // Two halves of one 64-bit value put together again (a reference that travelled through two
                // 32-bit stack cells) are that value.
                if (n.Op == Op.Concat && Resolve(n.In[1]) is { Op: Op.Trunc } low && low.In[0].Type == VT.I64 &&
                    Resolve(n.In[0]) is { Op: Op.Trunc } high && high.In[0] is { Op: Op.ShrU } shifted && shifted.In[1].IsConstValue(32) &&
                    ReferenceEquals(Resolve(shifted.In[0]), Resolve(low.In[0])))
                {
                    _replace[n] = Resolve(low.In[0]);
                    n.Dead = true;
                    changed = true;
                    continue;
                }
                // The same where the bottom half was narrowed further in: "trunc(a) + c" beside the top of "a + c".
                if (n.Op == Op.Concat && !IrBuilder.NoSumHalves && Resolve(n.In[0]) is { Op: Op.Trunc } top &&
                    top.In[0] is { Op: Op.ShrU } moved && moved.In[1].IsConstValue(32) &&
                    IrBuilder.IsLowHalf(n.In[1], moved.In[0], Resolve))
                {
                    _replace[n] = Resolve(moved.In[0]);
                    n.Dead = true;
                    changed = true;
                    continue;
                }
                // Two halves under one mask each are the whole under the mask made of both: "xorps x, m" on a
                // double whose mask was loaded once (ahead of a loop) is a 32-bit operation per lane, with
                // constants known only now. The whole, its halves put together, folds or merges as above.
                if (n.Op == Op.Concat && !NoMaskedHalves && MaskedHalves(n) is var (op, wholeHigh, wholeLow, mask))
                {
                    _b.Current = b;
                    _b.InsertIndex = i;
                    _b.CurrentAddr = n.Addr;
                    int count = b.Nodes.Count;
                    Node masked = _b.Binary(op, _b.Concat(wholeHigh, wholeLow), _b.Const(VT.I64, (long)mask));
                    _b.InsertIndex = -1;
                    i += b.Nodes.Count - count;
                    _replace[n] = masked;
                    n.Dead = true;
                    changed = true;
                    continue;
                }
                if (n.Op != Op.Trunc) continue;
                Node operand = Resolve(n.In[0]);
                if (operand.Op is not (Op.Or or Op.And or Op.Const)) continue;
                int before = b.Nodes.Count;
                _b.Current = b;
                _b.InsertIndex = i;
                _b.CurrentAddr = n.Addr;
                Node folded = _b.Trunc(operand, n.Type);
                _b.InsertIndex = -1;
                i += b.Nodes.Count - before;
                if (ReferenceEquals(folded, n) || (folded.Op == Op.Trunc && ReferenceEquals(folded.In[0], operand))) continue; // nothing gained
                if (!folded.IsConst) continue; // only the complete fold is taken: partial ones are the same value at more nodes
                _replace[n] = folded;
                n.Dead = true;
                changed = true;
            }
        }
        if (!changed) return false;
        foreach (Block b in _fn.Blocks) b.Nodes.RemoveAll(n => n.Dead);
        ApplyReplacements();
        return true;
    }

    private static readonly bool NoMaskedHalves = Environment.GetEnvironmentVariable("REWIND_NO_MASKED_HALVES") != null;

    /// <summary>
    /// A Concat whose top half is under a bitwise mask and whose bottom half is not (or is under the op's
    /// identity, a constant known only now): the op, the two unmasked halves and the 64-bit mask. That is the
    /// sign or magnitude of a double; two masked halves are two floats (a Vector2 negated), left as they are.
    /// </summary>
    private (Op Op, Node High, Node Low, ulong Mask)? MaskedHalves(Node concat)
    {
        Node high = Resolve(concat.In[0]), low = Resolve(concat.In[1]);
        if (high.Op is not (Op.Xor or Op.And or Op.Or) || high.In.Length != 2 || high.Type != VT.I32 || low.Type != VT.I32 || low.IsConst) return null;
        Node value = Resolve(high.In[0]), mask = Resolve(high.In[1]);
        if (value.IsConst && !mask.IsConst) (value, mask) = (mask, value);
        if (!mask.IsConst || value.IsConst) return null;
        uint identity = high.Op == Op.And ? uint.MaxValue : 0u;
        if (low.Op == high.Op && low.In.Length == 2)
        {
            Node a = Resolve(low.In[0]), b = Resolve(low.In[1]);
            if (a.IsConst && !b.IsConst) (a, b) = (b, a);
            if (b.IsConst && !a.IsConst)
            {
                if ((uint)b.UImm != identity) return null;
                low = a;
            }
        }
        // Only where the halves are those of a double: a struct of two floats with its second one negated
        // looks the same.
        if (!HalfOfDouble(value, []) && !HalfOfDouble(low, [])) return null;
        return (high.Op, value, low, (mask.UImm & 0xFFFFFFFFUL) << 32 | identity);
    }

    /// <summary>Is this a half of the bits of a double: cut out of them, returned in the top lane, or merged from such halves (and constants)?</summary>
    private bool HalfOfDouble(Node n, HashSet<Node> seen)
    {
        n = Resolve(n);
        // (Met again: its answer is the one already being given - every part must be such a half.)
        if (!seen.Add(n)) return true;
        if (seen.Count > 64) return false;
        switch (n.Op)
        {
            case Op.FToBits: return n.In[0].Type == VT.F64;
            // The second lane of what a call returns in a vector register: only a double fills it.
            case Op.Proj when n.Imm == CallResult.FloatLane1: return true;
            case Op.Trunc: return HalfOfDouble(n.In[0], seen);
            case Op.ShrU when n.In[1].IsConstValue(32): return HalfOfDouble(n.In[0], seen);
            case Op.Phi:
            {
                bool any = false;
                foreach (Node input in n.In)
                {
                    Node value = Resolve(input);
                    if (value.IsConst || ReferenceEquals(value, n)) continue;
                    if (!HalfOfDouble(value, seen)) return false;
                    any = true;
                }
                return any;
            }
            default: return false;
        }
    }

    private static readonly bool NoKnownZeros = Environment.GetEnvironmentVariable("REWIND_NO_KNOWN_ZEROS") != null;

    /// <summary>
    /// Where a test has just found a value to be zero, it is zero. "a != null ? a.b : default" hands on a itself
    /// on the way where it is null - the register that holds it is the cheapest zero at hand. Read literally
    /// that is an object where a number belongs, or one object where another belongs. Here the value is written
    /// as the constant it is known to be: in what a way in gives to a merged value, and in a block that only
    /// that way leads to.
    /// </summary>
    private bool UseKnownZeros()
    {
        if (NoKnownZeros) return false;
        bool changed = false;
        foreach (Block p in _fn.Blocks)
        {
            if (p.Terminator is not { Op: Op.Branch } term || p.Succs.Count != 2 || ReferenceEquals(p.Succs[0], p.Succs[1]) || Function.IsTryEntry(term.In[0])) continue;
            Node cond = Resolve(term.In[0]);
            if (cond.Op is not (Op.CmpEq or Op.CmpNe) || cond.In.Length != 2 || !cond.In[1].IsConstValue(0)) continue;
            Node tested = Resolve(cond.In[0]);
            if (tested.IsConst || tested.Type is not (VT.I64 or VT.I32)) continue;
            Block zero = p.Succs[cond.Op == Op.CmpEq ? 0 : 1];

            Node? Known(Node input)
            {
                if (ReferenceEquals(input, tested)) return _b.Const(tested.Type, 0);
                if (input.Op == Op.Trunc && ReferenceEquals(input.In[0], tested)) return _b.Const(input.Type, 0);
                return null;
            }
            bool Merges(Block from, Block into)
            {
                int at = into.Preds.IndexOf(from);
                if (at < 0 || into.Preds.LastIndexOf(from) != at) return false;
                bool any = false;
                foreach (Node phi in into.Phis)
                    if (!phi.Dead && at < phi.In.Length && Known(phi.In[at]) is { } constant)
                    {
                        phi.In[at] = constant;
                        any = true;
                    }
                return any;
            }

            changed |= Merges(p, zero);
            if (zero.Preds.Count != 1) continue;
            foreach (Node n in zero.Nodes)
            {
                if (n.Dead || n.Op is Op.Add or Op.Sub) continue;
                for (int i = 0; i < n.In.Length; i++)
                {
                    // Not where it is an address: nothing is read through what is null, and that is not ours to say.
                    if (i == 0 && n.Op is Op.Load or Op.Store) continue;
                    if (Known(n.In[i]) is not { } constant) continue;
                    n.In[i] = constant;
                    changed = true;
                }
            }
            foreach (Block next in zero.Succs) changed |= Merges(zero, next);
        }
        return changed;
    }

    private static readonly bool NoRejoinedMerges = Environment.GetEnvironmentVariable("REWIND_NO_REJOINED_MERGES") != null;

    /// <summary>
    /// A 64-bit value that went through two 32-bit stack cells is merged there half by half - "the low half of
    /// a or of b", "the high half of a or of b" - and put together again where it is used. That is the merge of
    /// the whole values, "a or b": a reference, as a rule, which as two halves is no reference any more.
    /// </summary>
    private bool RejoinSplitMerges()
    {
        if (NoRejoinedMerges) return false;
        Dictionary<(Node High, Node Low), Node>? whole = null;
        _notHalves.Clear();
        bool changed = false;
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op != Op.Concat) continue;
                Node high = Resolve(n.In[0]), low = Resolve(n.In[1]);
                if (high.Op != Op.Phi || low.Op != Op.Phi) continue;
                whole ??= [];
                var made = new List<(Node High, Node Low)>();
                _wholeSteps = 0;
                if (WholeOf(high, low, whole, made, 0) is not { } joined)
                {
                    foreach (var key in made) whole.Remove(key);
                    continue;
                }
                foreach (var key in made)
                {
                    Node phi = whole[key];
                    phi.Block!.Phis.Add(phi);
                }
                _replace[n] = joined;
                n.Dead = true;
                changed = true;
            }
        }
        if (!changed) return false;
        foreach (Block b in _fn.Blocks) b.Nodes.RemoveAll(n => n.Dead);
        ApplyReplacements();
        return true;
    }

    /// <summary>
    /// The 64-bit value two 32-bit values are the halves of: a value cut in two, a constant, or - where both
    /// are merges in one block - the merge of what their inputs are the halves of. Null when they are not the
    /// halves of one thing. Merges made on the way are noted in <paramref name="made"/>; they are put into
    /// their blocks only when the whole attempt works out.
    /// </summary>
    private readonly HashSet<(Node High, Node Low)> _notHalves = [];
    private int _wholeSteps;

    private Node? WholeOf(Node high, Node low, Dictionary<(Node High, Node Low), Node> whole, List<(Node High, Node Low)> made, int depth)
    {
        if (high.Type != VT.I32 || low.Type != VT.I32) return null;
        if (++_wholeSteps > 4096) return null;
        if (high.IsConst && low.IsConst) return _b.Const(VT.I64, (long)(high.UImm << 32 | (low.UImm & 0xFFFFFFFFUL)));
        if (low.Op == Op.Trunc && low.In[0].Type == VT.I64 && high.Op == Op.Trunc && Resolve(high.In[0]) is { Op: Op.ShrU } shifted &&
            shifted.In[1].IsConstValue(32) && ReferenceEquals(Resolve(shifted.In[0]), Resolve(low.In[0])))
            return Resolve(low.In[0]);
        if (high.Op != Op.Phi || low.Op != Op.Phi || ReferenceEquals(high, low) || !ReferenceEquals(high.Block, low.Block) ||
            high.In.Length != low.In.Length || high.Dead || low.Dead || depth > 32)
            return null;
        if (whole.TryGetValue((high, low), out Node? known)) return known;
        if (_notHalves.Contains((high, low))) return null;
        Node phi = _fn.NewNode(Op.Phi, VT.I64, high.Block);
        whole[(high, low)] = phi;
        made.Add((high, low));
        var inputs = new Node[high.In.Length];
        for (int i = 0; i < inputs.Length; i++)
        {
            if (WholeOf(Resolve(high.In[i]), Resolve(low.In[i]), whole, made, depth + 1) is not { } input)
            {
                // One input that is not the two halves of a value: this pair never is, whatever leads here.
                _notHalves.Add((high, low));
                return null;
            }
            inputs[i] = input;
        }
        phi.In = inputs;
        return phi;
    }

    /// <summary>A branch whose condition is known (a comparison of two constants) is a jump.</summary>
    private bool FoldKnownBranches()
    {
        bool changed = false;
        foreach (Block p in _fn.Blocks.ToList())
        {
            if (p.Terminator is not { Op: Op.Branch } term || p.Succs.Count != 2 || Function.IsTryEntry(term.In[0])) continue;
            Node cond = Resolve(term.In[0]);
            bool? known = null;
            if (cond.IsConst) known = cond.Imm != 0;
            else if (cond.Op is Op.CmpEq or Op.CmpNe or Op.CmpLtS or Op.CmpLeS or Op.CmpLtU or Op.CmpLeU && cond.In.Length == 2 &&
                     Resolve(cond.In[0]) is { IsConst: true } a && Resolve(cond.In[1]) is { IsConst: true } b && a.Type.IsInt() && a.Type == b.Type)
                known = _b.Cmp(cond.Op, a, b).Imm != 0;
            if (known == null) continue;
            Block taken = p.Succs[known.Value ? 0 : 1], other = p.Succs[known.Value ? 1 : 0];
            if (!ReferenceEquals(taken, other)) RemoveEdge(p, other);
            else RemoveEdge(p, other); // both ways led to one block: it loses one of its two entries
            term.Op = Op.Jump;
            term.In = [];
            p.Succs.Clear();
            p.Succs.Add(taken);
            changed = true;
        }
        return changed;
    }

    // ---- calls into the engine ----------------------------------------------------------------------------

    private readonly Dictionary<ulong, Node> _lazyTargets = [];

    /// <summary>
    /// A call into the engine goes through a pointer that is looked up by name on first use and remembered in
    /// a static: "if (p == null) p = resolve("Type::Method"); p(args)". The pointer only ever holds one value,
    /// the implementation of that method, so every read of the static is that value and the lookup is not
    /// part of the program.
    /// </summary>
    private bool CollapseLazyTargets()
    {
        Dictionary<Node, Node>? resolved = null;
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node call in b.Nodes)
            {
                if (call.Dead || HelperOf(call) != HelperKind.ResolveICall) continue;
                if (IntArg(call, 0) is not { IsConst: true } name) continue;
                ulong nameAddress = (ulong)name.Imm;
                if (!_lazyTargets.TryGetValue(nameAddress, out Node? idiom))
                {
                    idiom = _fn.NewNode(Op.Idiom, VT.I64, null, name);
                    idiom.Imm = (long)IdiomKind.InternalCall;
                    idiom.Addr = call.Addr;
                    _lazyTargets[nameAddress] = idiom;
                }
                call.Dead = true;
                foreach (Node n in b.Nodes)
                {
                    if (n.Op != Op.Proj || !ReferenceEquals(n.In[0], call)) continue;
                    n.Dead = true;
                    if (n.Imm == CallResult.IntReturn)
                    {
                        (resolved ??= [])[n] = idiom;
                        _replace[n] = idiom;
                    }
                    else _replace[n] = _fn.NewNode(Op.Undef, n.Type, null);
                }
            }
        }
        if (resolved == null) return false;

        // The static that remembers the pointer, and every read of it.
        var statics = new Dictionary<ulong, Node>();
        foreach (Block b in _fn.Blocks)
            foreach (Node n in b.Nodes)
                if (n.Op == Op.Store && n.In[0].IsConst && resolved.TryGetValue(n.In[1], out Node? idiom))
                {
                    statics[(ulong)n.In[0].Imm] = idiom;
                    n.Dead = true;
                }
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node n in b.Nodes)
                if (n.Op == Op.Load && n.In[0].IsConst && statics.TryGetValue((ulong)n.In[0].Imm, out Node? idiom))
                {
                    _replace[n] = idiom;
                    n.Dead = true;
                }
            b.Nodes.RemoveAll(n => n.Dead);
        }
        ApplyReplacements();

        // "Has it been looked up yet?" has one answer now.
        foreach (Block p in _fn.Blocks)
        {
            Node? term = p.Terminator;
            if (term?.Op != Op.Branch || p.Succs.Count != 2 || ReferenceEquals(p.Succs[0], p.Succs[1])) continue;
            Node condition = term.In[0];
            if (condition.Op is not (Op.CmpEq or Op.CmpNe)) continue;
            Node x = condition.In[0], y = condition.In[1];
            bool isTarget = (IsLazyTarget(x) && y.IsConstValue(0)) || (IsLazyTarget(y) && x.IsConstValue(0));
            if (!isTarget) continue;
            Block taken = p.Succs[condition.Op == Op.CmpNe ? 0 : 1], skipped = p.Succs[condition.Op == Op.CmpNe ? 1 : 0];
            RemoveEdge(p, skipped);
            term.Op = Op.Jump;
            term.In = [];
            p.Succs.Clear();
            p.Succs.Add(taken);
        }
        foreach (Block b in _fn.Blocks) SimplifyPhis(b);
        _result.RegionsRemoved++;
        return true;
    }

    private static bool IsLazyTarget(Node n) => n.Op == Op.Idiom && (IdiomKind)n.Imm is IdiomKind.InternalCall or IdiomKind.PInvokeTarget;

    /// <summary>
    /// An interface call in tail position is compiled as the search with a jump at each end: one where the
    /// search found the interface (through the entry it found), one where it did not (through the runtime's
    /// lookup, already the InterfaceEntry idiom here). Both are the same call. When both pass the same receiver
    /// and arguments - compared for as many positions as the interface method has parameters - the search and
    /// its arm go; the lookup arm is the call.
    /// </summary>
    private bool MergeInterfaceTailCalls()
    {
        bool changed = false;
        foreach (Block slow in _fn.Blocks.ToList())
        {
            if (!_fn.Blocks.Contains(slow) || slow.Terminator is not { Op: Op.TailCall, Aux: CallInfo { Indirect: true } slowInfo } slowCall) continue;
            if (Resolve(slowCall.In[0]) is not { Op: Op.Load } entryLoad || Resolve(entryLoad.In[0]) is not { Op: Op.Idiom } idiom ||
                (IdiomKind)idiom.Imm != IdiomKind.InterfaceEntry || !ReferenceEquals(idiom.Block, slow)) continue;
            // How many argument positions the method uses: the receiver, then its parameters.
            if (Resolve(idiom.In[1]) is not { Op: Op.SlotValue } klass || !idiom.In[2].IsConst) continue;
            ulong slotAddress = (ulong)klass.Imm;
            TypeDef? type = program.Defaults.Slots.TryGetValue(slotAddress, out TypeDef? known) ? known
                : program.Model.ResolveUsageSlot(slotAddress) is { Kind: UsageKind.TypeInfo, Type: { } sig } ? sig.Definition : null;
            MethodDef? method = type?.Methods.FirstOrDefault(m => m.HasSlot && m.Slot == (int)idiom.In[2].UImm);
            if (method == null) continue;
            int positions = 1 + method.Parameters.Length;

            var cfg = new Cfg(_fn);
            foreach (Block fast in _fn.Blocks)
            {
                if (ReferenceEquals(fast, slow) || fast.Phis.Count != 0 ||
                    fast.Terminator is not { Op: Op.TailCall, Aux: CallInfo { Indirect: true } fastInfo } fastCall) continue;
                if (fastCall.In.Length != slowCall.In.Length || fastInfo.Slots.Count != slowInfo.Slots.Count) continue;
                // The same call: receiver, arguments, floating point registers and stack arguments.
                bool same = true;
                for (int i = 0; i < slowCall.In.Length && same; i++)
                {
                    ArgSlot a = slowInfo.Slots[i], b = fastInfo.Slots[i];
                    if (a != b) { same = false; break; }
                    // Position 0 is the receiver; each parameter after it travels in the integer or the floating
                    // point register of its position, by its type. The other register of a position holds leftovers.
                    bool IsFloating(int position) => position >= 1 && position <= method.Parameters.Length &&
                        method.Parameters[position - 1].Type is PrimitiveSig { Element: Rewind.Runtime.Il2CppTypeEnum.R4 or Rewind.Runtime.Il2CppTypeEnum.R8 };
                    // (Where integer and floating-point registers are counted apart, every slot is compared.)
                    bool compared = !_fn.Regs.SharedPositions ? a.Kind != ArgSlotKind.Target : a.Kind switch
                    {
                        ArgSlotKind.IntReg => a.Index < positions && !IsFloating(a.Index),
                        ArgSlotKind.FloatReg => a.Index / 4 < positions && IsFloating(a.Index / 4),
                        ArgSlotKind.Stack => a.Index + 4 < positions,
                        _ => false,
                    };
                    if (compared && !SameValue(Resolve(slowCall.In[i]), Resolve(fastCall.In[i]))) same = false;
                }
                if (!same) continue;
                // Besides the jump, the arm only computes.
                if (fast.Nodes.Any(n => !n.Dead && !ReferenceEquals(n, fastCall) && n.Op is Op.Store or Op.Call or Op.TailCall)) continue;

                // The search: everything between the block that starts it and the two arms.
                Block? guard = cfg.ImmediateDominator(slow);
                while (guard != null && !cfg.Dominates(guard, fast)) guard = cfg.ImmediateDominator(guard);
                if (guard == null || ReferenceEquals(guard, slow) || ReferenceEquals(guard, fast)) continue;
                var region = new HashSet<Block>();
                var work = new Stack<Block>(guard.Succs);
                bool closed = true;
                while (work.Count > 0 && closed)
                {
                    Block b = work.Pop();
                    if (ReferenceEquals(b, slow) || ReferenceEquals(b, fast) || !region.Add(b)) continue;
                    if (ReferenceEquals(b, guard) || region.Count > 16) { closed = false; break; }
                    foreach (Block next in b.Succs) work.Push(next);
                }
                if (!closed) continue;
                if (region.Any(b => b.Preds.Any(p => !region.Contains(p) && !ReferenceEquals(p, guard)) ||
                                    b.Nodes.Any(n => !n.Dead && n.Op is Op.Store or Op.Call or Op.TailCall))) continue;
                if (slow.Preds.Any(p => !region.Contains(p) && !ReferenceEquals(p, guard)) ||
                    fast.Preds.Any(p => !region.Contains(p) && !ReferenceEquals(p, guard)) || slow.Phis.Count != 0) continue;
                // Nothing computed in the search may be used by the surviving arm.
                var defined = new HashSet<Node>();
                foreach (Block b in region)
                {
                    defined.UnionWith(b.Phis);
                    defined.UnionWith(b.Nodes);
                }
                if (slow.Nodes.Any(n => !n.Dead && n.In.Any(input => defined.Contains(Resolve(input))))) continue;

                foreach (Block b in region.Append(fast))
                {
                    foreach (Node n in b.Nodes) n.Dead = true;
                    foreach (Node n in b.Phis) n.Dead = true;
                    b.Preds.Clear();
                    b.Succs.Clear();
                    _fn.Blocks.Remove(b);
                }
                slow.Preds.Clear();
                slow.Preds.Add(guard);
                MakeJump(guard, slow);
                for (int i = 0; i < _fn.Blocks.Count; i++) _fn.Blocks[i].Id = i;
                DeadCode.Run(_fn);
                _result.RegionsRemoved++;
                changed = true;
                break;
            }
        }
        return changed;
    }

    /// <summary>
    /// A call of a P/Invoke declaration whose wrapper was inlined: the function pointer cached in a static is
    /// looked up through il2cpp_codegen_resolve_pinvoke on first use. The static names the declaration (see
    /// PInvokeImports); the lookup and the cache collapse into the value they produce.
    /// </summary>
    private bool CollapsePInvokeTargets()
    {
        var idioms = new Dictionary<ulong, Node>();
        foreach (Block b in _fn.Blocks)
            foreach (Node call in b.Nodes)
            {
                if (call.Dead || HelperOf(call) != HelperKind.ResolvePInvoke || ResultOf(call) is not { } result) continue;
                Node? store = b.Nodes.FirstOrDefault(n => !n.Dead && n.Op == Op.Store && n.In[0].IsConst && ReferenceEquals(Resolve(n.In[1]), result));
                if (store == null) continue;
                ulong slot = (ulong)store.In[0].Imm;
                if (program.PInvokeAtSlot(slot) == null) continue;
                if (!idioms.TryGetValue(slot, out Node? idiom))
                {
                    idiom = _fn.NewNode(Op.Idiom, VT.I64, null, store.In[0]);
                    idiom.Imm = (long)IdiomKind.PInvokeTarget;
                    idiom.Addr = call.Addr;
                    idioms[slot] = idiom;
                }
                call.Dead = true;
                store.Dead = true;
                foreach (Node n in b.Nodes)
                {
                    if (n.Op != Op.Proj || !ReferenceEquals(n.In[0], call)) continue;
                    n.Dead = true;
                    _replace[n] = n.Imm == CallResult.IntReturn ? idiom : _fn.NewNode(Op.Undef, n.Type, null);
                }
            }
        if (idioms.Count == 0) return false;
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node n in b.Nodes)
                if (n.Op == Op.Load && n.In[0].IsConst && idioms.TryGetValue((ulong)n.In[0].Imm, out Node? idiom))
                {
                    _replace[n] = idiom;
                    n.Dead = true;
                }
            b.Nodes.RemoveAll(n => n.Dead);
        }
        ApplyReplacements();
        // "Has it been resolved yet?" has one answer now.
        foreach (Block p in _fn.Blocks)
        {
            Node? term = p.Terminator;
            if (term?.Op != Op.Branch || p.Succs.Count != 2 || ReferenceEquals(p.Succs[0], p.Succs[1])) continue;
            Node condition = term.In[0];
            if (condition.Op is not (Op.CmpEq or Op.CmpNe)) continue;
            Node x = condition.In[0], y = condition.In[1];
            if (!((IsLazyTarget(x) && y.IsConstValue(0)) || (IsLazyTarget(y) && x.IsConstValue(0)))) continue;
            Block taken = p.Succs[condition.Op == Op.CmpNe ? 0 : 1], skipped = p.Succs[condition.Op == Op.CmpNe ? 1 : 0];
            RemoveEdge(p, skipped);
            term.Op = Op.Jump;
            term.In = [];
            p.Succs.Clear();
            p.Succs.Add(taken);
        }
        foreach (Block b in _fn.Blocks) SimplifyPhis(b);
        _result.RegionsRemoved++;
        return true;
    }

    // ---- interface dispatch -------------------------------------------------------------------------------

    private static Node? ResultOf(Node call)
    {
        List<Node> nodes = call.Block!.Nodes;
        int at = nodes.IndexOf(call);
        for (int k = at + 1; k < nodes.Count && nodes[k].Op == Op.Proj && ReferenceEquals(nodes[k].In[0], call); k++)
            if (nodes[k].Imm == CallResult.IntReturn)
                return nodes[k];
        return null;
    }

    /// <summary>
    /// An interface call is compiled as a search: walk the object's class's list of implemented interfaces
    /// for the wanted one, compute where its methods start in the vtable, and fall back to a runtime helper
    /// when the walk finds nothing. All of that only ever produces one value - the vtable entry to call
    /// through - and changes nothing, so the whole region is replaced by that value.
    /// </summary>
    private bool CollapseInterfaceLookups()
    {
        bool changed = false;
        for (int guard = 0; guard < 64; guard++)
        {
            bool rewritten = false;
            foreach (Block slow in _fn.Blocks)
            {
                Node? call = null;
                foreach (Node n in slow.Nodes)
                    if (!n.Dead && HelperOf(n) == HelperKind.InterfaceInvokeDataSlow) { call = n; break; }
                if (call == null) continue;
                Node? obj = IntArg(call, 0), iface = IntArg(call, 1), slot = IntArg(call, 2);
                Node? result = ResultOf(call);
                if (obj == null || iface == null || slot == null || !slot.IsConst || result == null) continue;

                Node idiom = _fn.NewNode(Op.Idiom, VT.I64, null, Resolve(obj), Resolve(iface), slot);
                idiom.Imm = (long)IdiomKind.InterfaceEntry;
                idiom.Addr = call.Addr;

                if (TryCollapseRegion(slow, call, result, idiom))
                {
                    rewritten = changed = true;
                    break;
                }

                // No inline search around it: the helper call alone is the lookup.
                idiom.Block = slow;
                slow.Nodes.Insert(slow.Nodes.IndexOf(call), idiom);
                call.Dead = true;
                foreach (Node n in slow.Nodes)
                    if (n.Op == Op.Proj && ReferenceEquals(n.In[0], call))
                    {
                        n.Dead = true;
                        _replace[n] = n.Imm == CallResult.IntReturn ? idiom : _fn.NewNode(Op.Undef, n.Type, null);
                    }
                slow.Nodes.RemoveAll(n => n.Dead);
                ApplyReplacements();
                rewritten = changed = true;
                break;
            }
            if (!rewritten) break;
        }
        if (changed)
            for (int i = 0; i < _fn.Blocks.Count; i++) _fn.Blocks[i].Id = i;
        return changed;
    }

    private bool TryCollapseRegion(Block slow, Node call, Node result, Node idiom)
    {
        if (slow.Succs.Count != 1) return false;
        Block join = slow.Succs[0];
        int slowIndex = join.Preds.IndexOf(slow);
        Node? entry = null;
        foreach (Node phi in join.Phis)
            if (slowIndex >= 0 && slowIndex < phi.In.Length && ReferenceEquals(Resolve(phi.In[slowIndex]), result)) { entry = phi; break; }
        if (entry == null) return false;

        var cfg = new Cfg(_fn);
        Block? start = cfg.ImmediateDominator(join);
        if (start == null || ReferenceEquals(start, slow) || start.Terminator?.Op != Op.Branch) return false;

        // Everything between the start of the search and the point where its result is used.
        var region = new HashSet<Block>();
        var work = new Stack<Block>();
        foreach (Block s in start.Succs) work.Push(s);
        while (work.Count > 0)
        {
            Block b = work.Pop();
            if (ReferenceEquals(b, join) || !region.Add(b)) continue;
            foreach (Block s in b.Succs) work.Push(s);
        }
        if (region.Contains(start) || !region.Contains(slow) || region.Count > 16) return false;

        var defined = new HashSet<Node>();
        foreach (Block b in region)
        {
            foreach (Block p in b.Preds)
                if (!region.Contains(p) && !ReferenceEquals(p, start))
                    return false;
            foreach (Node n in b.Phis) defined.Add(n);
            foreach (Node n in b.Nodes)
            {
                if (n.Dead) continue;
                if (n.Op is Op.Store or Op.Return or Op.TailCall or Op.Switch or Op.Unreachable) return false;
                if (n.Op == Op.Call && !ReferenceEquals(n, call)) return false;
                defined.Add(n);
            }
        }
        // The search's intermediate values must not be used anywhere else.
        foreach (Block b in _fn.Blocks)
        {
            if (region.Contains(b)) continue;
            foreach (Node n in b.Nodes)
                foreach (Node input in n.In)
                    if (defined.Contains(input))
                        return false;
            if (!ReferenceEquals(b, join))
                foreach (Node phi in b.Phis)
                    foreach (Node input in phi.In)
                        if (defined.Contains(input))
                            return false;
        }

        var keep = new List<int>();
        var fromRegion = new List<int>();
        for (int i = 0; i < join.Preds.Count; i++)
            (region.Contains(join.Preds[i]) || ReferenceEquals(join.Preds[i], start) ? fromRegion : keep).Add(i);
        foreach (Node phi in join.Phis)
        {
            Node? outside = null;
            foreach (int i in fromRegion)
            {
                Node input = Resolve(phi.In[i]);
                if (!defined.Contains(input) && input.Op != Op.Undef) outside ??= input;
            }
            var inputs = new List<Node>();
            foreach (int i in keep) inputs.Add(phi.In[i]);
            inputs.Add(ReferenceEquals(phi, entry) ? idiom : outside ?? _fn.NewNode(Op.Undef, phi.Type, null));
            phi.In = inputs.ToArray();
        }
        var preds = new List<Block>();
        foreach (int i in keep) preds.Add(join.Preds[i]);
        preds.Add(start);
        join.Preds.Clear();
        join.Preds.AddRange(preds);

        idiom.Block = join;
        join.Nodes.Insert(0, idiom);
        MakeJump(start, join);
        _fn.Blocks.RemoveAll(region.Contains);
        SimplifyPhis(join);
        _result.RegionsRemoved++;
        return true;
    }

    /// <summary>
    /// Runtime lookups whose result nothing uses any more (the type test behind a removed array-store check,
    /// for instance) are not calls the program makes.
    /// </summary>
    private bool RemoveUnusedLookups()
    {
        Dictionary<Node, List<Node>>? uses = null;
        bool changed = false;
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node call in b.Nodes)
            {
                if (call.Dead || HelperOf(call) is not (HelperKind.IsInst or HelperKind.InterfaceInvokeDataSlow or HelperKind.StaticFieldsFor
                        or HelperKind.MethodIsStatic or HelperKind.MethodIsInterface or HelperKind.MethodIsGenericInstance or HelperKind.TypeGetObject
                        or HelperKind.GetGenericVirtualMethod or HelperKind.RgctxData or HelperKind.WouldBoxToNonNull)) continue;
                uses ??= DeadCode.Uses(_fn);
                bool used = false;
                foreach (Node n in b.Nodes)
                    if (n.Op == Op.Proj && ReferenceEquals(n.In[0], call) && uses.TryGetValue(n, out List<Node>? users) && users.Count != 0)
                        used = true;
                if (used) continue;
                call.Dead = true;
                foreach (Node n in b.Nodes)
                    if (n.Op == Op.Proj && ReferenceEquals(n.In[0], call)) n.Dead = true;
                changed = true;
            }
            b.Nodes.RemoveAll(n => n.Dead);
        }
        return changed;
    }

    // ---- implicit checks -----------------------------------------------------------------------------------

    /// <summary>Recognizes a block that does nothing but raise one of the exceptions IL raises implicitly.</summary>
    private ThrowKind ClassifyThrowBlock(Block b, out Node? first, out Node? second)
    {
        first = second = null;
        if (b.Terminator?.Op != Op.Unreachable) return ThrowKind.None;
        var calls = new List<Node>();
        foreach (Node n in b.Nodes)
        {
            if (n.Dead) continue;
            // Saves for exception handlers belong to the throw; where the check goes, the throwing call that
            // takes its place saves the same values.
            if (n.Op == Op.Store && n.Aux is not HandlerSave) return ThrowKind.None;
            if (n.Op == Op.Call) calls.Add(n);
        }
        if (calls.Count == 1)
        {
            switch (HelperOf(calls[0]))
            {
                case HelperKind.ThrowNullReference: return ThrowKind.NullReference;
                case HelperKind.ThrowIndexOutOfRange: return ThrowKind.IndexOutOfRange;
                case HelperKind.ThrowDivideByZero: return ThrowKind.DivideByZero;
                // The stack protector's failure (its guard overwritten): no part of the program's meaning.
                case HelperKind.StackCheckFail: return ThrowKind.StackCheck;
                case HelperKind.ThrowInvalidCast:
                    first = IntArg(calls[0], 0);
                    second = IntArg(calls[0], 1);
                    return ThrowKind.InvalidCast;
            }
        }
        else if (calls.Count == 2 && HelperOf(calls[1]) == HelperKind.Throw)
        {
            switch (HelperOf(calls[0]))
            {
                // Overflow checks are NOT implicit in ordinary IL arithmetic: they stay, as an explicit
                // "if (...) throw new OverflowException()", until a later pass can prove a checked operator.
                case HelperKind.GetArrayTypeMismatchException: return ThrowKind.ArrayTypeMismatch;
                case HelperKind.GetIndexOutOfRangeException: return ThrowKind.IndexOutOfRange;
            }
        }
        return ThrowKind.None;
    }

    private static Node PhiInputFor(Node value, Block block, Block pred)
    {
        if (value.Op != Op.Phi || !ReferenceEquals(value.Block, block)) return value;
        int index = block.Preds.IndexOf(pred);
        return index >= 0 && index < value.In.Length ? value.In[index] : value;
    }

    private void NoteOverflow(Node condition)
    {
        var pending = new Stack<Node>();
        pending.Push(condition);
        int budget = 16;
        while (pending.Count > 0 && budget-- > 0)
        {
            Node n = pending.Pop();
            Op op = n.Op switch
            {
                Op.AddOvfS or Op.AddOvfU => Op.Add,
                Op.SubOvfS or Op.SubOvfU => Op.Sub,
                Op.MulOvfS or Op.MulOvfU => Op.Mul,
                _ => Op.Const,
            };
            if (op != Op.Const) _result.CheckedArithmetic.Add((n.Op, n.In[0], n.In[1]));
            else if (n.Type == VT.I1)
                foreach (Node input in n.In) pending.Push(input);
        }
    }

    private bool RemoveGuards()
    {
        bool changed = false;
        foreach (Block p in _fn.Blocks)
        {
            Node? term = p.Terminator;
            if (term?.Op != Op.Branch || p.Succs.Count != 2) continue;
            for (int side = 0; side < 2; side++)
            {
                Block target = p.Succs[side], other = p.Succs[1 - side];
                if (ReferenceEquals(target, other) || Function.IsTryEntry(term.In[0])) continue;
                ThrowKind kind = ClassifyThrowBlock(target, out Node? a, out Node? b);
                if (kind == ThrowKind.None) continue;
                // A block that also throws on the other side is not a guard around normal flow.
                if (ClassifyThrowBlock(other, out _, out _) != ThrowKind.None) continue;

                if (kind == ThrowKind.InvalidCast && a != null && b != null)
                    _result.Casts.Add(new CastFact(p, PhiInputFor(a, target, p), PhiInputFor(b, target, p)));
                if (kind == ThrowKind.Overflow) NoteOverflow(term.In[0]);

                RemoveEdge(p, target);
                term.Op = Op.Jump;
                term.In = [];
                p.Succs.Clear();
                p.Succs.Add(other);
                _result.GuardsRemoved++;
                changed = true;
                break;
            }
        }
        return changed;
    }

    /// <summary>Drops the edge from <paramref name="pred"/> into <paramref name="block"/>, fixing phi inputs.</summary>
    private void RemoveEdge(Block pred, Block block)
    {
        int index = block.Preds.IndexOf(pred);
        if (index < 0) return;
        block.Preds.RemoveAt(index);
        foreach (Node phi in block.Phis)
        {
            if (index >= phi.In.Length) continue;
            var inputs = phi.In.ToList();
            inputs.RemoveAt(index);
            phi.In = inputs.ToArray();
        }
        SimplifyPhis(block);
    }

    private void SimplifyPhis(Block block)
    {
        bool any = false;
        foreach (Node phi in block.Phis)
        {
            Node? same = null;
            bool trivial = true;
            foreach (Node raw in phi.In)
            {
                Node input = Resolve(raw);
                if (ReferenceEquals(input, phi) || (same != null && SameValue(input, same))) continue;
                if (same != null) { trivial = false; break; }
                same = input;
            }
            if (!trivial || same == null) continue;
            _replace[phi] = same;
            phi.Dead = true;
            any = true;
        }
        if (!any) return;
        block.Phis.RemoveAll(n => n.Dead);
        ApplyReplacements();
    }

    private static readonly bool NoPhiCycles = Environment.GetEnvironmentVariable("REWIND_NO_PHI_CYCLES") != null;

    /// <summary>
    /// Merges that only pass one value around: each is given that value or another merge of the group, as a frame
    /// pointer kept in a register through a loop is. They are all that value. (SimplifyPhis looks at one merge at a
    /// time and does not see through the cycle; a stack address hidden that way escapes the stack analyses.)
    /// </summary>
    private bool CollapsePhiCycles()
    {
        if (NoPhiCycles) return false;
        bool any = false;
        foreach (Block b in _fn.Blocks)
            foreach (Node phi in b.Phis)
            {
                if (phi.Dead) continue;
                Node? value = null;
                var group = new HashSet<Node> { phi };
                var work = new Stack<Node>();
                work.Push(phi);
                bool single = true;
                while (single && work.Count > 0)
                    foreach (Node raw in work.Pop().In)
                    {
                        Node input = Resolve(raw);
                        if (input.Op == Op.Phi)
                        {
                            if (group.Add(input)) work.Push(input);
                            continue;
                        }
                        if (value == null) value = input;
                        else if (!SameValue(input, value))
                        {
                            single = false;
                            break;
                        }
                    }
                if (!single || value == null || group.Count < 2) continue;
                foreach (Node merged in group)
                {
                    _replace[merged] = value;
                    merged.Dead = true;
                }
                any = true;
            }
        if (!any) return false;
        foreach (Block b in _fn.Blocks) b.Phis.RemoveAll(n => n.Dead);
        ApplyReplacements();
        return true;
    }

    private bool RemoveUnreachable()
    {
        var reachable = new HashSet<Block>();
        var work = new Stack<Block>();
        work.Push(_fn.Entry);
        reachable.Add(_fn.Entry);
        while (work.Count > 0)
            foreach (Block s in work.Pop().Succs)
                if (reachable.Add(s))
                    work.Push(s);
        if (reachable.Count == _fn.Blocks.Count) return false;

        foreach (Block dead in _fn.Blocks.Where(b => !reachable.Contains(b)).ToList())
            foreach (Block s in dead.Succs)
                if (reachable.Contains(s))
                    RemoveEdge(dead, s);
        _fn.Blocks.RemoveAll(b => !reachable.Contains(b));
        for (int i = 0; i < _fn.Blocks.Count; i++) _fn.Blocks[i].Id = i;
        return true;
    }

    /// <summary>
    /// Compilers duplicate the epilogue, so "return x" often exists in several blocks. Blocks that consist of
    /// the same return are one block as far as the program's meaning goes.
    /// </summary>
    private bool MergeReturnBlocks()
    {
        bool changed = false;
        var canonical = new List<Block>();
        foreach (Block b in _fn.Blocks.ToList())
        {
            if (b.Phis.Count != 0 || ReferenceEquals(b, _fn.Entry)) continue;
            Node? ret = b.Terminator;
            if (ret?.Op != Op.Return) continue;
            // A return inside a try region stays there: entering a region other than through its start is not possible.
            if (b.Scope != -1) continue;
            // Besides the return itself the block may only compute: nothing with an effect, nothing that reads memory.
            bool only = true;
            foreach (Node n in b.Nodes)
                if (!n.Dead && !ReferenceEquals(n, ret) && (n.IsEffect || n.Op == Op.Proj)) { only = false; break; }
            if (!only) continue;

            Block? twin = null;
            foreach (Block c in canonical)
            {
                Node other = c.Terminator!;
                if (other.In.Length != ret.In.Length) continue;
                bool same = true;
                for (int i = 0; i < ret.In.Length; i++)
                    if (!SameValue(Resolve(other.In[i]), Resolve(ret.In[i]))) { same = false; break; }
                if (same) { twin = c; break; }
            }
            if (twin == null)
            {
                canonical.Add(b);
                continue;
            }
            // Redirect every edge into b to its twin.
            foreach (Block pred in b.Preds.ToList())
            {
                for (int i = 0; i < pred.Succs.Count; i++)
                    if (ReferenceEquals(pred.Succs[i], b))
                    {
                        pred.Succs[i] = twin;
                        twin.Preds.Add(pred);
                    }
            }
            b.Preds.Clear();
            _fn.Blocks.Remove(b);
            changed = true;
        }
        if (changed)
            for (int i = 0; i < _fn.Blocks.Count; i++) _fn.Blocks[i].Id = i;
        return changed;
    }

    // ---- control flow that no longer decides anything ------------------------------------------------------

    private static bool IsEmpty(Block b)
    {
        if (b.Phis.Count != 0) return false;
        foreach (Node n in b.Nodes)
            if (!n.Dead && !n.IsTerminator)
                return false;
        return b.Terminator?.Op == Op.Jump && b.Succs.Count == 1;
    }

    /// <summary>
    /// After the scaffolding is removed, many branches guard nothing: both paths reach the same block without
    /// doing anything (the remains of "if (!initialized) { ... }"). Such a branch becomes a plain jump.
    /// </summary>
    private bool CollapseEmptyConditionals()
    {
        bool changed = false;
        bool progress = true;
        while (progress)
        {
            progress = false;
            foreach (Block p in _fn.Blocks)
            {
                Node? term = p.Terminator;
                if (term?.Op != Op.Branch || p.Succs.Count != 2 || Function.IsTryEntry(term.In[0])) continue;
                Block a = p.Succs[0], b = p.Succs[1];

                if (ReferenceEquals(a, b))
                {
                    // Both edges already lead to the same block; keep a single edge.
                    if (!SameInputsOnDuplicateEdges(a, p)) continue;
                    RemoveEdge(p, a);
                    MakeJump(p, a);
                    progress = changed = true;
                    break;
                }

                Block? join = null;
                Block? viaA = null, viaB = null;
                if (IsEmpty(a) && a.Preds.Count == 1 && ReferenceEquals(a.Succs[0], b)) { join = b; viaA = a; }
                else if (IsEmpty(b) && b.Preds.Count == 1 && ReferenceEquals(b.Succs[0], a)) { join = a; viaB = b; }
                else if (IsEmpty(a) && IsEmpty(b) && a.Preds.Count == 1 && b.Preds.Count == 1 &&
                         ReferenceEquals(a.Succs[0], b.Succs[0])) { join = a.Succs[0]; viaA = a; viaB = b; }
                if (join == null || ReferenceEquals(join, p)) continue;

                // Edges into the join that originate from this branch.
                Block edgeA = viaA ?? p, edgeB = viaB ?? p;
                int ia = join.Preds.IndexOf(edgeA), ib = join.Preds.LastIndexOf(edgeB);
                if (ia < 0 || ib < 0 || ia == ib) continue;
                bool same = true;
                foreach (Node phi in join.Phis)
                    if (!Compatible(Resolve(phi.In[ia]), Resolve(phi.In[ib]))) { same = false; break; }
                if (!same) continue;

                // Keep one edge p -> join, drop the other and the empty blocks. Where one side carried an
                // undefined value (a register the skipped code clobbered), the defined one is the value.
                foreach (Node phi in join.Phis)
                {
                    var inputs = phi.In.ToList();
                    int keep = Math.Min(ia, ib), drop = Math.Max(ia, ib);
                    if (Resolve(inputs[keep]).Op == Op.Undef) inputs[keep] = inputs[drop];
                    inputs.RemoveAt(drop);
                    phi.In = inputs.ToArray();
                }
                join.Preds.RemoveAt(Math.Max(ia, ib));
                join.Preds[Math.Min(ia, ib)] = p;
                MakeJump(p, join);
                if (viaA != null) _fn.Blocks.Remove(viaA);
                if (viaB != null) _fn.Blocks.Remove(viaB);
                SimplifyPhis(join);
                _result.RegionsRemoved++;
                progress = changed = true;
                break;
            }
        }
        if (changed)
            for (int i = 0; i < _fn.Blocks.Count; i++) _fn.Blocks[i].Id = i;
        return changed;
    }

    /// <summary>
    /// True when two nodes must hold the same value: the same node, or the same pure operation applied to
    /// operands that are themselves the same. (Compilers compute one expression on both sides of a branch;
    /// seeing through that lets the branch be recognized as deciding nothing.)
    /// </summary>
    /// <summary>Two values that can stand for each other: equal, or one of them is undefined.</summary>
    private static bool Compatible(Node a, Node b) => a.Op == Op.Undef || b.Op == Op.Undef || SameValue(a, b);

    internal static bool SameValue(Node a, Node b, int depth = 0)
    {
        if (ReferenceEquals(a, b)) return true;
        if (depth > 12 || a.Op != b.Op || a.Type != b.Type || a.In.Length != b.In.Length) return false;
        switch (a.Op)
        {
            case Op.Const:
            case Op.SlotValue:
                return a.Imm == b.Imm;
            case Op.Load or Op.Call or Op.Proj or Op.Phi or Op.Param or Op.Undef or Op.Store:
                return false; // position-dependent or distinct by identity
        }
        if (a.IsTerminator) return false;
        if (a.Imm != b.Imm) return false;
        for (int i = 0; i < a.In.Length; i++)
            if (!SameValue(a.In[i], b.In[i], depth + 1))
                return false;
        return true;
    }

    private bool SameInputsOnDuplicateEdges(Block join, Block pred)
    {
        int first = join.Preds.IndexOf(pred), last = join.Preds.LastIndexOf(pred);
        if (first == last) return true;
        foreach (Node phi in join.Phis)
            if (!SameValue(Resolve(phi.In[first]), Resolve(phi.In[last])))
                return false;
        return true;
    }

    // ---- shapes compilers produce for simple source -----------------------------------------------------------

    /// <summary>True for operations that can be evaluated anywhere their operands are available.</summary>
    private static bool IsHoistable(Node n) =>
        !n.IsEffect && n.Op is not (Op.Proj or Op.Phi or Op.DivS or Op.DivU or Op.RemS or Op.RemU);

    /// <summary>
    /// One float comparison is often tested by two consecutive branches (the CPU reports "unordered" through a
    /// separate flag). Both branches are folded into a single condition; single branches whose condition is a
    /// roundabout combination of comparisons are rewritten in the shortest form.
    /// </summary>
    private bool MergeFloatBranches()
    {
        bool changed = false;
        bool progress = true;
        while (progress)
        {
            progress = false;
            foreach (Block p in _fn.Blocks)
            {
                Node? first = p.Terminator;
                if (first?.Op != Op.Branch || p.Succs.Count != 2) continue;
                Node? a = null, b = null;
                if (!FloatConditions.TryMask(first.In[0], ref a, ref b, out int mask1) || a == null || b == null) continue;

                bool merged = false;
                for (int side = 0; side < 2 && !merged; side++)
                {
                    Block q = p.Succs[side], shared = p.Succs[1 - side];
                    if (ReferenceEquals(q, shared) || ReferenceEquals(q, p) || q.Preds.Count != 1 || q.Phis.Count != 0 || q.Scope != p.Scope) continue;
                    Node? second = q.Terminator;
                    if (second?.Op != Op.Branch || q.Succs.Count != 2) continue;
                    int qSide = ReferenceEquals(q.Succs[0], shared) ? 0 : ReferenceEquals(q.Succs[1], shared) ? 1 : -1;
                    if (qSide < 0) continue;
                    Block other = q.Succs[1 - qSide];
                    if (ReferenceEquals(other, shared) || ReferenceEquals(other, q)) continue;
                    bool hoistable = true;
                    foreach (Node n in q.Nodes)
                        if (!n.Dead && !ReferenceEquals(n, second) && !IsHoistable(n)) { hoistable = false; break; }
                    if (!hoistable) continue;
                    Node? a2 = a, b2 = b;
                    if (!FloatConditions.TryMask(second.In[0], ref a2, ref b2, out int mask2)) continue;

                    int ip = shared.Preds.IndexOf(p), iq = shared.Preds.IndexOf(q);
                    if (ip < 0 || iq < 0) continue;
                    bool agree = true;
                    foreach (Node phi in shared.Phis)
                        if (!SameValue(Resolve(phi.In[ip]), Resolve(phi.In[iq]))) { agree = false; break; }
                    if (!agree) continue;

                    // Outcomes that lead to the shared block: directly from p, or through q.
                    int fromP = side == 1 ? mask1 : ~mask1 & FloatConditions.All;
                    int fromQ = qSide == 0 ? mask2 : ~mask2 & FloatConditions.All;
                    int toShared = fromP | fromQ;

                    // q's computations move up into p; q disappears.
                    int at = p.Nodes.Count - 1;
                    foreach (Node n in q.Nodes)
                    {
                        if (n.Dead || ReferenceEquals(n, second)) continue;
                        n.Block = p;
                        p.Nodes.Insert(at++, n);
                    }
                    _b.PositionBefore(p, first);
                    first.In = [FloatConditions.Canonical(_b, toShared, a, b)];
                    _b.InsertIndex = -1;

                    foreach (Node phi in shared.Phis)
                    {
                        var inputs = phi.In.ToList();
                        inputs.RemoveAt(iq);
                        phi.In = inputs.ToArray();
                    }
                    shared.Preds.RemoveAt(iq);
                    int io = other.Preds.IndexOf(q);
                    if (io >= 0) other.Preds[io] = p;
                    p.Succs.Clear();
                    p.Succs.Add(shared);
                    p.Succs.Add(other);
                    _fn.Blocks.Remove(q);
                    merged = true;
                }
                if (merged)
                {
                    progress = changed = true;
                    break;
                }

                if (!FloatConditions.IsSimple(first.In[0]))
                {
                    _b.PositionBefore(p, first);
                    first.In = [FloatConditions.Canonical(_b, mask1, a, b)];
                    _b.InsertIndex = -1;
                    changed = true;
                }
            }
        }
        if (changed)
            for (int i = 0; i < _fn.Blocks.Count; i++) _fn.Blocks[i].Id = i;
        return changed;
    }

    private static bool IsConstantReturn(Block b, out long value)
    {
        value = 0;
        if (b.Phis.Count != 0) return false;
        Node? ret = b.Terminator;
        if (ret?.Op != Op.Return || ret.In.Length != 1 || !ret.In[0].IsConst || ret.In[0].Type != VT.I8) return false;
        foreach (Node n in b.Nodes)
            if (!n.Dead && !ReferenceEquals(n, ret))
                return false;
        value = ret.In[0].Imm;
        return value is 0 or 1;
    }

    /// <summary>
    /// "if (c) return true; else return false;" is how a comparison result looks when the compiler chose
    /// branches over a flag-to-register instruction. It is the comparison itself being returned.
    /// </summary>
    private bool FoldBooleanReturns()
    {
        bool changed = false;
        foreach (Block p in _fn.Blocks.ToList())
        {
            Node? term = p.Terminator;
            if (term?.Op != Op.Branch || p.Succs.Count != 2) continue;
            Block whenTrue = p.Succs[0], whenFalse = p.Succs[1];
            if (ReferenceEquals(whenTrue, whenFalse)) continue;
            if (!IsConstantReturn(whenTrue, out long t) || !IsConstantReturn(whenFalse, out long f) || t == f) continue;

            Node condition = term.In[0];
            _b.PositionBefore(p, term);
            if (t == 0) condition = _b.NotBool(condition);
            Node value = _b.ZExt(condition, VT.I8);
            _b.InsertIndex = -1;
            RemoveEdge(p, whenTrue);
            RemoveEdge(p, whenFalse);
            p.Succs.Clear();
            term.Op = Op.Return;
            term.In = [value];
            changed = true;
        }
        return changed;
    }

    /// <summary>Joins a block with its only successor when that successor has no other way in.</summary>
    private bool MergeLinearBlocks()
    {
        bool changed = false;
        bool progress = true;
        while (progress)
        {
            progress = false;
            foreach (Block p in _fn.Blocks)
            {
                Node? jump = p.Terminator;
                if (jump?.Op != Op.Jump || p.Succs.Count != 1) continue;
                Block s = p.Succs[0];
                if (ReferenceEquals(s, p) || ReferenceEquals(s, _fn.Entry) || s.Preds.Count != 1 || s.Scope != p.Scope) continue;

                foreach (Node phi in s.Phis)
                {
                    if (phi.Dead) continue;
                    _replace[phi] = phi.In.Length > 0 ? Resolve(phi.In[0]) : _fn.NewNode(Op.Undef, phi.Type, null);
                    phi.Dead = true;
                }
                s.Phis.Clear();
                p.Nodes.RemoveAt(p.Nodes.Count - 1);
                foreach (Node n in s.Nodes)
                {
                    n.Block = p;
                    p.Nodes.Add(n);
                }
                p.End = s.End;
                p.Succs.Clear();
                p.Succs.AddRange(s.Succs);
                foreach (Block next in s.Succs)
                    for (int i = 0; i < next.Preds.Count; i++)
                        if (ReferenceEquals(next.Preds[i], s))
                            next.Preds[i] = p;
                s.Succs.Clear();
                s.Preds.Clear();
                _fn.Blocks.Remove(s);
                ApplyReplacements();
                progress = changed = true;
                break;
            }
        }
        if (changed)
            for (int i = 0; i < _fn.Blocks.Count; i++) _fn.Blocks[i].Id = i;
        return changed;
    }

    private static void MakeJump(Block p, Block target)
    {
        Node term = p.Terminator!;
        term.Op = Op.Jump;
        term.In = [];
        p.Succs.Clear();
        p.Succs.Add(target);
    }
}
