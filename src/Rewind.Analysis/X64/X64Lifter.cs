// Modified by xob0t (2026): stack arguments of calls to targets not yet known. See FORK.md.
using Iced.Intel;
using Rewind.Analysis.Ir;
using Rewind.Binary;

namespace Rewind.Analysis.X64;

/// <summary>Which argument positions a call target takes, so the lifter captures exactly those values.</summary>
public sealed class CallShape
{
    /// <summary>Total argument slots (register positions first, then stack).</summary>
    public int Count;
    /// <summary>Per position: passed in a float register (positions past the register area ignore this).</summary>
    public bool[] IsFloat = [];
    public bool[] IsDouble = [];
    /// <summary>Where the result arrives, when known.</summary>
    public CallReturn Returns = CallReturn.Unknown;
    /// <summary>
    /// For conventions that do not number every parameter in one sequence (AArch64): exactly the argument
    /// locations to capture, as call slots (a double takes lanes 0 and 1 of its register).
    /// </summary>
    public List<ArgSlot>? Slots;
    /// <summary>AArch64: how many integer (x0, x1) and floating-point (v0-v3) registers the result arrives in.</summary>
    public int IntResults = 1, FloatResults = 1;
}

/// <summary>Turns a machine's code into SSA IR, one function at a time.</summary>
public interface IMachineLifter
{
    Function Lift(ulong start);
    /// <summary>How often each instruction the lifter does not model was met.</summary>
    IReadOnlyDictionary<string, int> UnsupportedCounts { get; }
}

/// <summary>What a callee leaves in the return registers.</summary>
public enum CallReturn { Unknown, Void, Integer, Float, Double }

public interface ILiftContext : ICodeContext
{
    /// <summary>Argument layout of a direct call target, or null when unknown.</summary>
    CallShape? ShapeOf(ulong target);

    /// <summary>Return convention of a direct call target whose argument layout is not known.</summary>
    CallReturn ReturnOf(ulong target) => CallReturn.Unknown;

    /// <summary>The C++ exception tables of the function at <paramref name="start"/>, when it has any.</summary>
    CxxFunctionInfo? ExceptionInfo(ulong start) => null;

    /// <summary>
    /// True when a call to <paramref name="target"/> is better lifted as the target's code in place: generated
    /// code that is no method of the program (a C++ lambda such as a finally block's body, a private helper).
    /// </summary>
    bool ShouldInline(ulong target) => false;
}

/// <summary>
/// Translates x64 machine code into SSA IR. The translation is purely about what the instructions do; nothing
/// here knows about IL2CPP.
/// </summary>
public sealed class X64Lifter : IMachineLifter
{
    public IReadOnlyDictionary<string, int> UnsupportedCounts => Unsupported.ToDictionary(kv => kv.Key.ToString(), kv => kv.Value);

    /// <summary>VarSavedRsp: the function's stack pointer while one of its catch funclets runs on a stack of its own.</summary>
    public const int VarRsp = 4, VarXmm = 16, VarFlags = 80, VarGsBase = 81, VarSavedRsp = 82, VarCount = 83;

    /// <summary>Win64 integer argument registers as variable numbers: rcx, rdx, r8, r9.</summary>
    public static readonly int[] IntArgRegs = [1, 2, 8, 9];

    private static readonly VT[] VarTypes = MakeVarTypes();

    private static VT[] MakeVarTypes()
    {
        var types = new VT[VarCount];
        for (int i = 0; i < 16; i++) types[i] = VT.I64;
        for (int i = VarXmm; i < VarFlags; i++) types[i] = VT.I32;
        types[VarFlags] = VT.Flags;
        types[VarGsBase] = VT.I64;
        types[VarSavedRsp] = VT.I64;
        return types;
    }

    private readonly ILiftContext _ctx;
    private readonly NativeImage _image;
    private Function _fn = null!;
    private IrBuilder _b = null!;
    private SsaBuilder _ssa = null!;
    private Block _block = null!;
    private Dictionary<ulong, Block> _blockAt = null!;
    /// <summary>Set by cdq/cqo: rdx currently holds the sign extension of rax of this width.</summary>
    private int _rdxSignExtends;

    public Dictionary<Mnemonic, int> Unsupported { get; } = [];

    public X64Lifter(ILiftContext context)
    {
        _ctx = context;
        _image = context.Image;
    }

    // Exception handling: the synthetic blocks and what they stand for.
    private readonly Dictionary<Block, int> _gates = [];
    private readonly Dictionary<Block, (int Region, CxxHandler Handler, List<int> Lost)> _landings = [];
    private readonly HashSet<Block> _funcletReturns = [];
    // Inlined calls: the returns of the pasted code, and where each pasted block was called from.
    private readonly HashSet<Block> _inlineReturns = [];
    /// <summary>Pasted code that ends in a jump to code pasted after it.</summary>
    private readonly HashSet<Block> _tailJumps = [];
    /// <summary>
    /// The function's own last jump, when its target is pasted: the pasted code is the rest of the function. It
    /// returns for the function (so do the copies it jumps on to), on the stack the function had at the jump.
    /// </summary>
    private readonly HashSet<Block> _outerJumps = [];
    private readonly Dictionary<Block, int> _outerReturns = [];   // such a copy's way out -> the region of the function's jump
    // Every pasted copy runs on stack memory of its own: at run time the frames of two callees called one after
    // the other occupy the same addresses, which would make one's saved register and the other's local the
    // same memory here. (Possible because pasted code never looks at stack-passed arguments: see InlineBody.)
    private readonly Dictionary<Block, int> _siteRegion = [];     // call or jump into a copy -> the copy's region
    private readonly Dictionary<Block, int> _returnOwner = [];    // a copy's return -> the call it returns from
    private readonly Dictionary<int, Node> _savedRsp = [];        // call -> the caller's stack pointer
    private const int InlineStackBase = 0x100000, InlineStackStride = 0x10000;
    private readonly Dictionary<Block, ulong> _inlineSite = [];
    private readonly Dictionary<ulong, X64Cfg?> _inlineBodies = [];
    private const int InlineBudget = 4000, MaxInlineDepth = 3;

    public Function Lift(ulong start)
    {
        CxxFunctionInfo? eh = _ctx.ExceptionInfo(start);
        if (eh is { TryBlocks.Count: > 0 })
        {
            Function? withRegions = LiftCore(start, eh);
            if (withRegions != null) return withRegions;
            Function plain = LiftCore(start, null)!;
            plain.Problems.Add($"exception handling not reconstructed: {_ehFailure}");
            return plain;
        }
        return LiftCore(start, null)!;
    }

    /// <summary>Lifts one function; with exception tables, null when its try regions have a shape this does not handle.</summary>
    private Function? LiftCore(ulong start, CxxFunctionInfo? eh)
    {
        _gates.Clear();
        _landings.Clear();
        _funcletReturns.Clear();
        _inlineReturns.Clear();
        _tailJumps.Clear();
        _outerJumps.Clear();
        _outerReturns.Clear();
        _siteRegion.Clear();
        _returnOwner.Clear();
        _savedRsp.Clear();
        _inlineSite.Clear();
        // With try regions the prologue is a block of its own: a region may begin right after it, and its gate
        // must see the stack pointer the handler's frame is relative to.
        X64Cfg cfg = eh != null
            ? X64Cfg.Build(_ctx, start, eh.IpToState.Select(e => e.Address).Append(PrologueEnd(start)), eh.TryBlocks.SelectMany(t => t.Handlers).SelectMany(h => h.Continuations))
            : X64Cfg.Build(_ctx, start);
        _fn = new Function { Address = start, End = cfg.Limit };
        _deferredConditions.Clear();
        _fn.Problems.AddRange(cfg.Problems);
        _b = new IrBuilder(_fn);
        _ssa = new SsaBuilder(_fn, VarTypes);
        _blockAt = [];
        if (cfg.Blocks.Count == 0) return _fn;

        var rawOf = new Dictionary<Block, RawBlock>();
        int budget = InlineBudget;
        var sites = new List<(Block Site, ulong Target, Block? Next, ulong NextAddress, Dictionary<ulong, Block> Map, int Depth, ulong Origin)>();

        // Makes the blocks of a piece of code, cut after each call whose target is lifted in place; returns the
        // pieces that carry the raw blocks' own endings. Origin: the caller's call instruction pasted code stands
        // for (0 for the function's own code).
        List<(Block Block, RawBlock Raw)> Place(IEnumerable<RawBlock> raws, Dictionary<ulong, Block> map, int depth, ulong origin)
        {
            var tails = new List<(Block, RawBlock)>();
            Block Make(RawBlock piece)
            {
                Block block = NewBlock(piece.Start, piece.EndAddress, -1);
                map[piece.Start] = block;
                rawOf[block] = piece;
                if (origin != 0) _inlineSite[block] = origin;
                return block;
            }
            foreach (RawBlock raw in raws)
            {
                int from = 0, firstSite = sites.Count;
                for (int k = 0; k < raw.Instructions.Count && depth < MaxInlineDepth; k++)
                {
                    Instruction ins = raw.Instructions[k];
                    bool last = k == raw.Instructions.Count - 1;
                    if (ins.FlowControl != FlowControl.Call || ins.Op0Kind != OpKind.NearBranch64 || (last && raw.End != BlockEnd.FallThrough)) continue;
                    ulong target = ins.NearBranchTarget;
                    if (target == start || !_ctx.ShouldInline(target) || InlineBody(target, start) is not { } body) continue;
                    int size = body.Blocks.Sum(x => x.Instructions.Count);
                    if (size > budget) continue;
                    budget -= size;
                    var piece = new RawBlock { Start = raw.Instructions[from].IP, End = BlockEnd.InlinedCall };
                    piece.Instructions.AddRange(raw.Instructions.GetRange(from, k - from + 1));
                    Block site = Make(piece);
                    if (sites.Count > firstSite && sites[^1].Next == null && sites[^1].NextAddress == piece.Start) sites[^1] = sites[^1] with { Next = site };
                    sites.Add((site, target, null, ins.NextIP, map, depth, origin != 0 ? origin : ins.IP));
                    from = k + 1;
                }
                if (from == 0)
                {
                    tails.Add((Make(raw), raw));
                    continue;
                }
                if (from < raw.Instructions.Count)
                {
                    var rest = new RawBlock { Start = raw.Instructions[from].IP, End = raw.End, Successors = raw.Successors };
                    rest.Instructions.AddRange(raw.Instructions.GetRange(from, raw.Instructions.Count - from));
                    Block block = Make(rest);
                    tails.Add((block, rest));
                    sites[^1] = sites[^1] with { Next = block };
                }
            }
            return tails;
        }

        var outerOwner = new Dictionary<int, int>(); // a copy pasted at the function's own last jump (or at such a copy's) -> the first one's region
        foreach (var (block, raw) in Place(cfg.Blocks, _blockAt, 0, 0))
        {
            foreach (ulong successor in raw.Successors)
                if (_blockAt.TryGetValue(successor, out Block? target)) Link(block, target);
            // The function ends in a jump to a private helper: the helper's code is the rest of the function.
            if (raw.End != BlockEnd.TailCall || raw.Instructions.Count == 0 || Environment.GetEnvironmentVariable("REWIND_NO_TAIL_INLINE") != null) continue;
            Instruction leave = raw.Instructions[^1];
            if (leave.Op0Kind != OpKind.NearBranch64 || leave.NearBranchTarget == start || !_ctx.ShouldInline(leave.NearBranchTarget) ||
                InlineBody(leave.NearBranchTarget, start) is not { } rest) continue;
            int restSize = rest.Blocks.Sum(x => x.Instructions.Count);
            if (restSize > budget) continue;
            budget -= restSize;
            _tailJumps.Add(block);
            _outerJumps.Add(block);
            outerOwner[sites.Count] = sites.Count;
            sites.Add((block, leave.NearBranchTarget, null, 0, _blockAt, 0, leave.IP));
        }
        // Each inlined call gets its own copy of the callee's code, returning to the instruction after the call.
        // (Copies may contain inlined calls of their own: the list grows while it is worked through.)
        var owners = new Dictionary<int, int>(); // a jump from one copy into the next returns for the call that started the chain
        for (int i = 0; i < sites.Count; i++)
        {
            var (site, target, next, nextAddress, map, depth, origin) = sites[i];
            int owner = owners.GetValueOrDefault(i, i);
            bool outerSite = outerOwner.TryGetValue(i, out int outerRegion);
            _siteRegion[site] = i;
            Block? continuation = next ?? map.GetValueOrDefault(nextAddress);
            X64Cfg body = _inlineBodies[target]!;
            var copy = new Dictionary<ulong, Block>();
            foreach (var (block, raw) in Place(body.Blocks, copy, depth + 1, origin))
            {
                foreach (ulong successor in raw.Successors)
                    if (copy.TryGetValue(successor, out Block? to)) Link(block, to);
                if (raw.End is not (BlockEnd.Return or BlockEnd.TailCall or BlockEnd.IndirectTailCall)) continue;
                // A jump to code that is lifted in place too: that code returns where this copy would have.
                Instruction jump = raw.Instructions[^1];
                if (raw.End == BlockEnd.TailCall && jump.Op0Kind == OpKind.NearBranch64 && depth + 1 < MaxInlineDepth &&
                    jump.NearBranchTarget != start && _ctx.ShouldInline(jump.NearBranchTarget) && InlineBody(jump.NearBranchTarget, start) is { } next2 &&
                    next2.Blocks.Sum(x => x.Instructions.Count) is int size2 && size2 <= budget)
                {
                    budget -= size2;
                    _tailJumps.Add(block);
                    if (outerSite) outerOwner[sites.Count] = outerRegion;
                    else owners[sites.Count] = owner;
                    sites.Add((block, jump.NearBranchTarget, continuation, 0, copy, depth + 1, origin));
                    continue;
                }
                if (outerSite)
                {
                    // The rest of the function: its way out is the function's.
                    _outerReturns[block] = outerRegion;
                    continue;
                }
                _inlineReturns.Add(block);
                _returnOwner[block] = owner;
                if (continuation != null) Link(block, continuation);
            }
            Link(site, copy[target]);
        }

        if (eh != null && !PlanExceptionRegions(eh, rawOf, start)) return null;

        // A function whose first instruction is also a jump target (a loop that starts the function, or
        // self-recursion the compiler turned into a jump) needs a separate entry: the values the caller
        // passed and the values of the next iteration meet at that instruction.
        if (_fn.Blocks[0].Preds.Count != 0)
        {
            Block first = _fn.Blocks[0];
            var entry = new Block { Start = start, End = start };
            entry.Succs.Add(first);
            first.Preds.Insert(0, entry);
            _fn.Blocks.Insert(0, entry);
            for (int i = 0; i < _fn.Blocks.Count; i++) _fn.Blocks[i].Id = i;
        }

        // Reverse post-order, so a block is lifted after its forward predecessors.
        var order = new List<Block>();
        var visited = new HashSet<Block>();
        void Visit(Block b)
        {
            if (!visited.Add(b)) return;
            foreach (Block s in b.Succs) Visit(s);
            order.Add(b);
        }
        Visit(_fn.Entry);
        order.Reverse();

        // Blocks never reached from the entry (decoded only through a rejected path) carry no meaning. They go
        // before values are built: a merged value must not get an input for a way in that does not exist.
        _fn.Blocks.RemoveAll(b => !visited.Contains(b));
        foreach (Block b in _fn.Blocks) b.Preds.RemoveAll(p => !visited.Contains(p));
        for (int i = 0; i < _fn.Blocks.Count; i++) _fn.Blocks[i].Id = i;

        var filled = new HashSet<Block>();

        foreach (Block block in order)
        {
            if (block.Preds.All(filled.Contains)) _ssa.Seal(block);
            if (rawOf.TryGetValue(block, out RawBlock? rawBlock)) LiftBlock(block, rawBlock);
            else if (_gates.TryGetValue(block, out int region))
            {
                // "Was an exception raised in the region?" - the way into the handler.
                _block = block;
                _b.Current = block;
                _b.CurrentAddr = block.Start;
                Node raised = _b.Raw(Op.Idiom, VT.I1);
                raised.Imm = (long)IdiomKind.TryEntry;
                raised.Aux = region;
                _b.Raw(Op.Branch, VT.None, raised);
            }
            else if (_landings.TryGetValue(block, out var landing))
            {
                // Entering the catch funclet: it gets the function's frame (the establisher frame) in rdx and
                // runs on a stack of its own; the catch object slot holds a reference to the caught exception.
                _block = block;
                _b.Current = block;
                _b.CurrentAddr = block.Start;
                Node frame = Var(VarRsp);
                SetVar(VarSavedRsp, frame);
                SetVar(IntArgRegs[1], frame);
                Node wrapper = _b.Raw(Op.Idiom, VT.I64);
                wrapper.Imm = (long)IdiomKind.CaughtWrapper;
                wrapper.Aux = landing.Region;
                _b.Store(_b.Add(frame, _b.Const(VT.I64, landing.Handler.CatchObjectOffset)), wrapper);
                // Callee-saved registers the protected code changes hold what they held at the call that raised
                // the exception, which one path into the handler cannot say. (Saving them at every call is exact
                // but the compiler reuses those registers for unrelated values, which then share one variable.)
                foreach (int variable in landing.Lost)
                {
                    Node lost = _b.Raw(Op.Idiom, VarTypes[variable]);
                    lost.Imm = (long)IdiomKind.LostRegister;
                    lost.Aux = variable;
                    SetVar(variable, lost);
                }
                SetVar(VarRsp, _b.Add(frame, _b.Const(VT.I64, -0x10000 - 0x1000 * landing.Region)));
                _b.Raw(Op.Jump, VT.None);
            }
            else
            {
                // The synthetic entry: nothing but the step into the first real block.
                _block = block;
                _b.Current = block;
                _b.CurrentAddr = start;
                _b.Raw(Op.Jump, VT.None);
            }
            filled.Add(block);
            foreach (Block s in block.Succs)
                if (!_ssa.IsSealed(s) && s.Preds.All(filled.Contains))
                    _ssa.Seal(s);
        }
        foreach (Block block in _fn.Blocks) _ssa.Seal(block);
        SettleDeferredConditions();
        _ssa.Finish();

        return _fn;
    }

    // ---- exception regions -------------------------------------------------------------------------------------

    private Block NewBlock(ulong start, ulong end, int scope)
    {
        var block = new Block { Id = _fn.Blocks.Count, Start = start, End = end, Scope = scope };
        _fn.Blocks.Add(block);
        return block;
    }

    private static void Link(Block from, Block to)
    {
        from.Succs.Add(to);
        to.Preds.Add(from);
    }

    /// <summary>
    /// The code of a call target that can be lifted in place: one function, small, with plain control flow (no
    /// tail calls out, no calls back into the caller or itself).
    /// </summary>
    /// <summary>Points the stack pointer at the stack memory of pasted copy <paramref name="region"/>.</summary>
    private void EnterInlineStack(int region, long returnAddress)
    {
        Node current = Var(VarRsp);
        long displacement = -(InlineStackBase + (long)InlineStackStride * region);
        // Counted from the function's entry stack pointer, so no two copies can meet however they nest.
        Node entry = _fn.Params.TryGetValue(VarRsp, out Node? sp0)
            ? _b.Add(sp0, _b.Const(VT.I64, displacement))
            : _b.Add(current, _b.Const(VT.I64, displacement));
        SetVar(VarRsp, entry);
        _b.Store(entry, _b.Const(VT.I64, returnAddress));
    }

    /// <summary>
    /// True when code may look at its stack-passed arguments (the fifth argument and beyond), through the stack
    /// pointer or a register holding it. Such code is not pasted: its copy runs on stack memory of its own, where
    /// the caller's argument area is not.
    /// </summary>
    private static bool TouchesStackArguments(X64Cfg body)
    {
        long depth = 0;
        var aliases = new Dictionary<Register, long>(); // register -> what it holds, relative to the entry stack pointer
        bool Touches(in Instruction ins, long depthNow)
        {
            bool memory = false;
            for (int i = 0; i < ins.OpCount; i++) memory |= ins.GetOpKind(i) == OpKind.Memory;
            if (!memory || ins.MemoryBase == Register.RIP || ins.MemoryBase == Register.None) return false;
            long relative;
            if (ins.MemoryBase == Register.RSP) relative = (long)ins.MemoryDisplacement64 - depthNow;
            else if (aliases.TryGetValue(ins.MemoryBase, out long held)) relative = held + (long)ins.MemoryDisplacement64;
            else return false;
            return relative >= 0x28 || ins.MemoryIndex != Register.None;
        }
        foreach (Instruction ins in body.Blocks[0].Instructions)
        {
            if (Touches(ins, depth)) return true;
            Register dest = ins.OpCount > 0 && ins.Op0Kind == OpKind.Register ? ins.Op0Register.GetFullRegister() : Register.None;
            if (ins.Mnemonic == Mnemonic.Push) depth += 8;
            else if (ins.Mnemonic == Mnemonic.Pop) depth -= 8;
            else if (ins.Mnemonic == Mnemonic.Sub && dest == Register.RSP && ins.Op1Kind != OpKind.Register) depth += (long)ins.GetImmediate(1);
            else if (ins.Mnemonic == Mnemonic.Add && dest == Register.RSP && ins.Op1Kind != OpKind.Register) depth -= (long)ins.GetImmediate(1);
            else if (ins.Mnemonic == Mnemonic.Mov && dest != Register.None && ins.Op1Kind == OpKind.Register && ins.Op1Register == Register.RSP) aliases[dest] = -depth;
            else if (ins.Mnemonic == Mnemonic.Lea && dest != Register.None && ins.MemoryBase == Register.RSP && ins.MemoryIndex == Register.None)
                aliases[dest] = (long)ins.MemoryDisplacement64 - depth;
            else if (dest == Register.RSP) return true; // the stack pointer set some other way
            else if (dest != Register.None) aliases.Remove(dest);
        }
        foreach (RawBlock block in body.Blocks.Skip(1))
            foreach (Instruction ins in block.Instructions)
                if (Touches(ins, depth)) return true;
        return false;
    }

    private X64Cfg? InlineBody(ulong target, ulong caller)
    {
        if (_inlineBodies.TryGetValue(target, out X64Cfg? known)) return known;
        X64Cfg? body = X64Cfg.Build(_ctx, target);
        bool fits = body.Blocks.Count is > 0 and <= 64 && body.Problems.Count == 0 && body.Blocks[0].Start == target &&
                    body.Blocks.Sum(b => b.Instructions.Count) <= 300 && !TouchesStackArguments(body) &&
                    body.Blocks.Any(b => b.End is BlockEnd.Return or BlockEnd.TailCall or BlockEnd.IndirectTailCall) &&
                    !body.Blocks.SelectMany(b => b.Instructions).Any(i => i.FlowControl == FlowControl.Call && i.Op0Kind == OpKind.NearBranch64 &&
                                                                         (i.NearBranchTarget == target || i.NearBranchTarget == caller));
        return _inlineBodies[target] = fits ? body : null;
    }

    /// <summary>Callee-saved registers as variable numbers: rbx, rbp, rsi, rdi, r12-r15.</summary>
    internal static readonly int[] CalleeSaved = [3, 5, 6, 7, 12, 13, 14, 15];
    private static readonly bool NoTailStackFix = Environment.GetEnvironmentVariable("REWIND_NO_TAIL_STACK_ARGS") != null;

    /// <summary>The first instruction after the prologue (register homing, pushes, frame allocation).</summary>
    private ulong PrologueEnd(ulong start)
    {
        ReadOnlySpan<byte> span = _image.SpanToSectionEnd(start);
        var decoder = Decoder.Create(64, new ByteArrayCodeReader(span[..Math.Min(span.Length, 160)].ToArray()), start);
        ulong end = start;
        for (int i = 0; i < 20; i++)
        {
            decoder.Decode(out Instruction ins);
            if (ins.IsInvalid) break;
            bool part = (ins.Mnemonic == Mnemonic.Push && ins.Op0Kind == OpKind.Register) ||
                        (ins.Mnemonic == Mnemonic.Sub && ins.Op0Kind == OpKind.Register && ins.Op0Register == Register.RSP && ins.Op1Kind != OpKind.Register) ||
                        (ins.Mnemonic is Mnemonic.Mov or Mnemonic.Movaps or Mnemonic.Movdqa or Mnemonic.Movups && ins.Op0Kind == OpKind.Memory &&
                         ins.MemoryBase == Register.RSP && ins.Op1Kind == OpKind.Register) ||
                        (ins.Mnemonic == Mnemonic.Lea && ins.Op0Kind == OpKind.Register && ins.Op0Register == Register.RBP && ins.MemoryBase == Register.RSP);
            if (!part) break;
            end = ins.NextIP;
        }
        return end;
    }

    /// <summary>
    /// Builds the try regions of a function that has C++ exception tables: tags each block with its region, puts
    /// a gate before each region's entry and lifts the catch funclet behind it, so the handler is ordinary
    /// control flow that continues where the funclet says. False when the shape is not one this handles.
    /// </summary>
    private string? _ehFailure;

    private bool Fail(string why)
    {
        _ehFailure = why;
        return false;
    }

    private bool PlanExceptionRegions(CxxFunctionInfo eh, Dictionary<Block, RawBlock> rawOf, ulong start)
    {
        int count = eh.TryBlocks.Count;
        for (int t = 0; t < count; t++) _fn.TryRegions.Add(new TryRegionInfo { Index = t });
        int Span(int t) => eh.TryBlocks[t].TryHigh - eh.TryBlocks[t].TryLow;
        bool Covers(int t, int state) => state >= eh.TryBlocks[t].TryLow && state <= eh.TryBlocks[t].TryHigh;
        var parentBlocks = _fn.Blocks.ToList();
        var parentSet = new HashSet<Block>(parentBlocks);

        // Only calls can raise an exception, and the state table is exact only at calls: the state of a call
        // decides whether its block is protected. Blocks without calls go wherever the structure needs them.
        // Code lifted in place from a call has the state of that call.
        var callStates = new Dictionary<Block, List<int>>();
        foreach (Block b in parentBlocks)
        {
            if (!rawOf.TryGetValue(b, out RawBlock? raw)) continue;
            bool inlined = _inlineSite.TryGetValue(b, out ulong siteAddress);
            foreach (Instruction ins in raw.Instructions)
            {
                if (ins.FlowControl is not (FlowControl.Call or FlowControl.IndirectCall)) continue;
                if (raw.End == BlockEnd.InlinedCall && ins.IP == raw.Instructions[^1].IP) continue; // stands for the pasted code
                ulong at = inlined ? siteAddress : ins.IP;
                int before = eh.StateAt(at), after = inlined ? before : eh.StateAt(ins.NextIP);
                if (before != after) return Fail("a call sits on a state boundary");
                if (!callStates.TryGetValue(b, out List<int>? list)) callStates[b] = list = [];
                if (!list.Contains(before)) list.Add(before);
            }
        }

        Block? BlockAt(ulong address) => _blockAt.TryGetValue(address, out Block? b) && parentSet.Contains(b) ? b : null;
        var continuations = new List<Block>[count];
        for (int t = 0; t < count; t++)
        {
            continuations[t] = [];
            foreach (CxxHandler h in eh.TryBlocks[t].Handlers)
                foreach (ulong c in h.Continuations)
                    if (BlockAt(c) is { } block && !continuations[t].Contains(block)) continuations[t].Add(block);
        }
        var protectedCalls = new List<Block>[count];
        for (int t = 0; t < count; t++)
            protectedCalls[t] = callStates.Where(kv => kv.Value.Any(s => Covers(t, s))).Select(kv => kv.Key).ToList();

        // Control flow including the exceptional edges: from protected calls to where their handler continues.
        var succs = new Dictionary<Block, List<Block>>();
        var preds = new Dictionary<Block, List<Block>>();
        foreach (Block b in parentBlocks)
        {
            succs[b] = b.Succs.Where(parentSet.Contains).ToList();
            preds[b] = b.Preds.Where(parentSet.Contains).ToList();
        }
        for (int t = 0; t < count; t++)
            foreach (Block from in protectedCalls[t])
                foreach (Block to in continuations[t])
                    if (!succs[from].Contains(to))
                    {
                        succs[from].Add(to);
                        preds[to].Add(from);
                    }
        Dictionary<Block, Block> idom = Dominators(parentBlocks[0], succs, preds);
        bool Dominates(Block a, Block b)
        {
            for (Block? x = b; x != null; x = idom.TryGetValue(x, out Block? up) && !ReferenceEquals(up, x) ? up : null)
                if (ReferenceEquals(x, a)) return true;
            return false;
        }

        // Outermost first: a region's code is carved out of the scope its try statement is in.
        var entries = new Block?[count];
        foreach (int t in Enumerable.Range(0, count).OrderByDescending(Span))
        {
            List<Block> must = protectedCalls[t];
            if (must.Count == 0) continue; // nothing in the region can raise an exception: the handler never runs
            if (eh.TryBlocks[t].Handlers.Count != 1) return Fail("several catch clauses");
            if (must.Any(b => callStates[b].Any(s => !Covers(t, s)))) return Fail("a block mixes protected and unprotected calls");
            if (must.Any(b => !idom.ContainsKey(b))) continue; // unreachable code

            // The region starts where all its protected calls are dominated; it holds the blocks on the way
            // from there to them.
            Block entry = must[0];
            foreach (Block b in must.Skip(1))
                while (!Dominates(entry, b)) entry = idom[entry];
            var body = new HashSet<Block>(must) { entry };
            var work = new Stack<Block>(must);
            while (work.Count > 0)
            {
                Block b = work.Pop();
                if (ReferenceEquals(b, entry)) continue;
                foreach (Block p in preds[b])
                    if (!continuations[t].Contains(p) && Dominates(entry, p) && body.Add(p)) work.Push(p);
            }
            if (body.Any(continuations[t].Contains)) return Fail("the catch continues inside its own try region");
            if (body.Any(b => callStates.TryGetValue(b, out List<int>? states) && states.Any(s => !Covers(t, s))))
                return Fail("unprotected calls inside a try region");
            int outer = entry.Scope;
            if (body.Any(b => b.Scope != outer)) return Fail("try regions overlap");
            foreach (Block b in body)
                foreach (Block p in b.Preds)
                    if (!body.Contains(p) && !ReferenceEquals(b, entry)) return Fail("try region entered in several places");
            foreach (Block b in body) b.Scope = 2 * t;
            _fn.TryRegions[t].Outer = outer;
            entries[t] = entry;
        }

        bool Inside(Block b, int t)
        {
            for (int s = b.Scope, guard = 0; s >= 0 && guard < 64; guard++)
            {
                if (s == 2 * t) return true;
                s = _fn.TryRegions[s >> 1].Outer;
            }
            return false;
        }
        int Depth(int t)
        {
            int depth = 0;
            for (int s = _fn.TryRegions[t].Outer; s >= 0 && depth < 64; s = _fn.TryRegions[s >> 1].Outer) depth++;
            return depth;
        }
        for (int t = 0; t < count; t++)
            if (entries[t] != null)
                foreach (Block c in continuations[t])
                    if (Inside(c, t)) return Fail("the catch continues inside its own try region");

        // Innermost first: an inner region's gate becomes the start of the region around it.
        var info = new InstructionInfoFactory();
        foreach (int t in Enumerable.Range(0, count).Where(t => entries[t] != null).OrderByDescending(Depth))
        {
            CxxHandler handler = eh.TryBlocks[t].Handlers[0];
            if (handler.Funclet == 0 || handler.Continuations.Count == 0) return Fail("handler without code or continuation");
            int outer = _fn.TryRegions[t].Outer;
            var body = _fn.Blocks.Where(b => Inside(b, t)).ToList();
            Block? entry = null;
            var outside = new List<Block>();
            foreach (Block b in body)
                foreach (Block p in b.Preds)
                {
                    if (Inside(p, t)) continue;
                    if (entry != null && !ReferenceEquals(entry, b)) return Fail("try region entered in several places");
                    entry = b;
                    if (!outside.Contains(p)) outside.Add(p);
                }
            if (entry == null || entry.Start == start) return Fail("try region entry not found");

            if (_ctx.ExceptionInfo(handler.Funclet) is { TryBlocks.Count: > 0 }) return Fail("try inside a catch clause");
            X64Cfg funclet = X64Cfg.Build(_ctx, handler.Funclet);
            if (funclet.Blocks.Count == 0 || funclet.Problems.Count != 0 || funclet.Blocks[0].Start != handler.Funclet) return Fail("catch funclet not decoded");

            // Callee-saved registers the protected code writes: after an exception they hold whatever they held
            // at the faulting call, which a single path into the handler cannot say.
            var lost = new SortedSet<int>();
            foreach (Block b in body)
            {
                // Inlined callees restore the callee-saved registers they use before returning.
                if (!parentSet.Contains(b) || _inlineSite.ContainsKey(b) || !rawOf.TryGetValue(b, out RawBlock? raw)) continue;
                foreach (Instruction ins in raw.Instructions)
                    foreach (UsedRegister used in info.GetInfo(ins).GetUsedRegisters())
                    {
                        if (used.Access is not (OpAccess.Write or OpAccess.ReadWrite or OpAccess.CondWrite or OpAccess.ReadCondWrite)) continue;
                        Register r = used.Register;
                        if (r.IsGPR() && !IsHighByte(r) && Array.IndexOf(CalleeSaved, GprVar(r)) >= 0) lost.Add(GprVar(r));
                        else if ((r.IsXMM() || r.IsYMM() || r.IsZMM()) && r.GetNumber() is >= 6 and < 16)
                            for (int lane = 0; lane < 4; lane++) lost.Add(VarXmm + r.GetNumber() * 4 + lane);
                    }
            }

            Block gate = NewBlock(entry.Start, entry.Start, outer);
            Block landing = NewBlock(handler.Funclet, handler.Funclet, 2 * t + 1);
            foreach (Block p in outside)
                for (int i = 0; i < p.Succs.Count; i++)
                    if (ReferenceEquals(p.Succs[i], entry))
                    {
                        p.Succs[i] = gate;
                        gate.Preds.Add(p);
                    }
            entry.Preds.RemoveAll(outside.Contains);
            Link(gate, landing);
            Link(gate, entry);

            var funcletBlocks = new Dictionary<ulong, Block>();
            var rawAt = new Dictionary<ulong, RawBlock>();
            foreach (RawBlock raw in funclet.Blocks)
            {
                if (_blockAt.ContainsKey(raw.Start)) return Fail("catch funclet overlaps the function");
                Block block = NewBlock(raw.Start, raw.EndAddress, 2 * t + 1);
                _blockAt[raw.Start] = block;
                funcletBlocks[raw.Start] = block;
                rawAt[raw.Start] = raw;
                rawOf[block] = raw;
            }
            foreach (RawBlock raw in funclet.Blocks)
            {
                Block block = funcletBlocks[raw.Start];
                foreach (ulong successor in raw.Successors)
                    if (funcletBlocks.TryGetValue(successor, out Block? target)) Link(block, target);
                if (raw.End != BlockEnd.Return) continue;
                if (ContinuationOf(raw, handler, rawAt, funclet) is not ulong continuation || BlockAt(continuation) is not { } next ||
                    Inside(next, t)) return Fail("catch continuation not found");
                _funcletReturns.Add(block);
                Link(block, next);
            }
            Link(landing, funcletBlocks[handler.Funclet]);
            _gates[gate] = t;
            _landings[landing] = (t, handler, lost.ToList());
            _fn.TryRegions[t].Funclet = handler.Funclet;
        }
        return true;
    }

    /// <summary>Immediate dominators (Cooper, Harvey, Kennedy) over the given edges; unreachable blocks are absent.</summary>
    internal static Dictionary<Block, Block> Dominators(Block entry, Dictionary<Block, List<Block>> succs, Dictionary<Block, List<Block>> preds)
    {
        var order = new List<Block>();
        var seen = new HashSet<Block>();
        var stack = new Stack<(Block Block, int Next)>();
        seen.Add(entry);
        stack.Push((entry, 0));
        while (stack.Count > 0)
        {
            var (b, next) = stack.Pop();
            List<Block> out_ = succs[b];
            if (next < out_.Count)
            {
                stack.Push((b, next + 1));
                if (seen.Add(out_[next])) stack.Push((out_[next], 0));
            }
            else order.Add(b);
        }
        order.Reverse(); // reverse post-order
        var index = new Dictionary<Block, int>();
        for (int i = 0; i < order.Count; i++) index[order[i]] = i;
        var idom = new Dictionary<Block, Block> { [entry] = entry };
        Block Intersect(Block a, Block b)
        {
            while (!ReferenceEquals(a, b))
            {
                while (index[a] > index[b]) a = idom[a];
                while (index[b] > index[a]) b = idom[b];
            }
            return a;
        }
        bool changed = true;
        while (changed)
        {
            changed = false;
            foreach (Block b in order.Skip(1))
            {
                Block? best = null;
                foreach (Block p in preds[b])
                    if (idom.ContainsKey(p) && index.ContainsKey(p))
                        best = best == null ? p : Intersect(p, best);
                if (best != null && (!idom.TryGetValue(b, out Block? old) || !ReferenceEquals(old, best)))
                {
                    idom[b] = best;
                    changed = true;
                }
            }
        }
        return idom;
    }

    /// <summary>
    /// Where a catch funclet's return continues: the funclet returns an index into the handler's continuation
    /// list (in rax), set on the way to its return.
    /// </summary>
    private static ulong? ContinuationOf(RawBlock ret, CxxHandler handler, Dictionary<ulong, RawBlock> rawAt, X64Cfg funclet)
    {
        List<ulong> continuations = handler.Continuations;
        if (continuations.Count == 1) return continuations[0];
        RawBlock? block = ret;
        for (int step = 0; block != null && step < 8; step++)
        {
            for (int i = block.Instructions.Count - 1; i >= 0; i--)
            {
                Instruction ins = block.Instructions[i];
                if (ins.OpCount == 0 || ins.Op0Kind != OpKind.Register || ins.Op0Register is not (Register.RAX or Register.EAX)) continue;
                if (ins.Mnemonic == Mnemonic.Mov && ins.Op1Kind is OpKind.Immediate32 or OpKind.Immediate32to64 or OpKind.Immediate64)
                {
                    ulong value = ins.GetImmediate(1);
                    if (value < (ulong)continuations.Count) return continuations[(int)value];
                    return continuations.Contains(value) ? value : null;
                }
                if (ins.Mnemonic == Mnemonic.Xor && ins.Op1Kind == OpKind.Register && ins.Op1Register == ins.Op0Register) return continuations[0];
                if (ins.Mnemonic == Mnemonic.Lea && ins.IsIPRelativeMemoryOperand)
                    return continuations.Contains(ins.IPRelativeMemoryAddress) ? ins.IPRelativeMemoryAddress : null;
                return null;
            }
            // Nothing set rax here: look in the only block that leads here.
            RawBlock? only = null;
            int ways = 0;
            foreach (RawBlock other in funclet.Blocks)
                if (other.Successors.Contains(block.Start) || (other.End == BlockEnd.FallThrough && other.EndAddress == block.Start))
                {
                    only = other;
                    ways++;
                }
            block = ways == 1 ? only : null;
        }
        return null;
    }

    // ---- variables ---------------------------------------------------------------------------------------------

    private Node Var(int variable) => _ssa.Read(variable, _block);
    private void SetVar(int variable, Node value) => _ssa.Write(variable, _block, value);

    private static int GprVar(Register r) => r.GetFullRegister().GetNumber();

    private static bool IsHighByte(Register r) => r is Register.AH or Register.BH or Register.CH or Register.DH;

    private static VT RegType(Register r) => r.GetSize() switch
    {
        1 => VT.I8, 2 => VT.I16, 4 => VT.I32, _ => VT.I64,
    };

    private Node ReadReg(Register r)
    {
        if (r == Register.RIP) return _b.Const(VT.I64, (long)_b.CurrentAddr);
        if (IsHighByte(r))
        {
            Node full = Var(r switch { Register.AH => 0, Register.CH => 1, Register.DH => 2, _ => 3 });
            return _b.Trunc(_b.Shift(Op.ShrU, full, _b.Const(VT.I8, 8)), VT.I8);
        }
        return _b.Trunc(Var(GprVar(r)), RegType(r));
    }

    private void WriteReg(Register r, Node value)
    {
        if (IsHighByte(r))
        {
            int v = r switch { Register.AH => 0, Register.CH => 1, Register.DH => 2, _ => 3 };
            Node old = Var(v);
            Node shifted = _b.Shift(Op.Shl, _b.ZExt(value, VT.I64), _b.Const(VT.I8, 8));
            SetVar(v, _b.Or(_b.And(old, _b.Const(VT.I64, ~0xFF00L)), shifted));
            NoteWrite(v);
            return;
        }
        int variable = GprVar(r);
        switch (r.GetSize())
        {
            case 8:
                SetVar(variable, value);
                break;
            case 4:
                SetVar(variable, _b.ZExt(value, VT.I64)); // 32-bit writes clear the upper half
                break;
            case 2:
                SetVar(variable, _b.Or(_b.And(Var(variable), _b.Const(VT.I64, ~0xFFFFL)), _b.ZExt(value, VT.I64)));
                break;
            default:
                SetVar(variable, _b.Or(_b.And(Var(variable), _b.Const(VT.I64, ~0xFFL)), _b.ZExt(value, VT.I64)));
                break;
        }
        NoteWrite(variable);
    }

    private void NoteWrite(int variable)
    {
        if (variable is 0 or 2) _rdxSignExtends = 0;
    }

    private static int LaneVar(Register xmm, int lane) => VarXmm + (xmm.GetNumber()) * 4 + lane;
    private Node Lane(Register xmm, int lane) => Var(LaneVar(xmm, lane));
    private void SetLane(Register xmm, int lane, Node value) => SetVar(LaneVar(xmm, lane), value);

    // ---- operands ----------------------------------------------------------------------------------------------

    private Node Address(in Instruction ins)
    {
        if (ins.IsIPRelativeMemoryOperand) return _b.Const(VT.I64, (long)ins.IPRelativeMemoryAddress);
        Node? address = null;
        if (ins.MemoryBase != Register.None) address = _b.ZExt(ReadReg(ins.MemoryBase), VT.I64);
        if (ins.MemoryIndex != Register.None)
        {
            Node index = _b.ZExt(ReadReg(ins.MemoryIndex), VT.I64);
            int scale = ins.MemoryIndexScale;
            if (scale != 1) index = _b.Mul(index, _b.Const(VT.I64, scale));
            address = address == null ? index : _b.Add(address, index);
        }
        long displacement = (long)ins.MemoryDisplacement64;
        address = address == null ? _b.Const(VT.I64, displacement) : _b.Add(address, _b.Const(VT.I64, displacement));
        if (ins.MemorySegment == Register.GS && ins.SegmentPrefix == Register.GS)
            address = _b.Add(Var(VarGsBase), address);
        return address;
    }

    /// <summary>Loads from memory, folding reads of read-only image data into constants.</summary>
    private Node LoadAt(Node address, VT type)
    {
        if (address.IsConst)
        {
            ulong va = (ulong)address.Imm;
            ImageSection? section = _image.SectionAt(va);
            if (section != null && !section.IsWritable && !section.IsExecutable && _image.IsMapped(va, type.Bytes()))
            {
                long raw = type.Bytes() switch
                {
                    1 => _image.U8(va),
                    2 => _image.U16(va),
                    4 => _image.U32(va),
                    _ => (long)_image.U64(va),
                };
                return _b.Const(type, raw);
            }
        }
        return _b.Load(address, type);
    }

    private static bool IsImmediate(OpKind kind) => kind is OpKind.Immediate8 or OpKind.Immediate16 or OpKind.Immediate32
        or OpKind.Immediate64 or OpKind.Immediate8to16 or OpKind.Immediate8to32 or OpKind.Immediate8to64 or OpKind.Immediate32to64;

    /// <summary>Type of an integer operand, from the register or the memory operand size.</summary>
    private static VT OperandType(in Instruction ins, int op)
    {
        OpKind kind = ins.GetOpKind(op);
        if (kind == OpKind.Register) return RegType(ins.GetOpRegister(op));
        if (kind == OpKind.Memory)
            return ins.MemorySize.GetSize() switch { 1 => VT.I8, 2 => VT.I16, 4 => VT.I32, 8 => VT.I64, _ => VT.I64 };
        return VT.I64;
    }

    private Node ReadOp(in Instruction ins, int op, VT type, Node? address = null)
    {
        OpKind kind = ins.GetOpKind(op);
        if (kind == OpKind.Register) return ReadReg(ins.GetOpRegister(op));
        if (kind == OpKind.Memory) return LoadAt(address ?? Address(ins), type);
        if (IsImmediate(kind)) return _b.Const(type, (long)ins.GetImmediate(op));
        throw new NotSupportedException($"operand kind {kind}");
    }

    private void WriteOp(in Instruction ins, int op, Node value, Node? address = null)
    {
        if (ins.GetOpKind(op) == OpKind.Register) WriteReg(ins.GetOpRegister(op), value);
        else _b.Store(address ?? Address(ins), value);
    }

    // ---- flags -------------------------------------------------------------------------------------------------

    private void SetFlags(FlagKind kind, Node a, Node b, Node? result = null)
    {
        Node f = _fn.NewNode(Op.Flags, VT.Flags, null, result == null ? [a, b] : [a, b, result]);
        f.Imm = (long)kind;
        SetVar(VarFlags, f);
    }

    private const int FlagBitTest = 100;

    private Node Zero(Node like) => _b.Const(like.Type, 0);

    private Node BoolOr(Node a, Node b) => a.IsConst ? (a.Imm != 0 ? a : b) : b.IsConst ? (b.Imm != 0 ? b : a) : _b.Raw(Op.Or, VT.I1, a, b);
    private Node BoolAnd(Node a, Node b) => a.IsConst ? (a.Imm != 0 ? b : a) : b.IsConst ? (b.Imm != 0 ? a : b) : _b.Raw(Op.And, VT.I1, a, b);

    /// <summary>Expresses an x86 condition code over the operands of the instruction that last set the flags.</summary>
    private Node Condition(ConditionCode cc)
    {
        Node f = Var(VarFlags);
        if (f.Op == Op.Flags) return ConditionOf(cc, f);
        if (f.Op == Op.Phi && ConditionFromPhi(cc, f) is { } merged) return merged;
        Node opaque = Opaque(cc, f);
        // At the head of a loop the flags of the way back are not known yet: asked again when they are.
        if (f.Op == Op.Phi) _deferredConditions.Add((opaque, cc, f, _fn.Problems.Count - 1));
        return opaque;
    }

    /// <summary>Conditions on flags that several ways in bring, left open because one of the ways was not lifted yet.</summary>
    private readonly List<(Node Placeholder, ConditionCode Code, Node Flags, int Problem)> _deferredConditions = [];

    /// <summary>
    /// The open conditions, once every block is lifted. The compiler tests a loop's condition at its foot and
    /// lets the head use the same flags for another test ("i &lt; count" signed, then the bounds check
    /// "i &lt; count" unsigned): at the head the flags come from the compare before the loop and from the one at
    /// its foot. With both known, the condition is worked out on each way in and merged, like any other.
    /// </summary>
    private void SettleDeferredConditions()
    {
        if (_deferredConditions.Count == 0) return;
        var settled = new Dictionary<Node, Node>();
        var solved = new List<int>();
        Block savedBlock = _block;
        foreach (var (placeholder, cc, flags, problem) in _deferredConditions)
        {
            Node now = _ssa.Resolve(flags);
            Block home = placeholder.Block!;
            int before = _fn.Problems.Count;
            Node? condition = null;
            if (now.Op == Op.Flags)
            {
                // One compare reaches it after all.
                _block = home;
                _b.PositionBefore(home, placeholder);
                condition = ConditionOf(cc, now);
                _b.InsertIndex = -1;
            }
            else if (now.Op == Op.Phi && !now.Dead)
            {
                _b.CurrentAddr = placeholder.Addr;
                condition = ConditionFromPhi(cc, now);
            }
            if (condition == null || _fn.Problems.Count != before)
            {
                _fn.Problems.RemoveRange(before, _fn.Problems.Count - before);
                continue;
            }
            settled[placeholder] = condition;
            solved.Add(problem);
        }
        _block = savedBlock;
        _deferredConditions.Clear();
        if (settled.Count == 0) return;
        foreach (Block b in _fn.Blocks)
        {
            foreach (Node n in b.Phis)
                for (int i = 0; i < n.In.Length; i++)
                    if (settled.TryGetValue(n.In[i], out Node? condition))
                        n.In[i] = condition;
            foreach (Node n in b.Nodes)
                for (int i = 0; i < n.In.Length; i++)
                    if (settled.TryGetValue(n.In[i], out Node? condition))
                        n.In[i] = condition;
            b.Nodes.RemoveAll(n =>
            {
                if (!settled.ContainsKey(n)) return false;
                n.Dead = true;
                return true;
            });
        }
        solved.Sort();
        for (int i = solved.Count - 1; i >= 0; i--)
            if (solved[i] < _fn.Problems.Count)
                _fn.Problems.RemoveAt(solved[i]);
    }

    /// <summary>
    /// Flags that reach a block from several predecessors: evaluate the condition at the end of each
    /// predecessor, where the flag-setting operands are known, and merge the results.
    /// </summary>
    private Node? ConditionFromPhi(ConditionCode cc, Node phi)
    {
        Block home = phi.Block!;
        if (phi.In.Length == 0 || phi.In.Length != home.Preds.Count) return null;
        var flags = new Node[phi.In.Length];
        for (int i = 0; i < flags.Length; i++)
        {
            flags[i] = _ssa.Resolve(phi.In[i]);
            if (flags[i].Op != Op.Flags) return null;
        }

        Block savedBlock = _block;
        ulong savedAddr = _b.CurrentAddr;
        int problemsBefore = _fn.Problems.Count;
        var conditions = new Node[flags.Length];
        try
        {
            _b.InsertBeforeTerminator = true;
            for (int i = 0; i < flags.Length; i++)
            {
                Block pred = home.Preds[i];
                _block = pred;
                _b.Current = pred;
                conditions[i] = ConditionOf(cc, flags[i]);
            }
        }
        finally
        {
            _b.InsertBeforeTerminator = false;
            _block = savedBlock;
            _b.Current = savedBlock;
            _b.CurrentAddr = savedAddr;
        }
        if (_fn.Problems.Count != problemsBefore) return null;

        Node merged = _fn.NewNode(Op.Phi, VT.I1, home, conditions);
        home.Phis.Add(merged);
        return merged;
    }

    private Node ConditionOf(ConditionCode cc, Node f)
    {
        Node a = f.In[0], b = f.In[1];
        Node? r = f.In.Length > 2 ? f.In[2] : null;

        switch ((int)f.Imm)
        {
            case (int)FlagKind.Sub:
                switch (cc)
                {
                    case ConditionCode.e: return _b.Cmp(Op.CmpEq, a, b);
                    case ConditionCode.ne: return _b.Cmp(Op.CmpNe, a, b);
                    case ConditionCode.l: return _b.Cmp(Op.CmpLtS, a, b);
                    case ConditionCode.ge: return _b.Cmp(Op.CmpLeS, b, a);
                    case ConditionCode.le: return _b.Cmp(Op.CmpLeS, a, b);
                    case ConditionCode.g: return _b.Cmp(Op.CmpLtS, b, a);
                    case ConditionCode.b: return _b.Cmp(Op.CmpLtU, a, b);
                    case ConditionCode.ae: return _b.Cmp(Op.CmpLeU, b, a);
                    case ConditionCode.be: return _b.Cmp(Op.CmpLeU, a, b);
                    case ConditionCode.a: return _b.Cmp(Op.CmpLtU, b, a);
                    case ConditionCode.s: return _b.Cmp(Op.CmpLtS, r ?? _b.Sub(a, b), Zero(a));
                    case ConditionCode.ns: return _b.Cmp(Op.CmpLeS, Zero(a), r ?? _b.Sub(a, b));
                    case ConditionCode.o: return _b.Raw(Op.SubOvfS, VT.I1, a, b);
                    case ConditionCode.no: return _b.NotBool(_b.Raw(Op.SubOvfS, VT.I1, a, b));
                }
                break;

            case (int)FlagKind.Test:
            case (int)FlagKind.Logic:
            {
                Node v = (FlagKind)f.Imm == FlagKind.Logic ? r! : ReferenceEquals(a, b) ? a : _b.And(a, b);
                switch (cc)
                {
                    case ConditionCode.e or ConditionCode.be: return _b.Cmp(Op.CmpEq, v, Zero(v));
                    case ConditionCode.ne or ConditionCode.a: return _b.Cmp(Op.CmpNe, v, Zero(v));
                    case ConditionCode.s or ConditionCode.l: return _b.Cmp(Op.CmpLtS, v, Zero(v));
                    case ConditionCode.ns or ConditionCode.ge: return _b.Cmp(Op.CmpLeS, Zero(v), v);
                    case ConditionCode.le: return _b.Cmp(Op.CmpLeS, v, Zero(v));
                    case ConditionCode.g: return _b.Cmp(Op.CmpLtS, Zero(v), v);
                    case ConditionCode.b or ConditionCode.o: return _b.Const(VT.I1, 0);
                    case ConditionCode.ae or ConditionCode.no: return _b.Const(VT.I1, 1);
                }
                break;
            }

            case (int)FlagKind.Add:
                switch (cc)
                {
                    case ConditionCode.e: return _b.Cmp(Op.CmpEq, r!, Zero(r!));
                    case ConditionCode.ne: return _b.Cmp(Op.CmpNe, r!, Zero(r!));
                    case ConditionCode.s: return _b.Cmp(Op.CmpLtS, r!, Zero(r!));
                    case ConditionCode.ns: return _b.Cmp(Op.CmpLeS, Zero(r!), r!);
                    case ConditionCode.b: return _b.Raw(Op.AddOvfU, VT.I1, a, b);
                    case ConditionCode.ae: return _b.NotBool(_b.Raw(Op.AddOvfU, VT.I1, a, b));
                    case ConditionCode.o: return _b.Raw(Op.AddOvfS, VT.I1, a, b);
                    case ConditionCode.no: return _b.NotBool(_b.Raw(Op.AddOvfS, VT.I1, a, b));
                }
                break;

            case (int)FlagKind.IncDec:
            case (int)FlagKind.Shift:
            case (int)FlagKind.Neg:
                switch (cc)
                {
                    case ConditionCode.e: return _b.Cmp(Op.CmpEq, r!, Zero(r!));
                    case ConditionCode.ne: return _b.Cmp(Op.CmpNe, r!, Zero(r!));
                    case ConditionCode.s: return _b.Cmp(Op.CmpLtS, r!, Zero(r!));
                    case ConditionCode.ns: return _b.Cmp(Op.CmpLeS, Zero(r!), r!);
                    // After neg, carry is set exactly when the operand was non-zero.
                    case ConditionCode.b when (FlagKind)f.Imm == FlagKind.Neg: return _b.Cmp(Op.CmpNe, a, Zero(a));
                    case ConditionCode.ae when (FlagKind)f.Imm == FlagKind.Neg: return _b.Cmp(Op.CmpEq, a, Zero(a));
                    // inc/dec leave OF = (result crossed the signed boundary); with ZF/SF that makes these exact.
                    case ConditionCode.g when (FlagKind)f.Imm == FlagKind.IncDec && b.IsConstValue(-1):
                        return _b.Cmp(Op.CmpLtS, _b.Const(a.Type, 1), a); // dec a; jg  <=>  a > 1
                    case ConditionCode.le when (FlagKind)f.Imm == FlagKind.IncDec && b.IsConstValue(-1):
                        return _b.Cmp(Op.CmpLeS, a, _b.Const(a.Type, 1));
                    case ConditionCode.ge when (FlagKind)f.Imm == FlagKind.IncDec && b.IsConstValue(-1):
                        return _b.Cmp(Op.CmpLeS, _b.Const(a.Type, 1), a); // dec a; jge <=>  a >= 1
                    case ConditionCode.l when (FlagKind)f.Imm == FlagKind.IncDec && b.IsConstValue(-1):
                        return _b.Cmp(Op.CmpLtS, a, _b.Const(a.Type, 1));
                }
                break;

            case (int)FlagKind.Mul:
                switch (cc)
                {
                    case ConditionCode.o or ConditionCode.b: return _b.Raw(Op.MulOvfS, VT.I1, a, b);
                    case ConditionCode.no or ConditionCode.ae: return _b.NotBool(_b.Raw(Op.MulOvfS, VT.I1, a, b));
                }
                break;

            case (int)FlagKind.FCompare:
                // ucomis sets ZF=PF=CF=1 when unordered, CF=1 when a < b, ZF=1 when equal.
                switch (cc)
                {
                    case ConditionCode.a: return _b.Raw(Op.FCmpLt, VT.I1, b, a);
                    case ConditionCode.ae: return _b.Raw(Op.FCmpLe, VT.I1, b, a);
                    case ConditionCode.b: return _b.NotBool(_b.Raw(Op.FCmpLe, VT.I1, b, a));
                    case ConditionCode.be: return _b.NotBool(_b.Raw(Op.FCmpLt, VT.I1, b, a));
                    case ConditionCode.e: return BoolOr(_b.Raw(Op.FCmpEq, VT.I1, a, b), _b.Raw(Op.FCmpUnord, VT.I1, a, b));
                    case ConditionCode.ne: return _b.NotBool(BoolOr(_b.Raw(Op.FCmpEq, VT.I1, a, b), _b.Raw(Op.FCmpUnord, VT.I1, a, b)));
                    case ConditionCode.p: return _b.Raw(Op.FCmpUnord, VT.I1, a, b);
                    case ConditionCode.np: return _b.NotBool(_b.Raw(Op.FCmpUnord, VT.I1, a, b));
                }
                break;

            case FlagBitTest:
            {
                Node bit = _b.And(_b.Shift(Op.ShrU, a, _b.Trunc(b, VT.I8)), _b.Const(a.Type, 1));
                switch (cc)
                {
                    case ConditionCode.b: return _b.Cmp(Op.CmpNe, bit, Zero(bit));
                    case ConditionCode.ae: return _b.Cmp(Op.CmpEq, bit, Zero(bit));
                }
                break;
            }
        }
        return Opaque(cc, f);
    }

    private Node Opaque(ConditionCode cc, Node flags)
    {
        _fn.Problems.Add($"condition '{cc}' on {(flags.Op == Op.Flags ? ((FlagKind)flags.Imm).ToString() : flags.Op.ToString())} flags not modelled at 0x{_b.CurrentAddr:X}");
        Node n = _b.Raw(Op.FlagCond, VT.I1, flags);
        n.Imm = (long)cc;
        return n;
    }

    // ---- calls -------------------------------------------------------------------------------------------------

    private Node[] CaptureArguments(CallInfo info, CallShape? shape, Node? indirectTarget, bool tail = false)
    {
        var inputs = new List<Node>();
        if (indirectTarget != null)
        {
            inputs.Add(indirectTarget);
            info.Slots.Add(new ArgSlot(ArgSlotKind.Target, 0));
        }
        int registerPositions = shape == null ? 4 : Math.Min(4, shape.Count);
        for (int i = 0; i < registerPositions; i++)
        {
            bool known = shape != null;
            bool isFloat = known && shape!.IsFloat[i];
            if (!known || !isFloat)
            {
                inputs.Add(Var(IntArgRegs[i]));
                info.Slots.Add(new ArgSlot(ArgSlotKind.IntReg, i));
            }
            if (!known || isFloat)
            {
                inputs.Add(Var(VarXmm + i * 4));
                info.Slots.Add(new ArgSlot(ArgSlotKind.FloatReg, i * 4));
                if (!known || shape!.IsDouble[i])
                {
                    inputs.Add(Var(VarXmm + i * 4 + 1));
                    info.Slots.Add(new ArgSlot(ArgSlotKind.FloatReg, i * 4 + 1));
                }
            }
        }
        // Stack arguments sit above the 32-byte home area. For unknown indirect targets a few are captured
        // speculatively and dropped later if the resolved signature does not use them.
        int stackSlots = shape != null ? Math.Max(0, shape.Count - 4) : 4;
        Node sp = Var(VarRsp);
        // A call pushes the return address on top of them; a jump to another function leaves the caller's
        // return address where it is, so there they sit one slot further up already.
        int first = tail && !NoTailStackFix ? 0x28 : 0x20;
        if (shape == null && !NoStoredStackArguments) stackSlots = Math.Max(stackSlots, StoredStackSlots(sp, first));
        for (int i = 0; i < stackSlots; i++)
        {
            inputs.Add(_b.Load(_b.Add(sp, _b.Const(VT.I64, first + 8 * i)), VT.I64));
            info.Slots.Add(new ArgSlot(ArgSlotKind.Stack, i));
        }
        return inputs.ToArray();
    }

    private static readonly bool NoStoredStackArguments = Environment.GetEnvironmentVariable("REWIND_NO_STORED_STACK_ARGUMENTS") != null;

    /// <summary>
    /// How many stack argument slots, from the first on, the code just before a call writes: each of them
    /// written since the previous call, on every way to it. A call whose target is not known yet (a virtual
    /// call, say) has as many stack arguments as that run is long; a method with many parameters has more than
    /// the few slots captured on speculation, and the rest would be lost. Locals sit above the outgoing area,
    /// so a run that starts at the first slot and has no hole is the arguments being set up. The writes can
    /// start in the blocks before (the arguments two calls share, written before the branch between them).
    /// </summary>
    private int StoredStackSlots(Node sp, int first)
    {
        Node root = sp;
        long bias = 0;
        if (sp.Op == Op.Add && sp.In[1].IsConst)
        {
            root = sp.In[0];
            bias = IrBuilder.SImm(sp.In[1]);
        }
        HashSet<int> Stored(Block block, int depth)
        {
            var stored = new HashSet<int>();
            List<Node> nodes = block.Nodes;
            for (int i = nodes.Count - 1; i >= 0; i--)
            {
                Node n = nodes[i];
                if (n.Op is Op.Call or Op.TailCall) return stored;
                if (n.Op != Op.Store) continue;
                Node address = n.In[0];
                long offset;
                if (ReferenceEquals(address, root)) offset = 0;
                else if (address.Op == Op.Add && ReferenceEquals(address.In[0], root) && address.In[1].IsConst) offset = IrBuilder.SImm(address.In[1]);
                else continue;
                offset -= bias + first;
                if (offset < 0 || offset >= 8 * 64) continue;
                stored.Add((int)(offset / 8));
            }
            // (A block not lifted yet - one that loops back here - has no nodes and adds nothing.)
            if (depth == 0 || block.Preds.Count == 0 || block.Preds.Any(p => p.Nodes.Count == 0)) return stored;
            HashSet<int>? before = null;
            foreach (Block p in block.Preds)
            {
                HashSet<int> set = Stored(p, depth - 1);
                if (before == null) before = set;
                else before.IntersectWith(set);
            }
            stored.UnionWith(before!);
            return stored;
        }
        HashSet<int> all = Stored(_b.Current, 4);
        int count = 0;
        while (all.Contains(count)) count++;
        return count;
    }

    private void AfterCall(Node call, CallReturn returns)
    {
        Node Proj(int which, VT type)
        {
            Node p = _b.Raw(Op.Proj, type, call);
            p.Imm = which;
            return p;
        }
        // Registers the callee does not return anything in hold nothing meaningful afterwards.
        bool any = returns == CallReturn.Unknown;
        SetVar(0, any || returns == CallReturn.Integer ? Proj(CallResult.IntReturn, VT.I64) : _b.Undef(VT.I64));
        SetVar(VarXmm + 0, any || returns is CallReturn.Float or CallReturn.Double ? Proj(CallResult.FloatLane0, VT.I32) : _b.Undef(VT.I32));
        SetVar(VarXmm + 1, any || returns == CallReturn.Double ? Proj(CallResult.FloatLane1, VT.I32) : _b.Undef(VT.I32));
        SetVar(VarXmm + 2, _b.Undef(VT.I32));
        SetVar(VarXmm + 3, _b.Undef(VT.I32));
        // Caller-saved registers hold nothing meaningful afterwards.
        foreach (int v in (int[])[1, 2, 8, 9, 10, 11]) SetVar(v, _b.Undef(VT.I64));
        for (int x = 1; x <= 5; x++)
            for (int lane = 0; lane < 4; lane++)
                SetVar(VarXmm + x * 4 + lane, _b.Undef(VT.I32));
        SetVar(VarFlags, _b.Undef(VT.Flags));
        _rdxSignExtends = 0;
    }

    /// <summary>Return convention of the call most recently emitted.</summary>
    private CallReturn _lastCallReturn;

    private Node EmitCall(in Instruction ins, bool tail, bool noReturn)
    {
        var info = new CallInfo { NoReturn = noReturn };
        Node? indirect = null;
        CallShape? shape = null;
        _lastCallReturn = CallReturn.Unknown;
        if (ins.Op0Kind == OpKind.NearBranch64)
        {
            info.Target = ins.NearBranchTarget;
            shape = _ctx.ShapeOf(info.Target);
            _lastCallReturn = shape?.Returns ?? _ctx.ReturnOf(info.Target);
        }
        else
        {
            info.Indirect = true;
            indirect = ReadOp(ins, 0, VT.I64);
        }
        Node[] inputs = CaptureArguments(info, shape, indirect, tail);
        Node call = _b.Raw(tail ? Op.TailCall : Op.Call, VT.None, inputs);
        call.Aux = info;
        return call;
    }

    private Node Intrinsic(string name, VT type, params Node[] inputs)
    {
        Node call = _b.Raw(Op.Call, type, inputs);
        call.Aux = new CallInfo { Intrinsic = name };
        return call;
    }

    // ---- blocks ------------------------------------------------------------------------------------------------

    private void LiftBlock(Block block, RawBlock raw)
    {
        _block = block;
        _b.Current = block;
        _rdxSignExtends = 0;
        int count = raw.Instructions.Count;
        for (int i = 0; i < count; i++)
        {
            Instruction ins = raw.Instructions[i];
            _b.CurrentAddr = ins.IP;
            bool last = i == count - 1;
            try
            {
                if (last && LiftTerminator(ins, raw, block)) return;
                Instruction? next = i + 1 < count ? raw.Instructions[i + 1] : null;
                LiftInstruction(ins, next);
            }
            catch (NotSupportedException e)
            {
                _fn.Problems.Add($"0x{ins.IP:X} {ins.Mnemonic}: {e.Message}");
            }
        }
        // No explicit terminator: control continues into the next block.
        if (block.Terminator == null)
        {
            if (raw.End == BlockEnd.FallThrough && block.Succs.Count == 1) _b.Raw(Op.Jump, VT.None);
            else _b.Raw(Op.Unreachable, VT.None);
        }
    }

    private Node[] ReturnValues() => [Var(0), Var(VarXmm + 0), Var(VarXmm + 1)];

    private bool LiftTerminator(in Instruction ins, RawBlock raw, Block block)
    {
        switch (raw.End)
        {
            case BlockEnd.Jump:
                _b.Raw(Op.Jump, VT.None);
                return true;
            case BlockEnd.InlinedCall:
            {
                // The callee's code follows, on a stack of its own, with the return address where it expects it.
                int region = _siteRegion[block];
                _savedRsp[region] = Var(VarRsp);
                EnterInlineStack(region, (long)ins.NextIP);
                _b.Raw(Op.Jump, VT.None);
                return true;
            }
            case BlockEnd.Return when _inlineReturns.Contains(block):
                SetVar(VarRsp, _savedRsp[_returnOwner[block]]);
                _b.Raw(Op.Jump, VT.None);
                return true;
            case BlockEnd.TailCall when _tailJumps.Contains(block):
                // A jump into more pasted code: it returns for the same call, and gets fresh stack too.
                if (_outerJumps.Contains(block)) _savedRsp[_siteRegion[block]] = Var(VarRsp);
                EnterInlineStack(_siteRegion[block], 0);
                _b.Raw(Op.Jump, VT.None);
                return true;
            case BlockEnd.TailCall or BlockEnd.IndirectTailCall when _inlineReturns.Contains(block):
                // Pasted code ending in a jump to another function: that function returns where the pasted
                // code would have. Popping the return address first leaves the stack as the jump leaves it.
                SetVar(VarRsp, _b.Add(Var(VarRsp), _b.Const(VT.I64, 8)));
                EmitCall(ins, tail: false, noReturn: false);
                SetVar(VarRsp, _savedRsp[_returnOwner[block]]);
                _b.Raw(Op.Jump, VT.None);
                return true;
            case BlockEnd.Return when _outerReturns.TryGetValue(block, out int left):
                // Code pasted at the function's own last jump returns for the function, on the function's stack.
                SetVar(VarRsp, _savedRsp[left]);
                _b.Raw(Op.Return, VT.None, ReturnValues());
                return true;
            case BlockEnd.TailCall or BlockEnd.IndirectTailCall when _outerReturns.TryGetValue(block, out int leftBy):
                // ... or jumps on to another function for it.
                SetVar(VarRsp, _savedRsp[leftBy]);
                EmitCall(ins, tail: true, noReturn: false);
                return true;
            case BlockEnd.Return when _funcletReturns.Contains(block):
                // The catch funclet is done: execution continues in the function, on the function's stack.
                SetVar(VarRsp, Var(VarSavedRsp));
                _b.Raw(Op.Jump, VT.None);
                return true;
            case BlockEnd.Branch:
            {
                Node cond = Condition(ins.ConditionCode);
                _b.Raw(Op.Branch, VT.None, cond);
                return true;
            }
            case BlockEnd.Switch:
            {
                // The index is whatever the table load was indexed by; recover it from the jump's operand
                // expression: target = imageBase + load32(imageBase + rva + index * 4).
                Node target = ReadOp(ins, 0, VT.I64);
                Node? index = FindSwitchIndex(target);
                if (index == null)
                {
                    _fn.Problems.Add($"jump table index not recovered at 0x{ins.IP:X}");
                    index = _b.Undef(VT.I64);
                }
                Node sw = _b.Raw(Op.Switch, VT.None, index);
                sw.Aux = new List<Block>(block.Succs);
                return true;
            }
            case BlockEnd.Return:
                // "ret" pops the return address; nothing after it matters to this function.
                _b.Raw(Op.Return, VT.None, ReturnValues());
                return true;
            case BlockEnd.TailCall:
            case BlockEnd.IndirectTailCall:
                EmitCall(ins, tail: true, noReturn: false);
                return true;
            case BlockEnd.NoReturnCall:
                EmitCall(ins, tail: false, noReturn: true);
                _b.Raw(Op.Unreachable, VT.None);
                return true;
            case BlockEnd.Trap:
                _b.Raw(Op.Unreachable, VT.None);
                return true;
            default:
                return false;
        }
    }

    private static Node? FindSwitchIndex(Node target)
    {
        // Look for load32(base + index*4 + c) underneath additions and extensions.
        var pending = new Stack<Node>();
        pending.Push(target);
        int budget = 32;
        while (pending.Count > 0 && budget-- > 0)
        {
            Node n = pending.Pop();
            if (n.Op == Op.Load && n.Type == VT.I32)
            {
                var terms = new Stack<Node>();
                terms.Push(n.In[0]);
                int inner = 16;
                while (terms.Count > 0 && inner-- > 0)
                {
                    Node t = terms.Pop();
                    if (t.Op == Op.Mul && t.In[1].IsConstValue(4)) return t.In[0];
                    if (t.Op == Op.Shl && t.In[1].IsConstValue(2)) return t.In[0];
                    if (t.Op == Op.Add)
                    {
                        terms.Push(t.In[0]);
                        terms.Push(t.In[1]);
                    }
                }
                return null;
            }
            foreach (Node input in n.In) pending.Push(input);
        }
        return null;
    }

    // ---- instructions ------------------------------------------------------------------------------------------

    private void Unknown(in Instruction ins)
    {
        Unsupported[ins.Mnemonic] = Unsupported.GetValueOrDefault(ins.Mnemonic) + 1;
        throw new NotSupportedException("instruction not modelled");
    }

    private void LiftInstruction(in Instruction ins, Instruction? next)
    {
        Mnemonic m = ins.Mnemonic;
        switch (m)
        {
            case Mnemonic.Nop or Mnemonic.Fnop or Mnemonic.Endbr64 or Mnemonic.Pause
                or Mnemonic.Prefetchnta or Mnemonic.Prefetcht0 or Mnemonic.Prefetcht1 or Mnemonic.Prefetcht2 or Mnemonic.Prefetchw:
                return;

            case Mnemonic.Mov:
            {
                VT type = OperandType(ins, ins.Op0Kind == OpKind.Memory ? 0 : ins.Op1Kind == OpKind.Memory ? 1 : 0);
                if (ins.Op0Kind == OpKind.Register) type = RegType(ins.Op0Register);
                WriteOp(ins, 0, ReadOp(ins, 1, type));
                return;
            }
            case Mnemonic.Movzx:
                WriteReg(ins.Op0Register, _b.ZExt(ReadOp(ins, 1, OperandType(ins, 1)), RegType(ins.Op0Register)));
                return;
            case Mnemonic.Movsx or Mnemonic.Movsxd:
                WriteReg(ins.Op0Register, _b.SExt(ReadOp(ins, 1, OperandType(ins, 1)), RegType(ins.Op0Register)));
                return;
            case Mnemonic.Lea:
                WriteReg(ins.Op0Register, _b.Trunc(Address(ins), RegType(ins.Op0Register)));
                return;

            case Mnemonic.Push:
            {
                Node value = ins.Op0Kind == OpKind.Register ? _b.ZExt(ReadReg(ins.Op0Register), VT.I64) : ReadOp(ins, 0, VT.I64);
                Node sp = _b.Add(Var(VarRsp), _b.Const(VT.I64, -8));
                SetVar(VarRsp, sp);
                _b.Store(sp, value);
                return;
            }
            case Mnemonic.Pop:
            {
                Node sp = Var(VarRsp);
                Node value = _b.Load(sp, VT.I64);
                SetVar(VarRsp, _b.Add(sp, _b.Const(VT.I64, 8)));
                WriteOp(ins, 0, value);
                return;
            }

            case Mnemonic.Add or Mnemonic.Sub or Mnemonic.And or Mnemonic.Or or Mnemonic.Xor:
            {
                VT type = OperandType(ins, 0);
                Node? address = ins.Op0Kind == OpKind.Memory || ins.Op1Kind == OpKind.Memory ? Address(ins) : null;
                // xor r, r and sub r, r are the idiomatic zeroing forms and do not depend on the old value.
                if (m is Mnemonic.Xor or Mnemonic.Sub && ins.Op0Kind == OpKind.Register && ins.Op1Kind == OpKind.Register &&
                    ins.Op0Register == ins.Op1Register)
                {
                    Node zero = _b.Const(type, 0);
                    WriteReg(ins.Op0Register, zero);
                    SetFlags(FlagKind.Logic, zero, zero, zero);
                    return;
                }
                Node a = ReadOp(ins, 0, type, address), b = ReadOp(ins, 1, type, address);
                if (ins.HasLockPrefix)
                {
                    Intrinsic("atomic_" + m.ToString().ToLowerInvariant(), VT.None, address!, b);
                    SetVar(VarFlags, _b.Undef(VT.Flags));
                    return;
                }
                Node r = m switch
                {
                    Mnemonic.Add => _b.Add(a, b),
                    Mnemonic.Sub => _b.Sub(a, b),
                    Mnemonic.And => _b.And(a, b),
                    Mnemonic.Or => _b.Or(a, b),
                    _ => _b.Xor(a, b),
                };
                WriteOp(ins, 0, r, address);
                if (m == Mnemonic.Add) SetFlags(FlagKind.Add, a, b, r);
                else if (m == Mnemonic.Sub) SetFlags(FlagKind.Sub, a, b, r);
                else SetFlags(FlagKind.Logic, a, b, r);
                return;
            }

            case Mnemonic.Cmp:
            {
                VT type = OperandType(ins, 0);
                Node? address = ins.Op0Kind == OpKind.Memory || ins.Op1Kind == OpKind.Memory ? Address(ins) : null;
                SetFlags(FlagKind.Sub, ReadOp(ins, 0, type, address), ReadOp(ins, 1, type, address));
                return;
            }
            case Mnemonic.Test:
            {
                VT type = OperandType(ins, 0);
                Node? address = ins.Op0Kind == OpKind.Memory || ins.Op1Kind == OpKind.Memory ? Address(ins) : null;
                Node a = ReadOp(ins, 0, type, address);
                Node b = ins.Op1Kind == OpKind.Register && ins.Op0Kind == OpKind.Register && ins.Op0Register == ins.Op1Register
                    ? a
                    : ReadOp(ins, 1, type, address);
                SetFlags(FlagKind.Test, a, b);
                return;
            }

            case Mnemonic.Inc or Mnemonic.Dec:
            {
                VT type = OperandType(ins, 0);
                Node? address = ins.Op0Kind == OpKind.Memory ? Address(ins) : null;
                Node a = ReadOp(ins, 0, type, address);
                Node delta = _b.Const(type, m == Mnemonic.Inc ? 1 : -1);
                if (ins.HasLockPrefix)
                {
                    Intrinsic(m == Mnemonic.Inc ? "atomic_inc" : "atomic_dec", VT.None, address!);
                    SetVar(VarFlags, _b.Undef(VT.Flags));
                    return;
                }
                Node r = _b.Add(a, delta);
                WriteOp(ins, 0, r, address);
                SetFlags(FlagKind.IncDec, a, delta, r);
                return;
            }
            case Mnemonic.Neg:
            {
                VT type = OperandType(ins, 0);
                Node? address = ins.Op0Kind == OpKind.Memory ? Address(ins) : null;
                Node a = ReadOp(ins, 0, type, address);
                Node r = _b.Neg(a);
                WriteOp(ins, 0, r, address);
                SetFlags(FlagKind.Neg, a, a, r);
                return;
            }
            case Mnemonic.Not:
            {
                VT type = OperandType(ins, 0);
                Node? address = ins.Op0Kind == OpKind.Memory ? Address(ins) : null;
                WriteOp(ins, 0, _b.Not(ReadOp(ins, 0, type, address)), address);
                return;
            }

            case Mnemonic.Adc or Mnemonic.Sbb:
            {
                VT type = OperandType(ins, 0);
                Node carry = Condition(ConditionCode.b);
                if (m == Mnemonic.Sbb && ins.Op0Kind == OpKind.Register && ins.Op1Kind == OpKind.Register &&
                    ins.Op0Register == ins.Op1Register)
                {
                    // sbb r, r yields -1 when carry is set, else 0.
                    WriteReg(ins.Op0Register, _b.Select(carry, _b.Const(type, -1), _b.Const(type, 0)));
                    SetVar(VarFlags, _b.Undef(VT.Flags));
                    return;
                }
                Node? address = ins.Op0Kind == OpKind.Memory || ins.Op1Kind == OpKind.Memory ? Address(ins) : null;
                Node a = ReadOp(ins, 0, type, address), b = ReadOp(ins, 1, type, address);
                Node c = _b.ZExt(carry, type);
                Node r = m == Mnemonic.Adc ? _b.Add(_b.Add(a, b), c) : _b.Sub(_b.Sub(a, b), c);
                WriteOp(ins, 0, r, address);
                SetVar(VarFlags, _b.Undef(VT.Flags));
                return;
            }

            case Mnemonic.Imul:
            {
                if (ins.OpCount == 1)
                {
                    VT type = OperandType(ins, 0);
                    Node src = ReadOp(ins, 0, type);
                    Node acc = _b.Trunc(Var(0), type);
                    WriteReg(AccumulatorOf(type), _b.Mul(acc, src));
                    if (type != VT.I8) WriteReg(DataOf(type), _b.Raw(Op.MulHiS, type, acc, src));
                    SetFlags(FlagKind.Mul, acc, src);
                    return;
                }
                VT t = RegType(ins.Op0Register);
                Node a = ins.OpCount == 3 ? ReadOp(ins, 1, t) : ReadReg(ins.Op0Register);
                Node b = ReadOp(ins, ins.OpCount == 3 ? 2 : 1, t);
                Node r = _b.Mul(a, b);
                WriteReg(ins.Op0Register, r);
                SetFlags(FlagKind.Mul, a, b, r);
                return;
            }
            case Mnemonic.Mul:
            {
                VT type = OperandType(ins, 0);
                Node src = ReadOp(ins, 0, type);
                Node acc = _b.Trunc(Var(0), type);
                WriteReg(AccumulatorOf(type), _b.Mul(acc, src));
                if (type != VT.I8) WriteReg(DataOf(type), _b.Raw(Op.MulHiU, type, acc, src));
                SetVar(VarFlags, _b.Undef(VT.Flags));
                return;
            }
            case Mnemonic.Idiv or Mnemonic.Div:
            {
                VT type = OperandType(ins, 0);
                if (type is VT.I8 or VT.I16) Unknown(ins);
                Node src = ReadOp(ins, 0, type);
                Node acc = _b.Trunc(Var(0), type);
                bool signed = m == Mnemonic.Idiv;
                // The dividend is rdx:rax. Compilers set rdx to the sign extension (cdq/cqo) or to zero first,
                // which makes this an ordinary division of rax.
                Node high = _b.Trunc(Var(2), type);
                bool ok = signed ? _rdxSignExtends == type.Bits() : high.IsConstValue(0);
                if (!ok) _fn.Problems.Add($"wide division at 0x{ins.IP:X} treated as a plain division");
                Node q = _b.Raw(signed ? Op.DivS : Op.DivU, type, acc, src);
                Node rem = _b.Raw(signed ? Op.RemS : Op.RemU, type, acc, src);
                WriteReg(AccumulatorOf(type), q);
                WriteReg(DataOf(type), rem);
                SetVar(VarFlags, _b.Undef(VT.Flags));
                return;
            }
            case Mnemonic.Cdq:
                WriteReg(Register.EDX, _b.Shift(Op.ShrS, _b.Trunc(Var(0), VT.I32), _b.Const(VT.I8, 31)));
                _rdxSignExtends = 32;
                return;
            case Mnemonic.Cqo:
                SetVar(2, _b.Shift(Op.ShrS, Var(0), _b.Const(VT.I8, 63)));
                _rdxSignExtends = 64;
                return;
            case Mnemonic.Cdqe:
                SetVar(0, _b.SExt(_b.Trunc(Var(0), VT.I32), VT.I64));
                return;
            case Mnemonic.Cwde:
                WriteReg(Register.EAX, _b.SExt(_b.Trunc(Var(0), VT.I16), VT.I32));
                return;
            case Mnemonic.Cbw:
                WriteReg(Register.AX, _b.SExt(_b.Trunc(Var(0), VT.I8), VT.I16));
                return;

            case Mnemonic.Shl or Mnemonic.Sal or Mnemonic.Shr or Mnemonic.Sar or Mnemonic.Rol or Mnemonic.Ror:
            {
                VT type = OperandType(ins, 0);
                Node? address = ins.Op0Kind == OpKind.Memory ? Address(ins) : null;
                Node a = ReadOp(ins, 0, type, address);
                Node count = ins.OpCount < 2 ? _b.Const(VT.I8, 1)
                    : ins.Op1Kind == OpKind.Register ? ReadReg(Register.CL)
                    : _b.Const(VT.I8, (long)ins.GetImmediate(1));
                Op op = m switch
                {
                    Mnemonic.Shl or Mnemonic.Sal => Op.Shl,
                    Mnemonic.Shr => Op.ShrU,
                    Mnemonic.Sar => Op.ShrS,
                    Mnemonic.Rol => Op.Rol,
                    _ => Op.Ror,
                };
                // Shift counts are taken modulo 64 for 64-bit operands and modulo 32 for all narrower ones;
                // rotations wrap at the operand width.
                int countMask = op is Op.Rol or Op.Ror ? type.Bits() - 1 : type == VT.I64 ? 63 : 31;
                if (!count.IsConst) count = _b.And(count, _b.Const(VT.I8, countMask));
                Node r = _b.Shift(op, a, count);
                WriteOp(ins, 0, r, address);
                SetFlags(FlagKind.Shift, a, count, r);
                return;
            }

            case Mnemonic.Bt or Mnemonic.Bts or Mnemonic.Btr or Mnemonic.Btc:
            {
                VT type = OperandType(ins, 0);
                if (ins.Op0Kind == OpKind.Memory && ins.Op1Kind == OpKind.Register) Unknown(ins); // bit string form
                Node a = ReadOp(ins, 0, type);
                Node index = _b.And(_b.ZExt(ReadOp(ins, 1, VT.I8), type), _b.Const(type, type.Bits() - 1));
                if (ins.Op1Kind == OpKind.Register) index = _b.And(_b.ZExt(_b.Trunc(ReadReg(ins.Op1Register), VT.I8), type), _b.Const(type, type.Bits() - 1));
                if (m != Mnemonic.Bt)
                {
                    Node mask = _b.Shift(Op.Shl, _b.Const(type, 1), _b.Trunc(index, VT.I8));
                    Node r = m switch
                    {
                        Mnemonic.Bts => _b.Or(a, mask),
                        Mnemonic.Btr => _b.And(a, _b.Not(mask)),
                        _ => _b.Xor(a, mask),
                    };
                    WriteOp(ins, 0, r);
                }
                Node f = _fn.NewNode(Op.Flags, VT.Flags, null, a, index);
                f.Imm = FlagBitTest;
                SetVar(VarFlags, f);
                return;
            }

            case Mnemonic.Bswap:
                WriteReg(ins.Op0Register, _b.Raw(Op.Bswap, RegType(ins.Op0Register), ReadReg(ins.Op0Register)));
                return;
            case Mnemonic.Popcnt or Mnemonic.Lzcnt or Mnemonic.Tzcnt:
            {
                VT type = RegType(ins.Op0Register);
                Op op = m == Mnemonic.Popcnt ? Op.Popcnt : m == Mnemonic.Lzcnt ? Op.Lzcnt : Op.Tzcnt;
                WriteReg(ins.Op0Register, _b.Raw(op, type, ReadOp(ins, 1, type)));
                SetVar(VarFlags, _b.Undef(VT.Flags));
                return;
            }
            case Mnemonic.Bsf or Mnemonic.Bsr:
            {
                // For a non-zero source: bsf = trailing zero count, bsr = 63/31 - leading zero count.
                VT type = RegType(ins.Op0Register);
                Node src = ReadOp(ins, 1, type);
                Node r = m == Mnemonic.Bsf
                    ? _b.Raw(Op.Tzcnt, type, src)
                    : _b.Sub(_b.Const(type, type.Bits() - 1), _b.Raw(Op.Lzcnt, type, src));
                WriteReg(ins.Op0Register, r);
                SetFlags(FlagKind.Test, src, src);
                return;
            }

            case Mnemonic.Xchg:
            {
                VT type = OperandType(ins, 0);
                Node? address = ins.Op0Kind == OpKind.Memory || ins.Op1Kind == OpKind.Memory ? Address(ins) : null;
                if (address != null)
                {
                    // xchg with memory is always atomic.
                    Register reg = ins.Op0Kind == OpKind.Register ? ins.Op0Register : ins.Op1Register;
                    Node old = Intrinsic("atomic_exchange", type, address, ReadReg(reg));
                    WriteReg(reg, old);
                    return;
                }
                Node a = ReadReg(ins.Op0Register), b = ReadReg(ins.Op1Register);
                WriteReg(ins.Op0Register, b);
                WriteReg(ins.Op1Register, a);
                return;
            }
            case Mnemonic.Cmpxchg:
            {
                VT type = OperandType(ins, 0);
                if (ins.Op0Kind != OpKind.Memory) Unknown(ins);
                Node address = Address(ins);
                Node expected = _b.Trunc(Var(0), type);
                Node old = Intrinsic("atomic_compare_exchange", type, address, ReadReg(ins.Op1Register), expected);
                WriteReg(AccumulatorOf(type), old);
                SetFlags(FlagKind.Sub, expected, old);
                return;
            }
            case Mnemonic.Xadd:
            {
                VT type = OperandType(ins, 0);
                if (ins.Op0Kind != OpKind.Memory) Unknown(ins);
                Node old = Intrinsic("atomic_fetch_add", type, Address(ins), ReadReg(ins.Op1Register));
                WriteReg(ins.Op1Register, old);
                SetVar(VarFlags, _b.Undef(VT.Flags));
                return;
            }
            case Mnemonic.Mfence or Mnemonic.Lfence or Mnemonic.Sfence:
                Intrinsic("memory_barrier", VT.None);
                return;

            case Mnemonic.Call:
            {
                // __chkstk only probes the stack; it leaves every register (including rax) untouched.
                if (next is { Mnemonic: Mnemonic.Sub } n && n.Op0Kind == OpKind.Register && n.Op0Register == Register.RSP &&
                    n.Op1Kind == OpKind.Register && n.Op1Register == Register.RAX)
                    return;
                Node call = EmitCall(ins, tail: false, noReturn: false);
                AfterCall(call, _lastCallReturn);
                return;
            }

            case Mnemonic.Movsb or Mnemonic.Movsw or Mnemonic.Movsd or Mnemonic.Movsq when ins.OpCount == 2 && ins.Op0Kind == OpKind.MemoryESRDI:
            case Mnemonic.Stosb or Mnemonic.Stosw or Mnemonic.Stosd or Mnemonic.Stosq:
            {
                int width = m switch
                {
                    Mnemonic.Movsb or Mnemonic.Stosb => 1, Mnemonic.Movsw or Mnemonic.Stosw => 2,
                    Mnemonic.Movsd or Mnemonic.Stosd => 4, _ => 8,
                };
                bool isMove = m is Mnemonic.Movsb or Mnemonic.Movsw or Mnemonic.Movsd or Mnemonic.Movsq;
                Node count = ins.HasRepPrefix ? Var(1) : _b.Const(VT.I64, 1);
                Node bytes = _b.Mul(count, _b.Const(VT.I64, width));
                if (isMove) Intrinsic("memcpy", VT.None, Var(7), Var(6), bytes);
                else Intrinsic("memset" + width, VT.None, Var(7), _b.Trunc(Var(0), VTExtensions.IntOfBytes(width)), bytes);
                SetVar(7, _b.Add(Var(7), bytes));
                if (isMove) SetVar(6, _b.Add(Var(6), bytes));
                if (ins.HasRepPrefix) SetVar(1, _b.Const(VT.I64, 0));
                return;
            }
        }

        if (m >= Mnemonic.Cmova && m <= Mnemonic.Cmovs)
        {
            VT type = RegType(ins.Op0Register);
            Node cond = Condition(ins.ConditionCode);
            Node whenTrue = ReadOp(ins, 1, type);
            WriteReg(ins.Op0Register, _b.Select(cond, whenTrue, ReadReg(ins.Op0Register)));
            return;
        }
        if (m >= Mnemonic.Seta && m <= Mnemonic.Sets)
        {
            WriteOp(ins, 0, _b.ZExt(Condition(ins.ConditionCode), VT.I8));
            return;
        }

        if (LiftSse(ins)) return;
        Unknown(ins);
    }

    private static Register AccumulatorOf(VT type) => type switch
    {
        VT.I8 => Register.AL, VT.I16 => Register.AX, VT.I32 => Register.EAX, _ => Register.RAX,
    };

    private static Register DataOf(VT type) => type switch
    {
        VT.I8 => Register.DL, VT.I16 => Register.DX, VT.I32 => Register.EDX, _ => Register.RDX,
    };

    // ---- SSE ---------------------------------------------------------------------------------------------------

    private Node F32(in Instruction ins, int op) =>
        ins.GetOpKind(op) == OpKind.Register ? _b.BitsToF(Lane(ins.GetOpRegister(op), 0)) : _b.BitsToF(LoadAt(Address(ins), VT.I32));

    private Node F64(in Instruction ins, int op)
    {
        if (ins.GetOpKind(op) != OpKind.Register) return _b.BitsToF(LoadAt(Address(ins), VT.I64));
        Register r = ins.GetOpRegister(op);
        return _b.BitsToF(_b.Concat(Lane(r, 1), Lane(r, 0)));
    }

    private void SetF32(Register xmm, Node value) => SetLane(xmm, 0, _b.FToBits(value));

    private void SetF64(Register xmm, Node value) => SetQword(xmm, 0, _b.FToBits(value));

    private Node Qword(Register xmm, int half) => _b.Concat(Lane(xmm, half * 2 + 1), Lane(xmm, half * 2));

    private void SetQword(Register xmm, int half, Node value)
    {
        SetLane(xmm, half * 2, _b.Trunc(value, VT.I32));
        SetLane(xmm, half * 2 + 1, _b.Trunc(_b.Shift(Op.ShrU, value, _b.Const(VT.I8, 32)), VT.I32));
    }

    /// <summary>The four 32-bit lanes of a 128-bit source operand (register or memory).</summary>
    private Node[] Lanes(in Instruction ins, int op)
    {
        if (ins.GetOpKind(op) == OpKind.Register)
        {
            Register r = ins.GetOpRegister(op);
            return [Lane(r, 0), Lane(r, 1), Lane(r, 2), Lane(r, 3)];
        }
        Node address = Address(ins);
        Node lo = LoadAt(address, VT.I64), hi = LoadAt(_b.Add(address, _b.Const(VT.I64, 8)), VT.I64);
        Node c32 = _b.Const(VT.I8, 32);
        return
        [
            _b.Trunc(lo, VT.I32), _b.Trunc(_b.Shift(Op.ShrU, lo, c32), VT.I32),
            _b.Trunc(hi, VT.I32), _b.Trunc(_b.Shift(Op.ShrU, hi, c32), VT.I32),
        ];
    }

    private void SetLanes(Register xmm, Node[] lanes)
    {
        for (int i = 0; i < 4; i++) SetLane(xmm, i, lanes[i]);
    }

    private Node ZeroLane() => _b.Const(VT.I32, 0);

    private bool LiftSse(in Instruction ins)
    {
        Mnemonic m = ins.Mnemonic;
        switch (m)
        {
            case Mnemonic.Movss:
                if (ins.Op0Kind == OpKind.Memory) _b.Store(Address(ins), Lane(ins.Op1Register, 0));
                else if (ins.Op1Kind == OpKind.Memory)
                    SetLanes(ins.Op0Register, [LoadAt(Address(ins), VT.I32), ZeroLane(), ZeroLane(), ZeroLane()]);
                else SetLane(ins.Op0Register, 0, Lane(ins.Op1Register, 0));
                return true;

            case Mnemonic.Movsd when ins.Op0Kind != OpKind.MemoryESRDI:
                if (ins.Op0Kind == OpKind.Memory) _b.Store(Address(ins), Qword(ins.Op1Register, 0));
                else if (ins.Op1Kind == OpKind.Memory)
                {
                    SetQword(ins.Op0Register, 0, LoadAt(Address(ins), VT.I64));
                    SetLane(ins.Op0Register, 2, ZeroLane());
                    SetLane(ins.Op0Register, 3, ZeroLane());
                }
                else
                {
                    SetLane(ins.Op0Register, 0, Lane(ins.Op1Register, 0));
                    SetLane(ins.Op0Register, 1, Lane(ins.Op1Register, 1));
                }
                return true;

            case Mnemonic.Movaps or Mnemonic.Movups or Mnemonic.Movapd or Mnemonic.Movupd or Mnemonic.Movdqa or Mnemonic.Movdqu:
                if (ins.Op0Kind == OpKind.Memory)
                {
                    Node address = Address(ins);
                    _b.Store(address, Qword(ins.Op1Register, 0));
                    _b.Store(_b.Add(address, _b.Const(VT.I64, 8)), Qword(ins.Op1Register, 1));
                }
                else SetLanes(ins.Op0Register, Lanes(ins, 1));
                return true;

            case Mnemonic.Movd:
                if (ins.Op0Kind == OpKind.Register && ins.Op0Register.IsXMM())
                    SetLanes(ins.Op0Register, [ReadOp(ins, 1, VT.I32), ZeroLane(), ZeroLane(), ZeroLane()]);
                else WriteOp(ins, 0, Lane(ins.Op1Register, 0));
                return true;

            case Mnemonic.Movq:
                if (ins.Op0Kind == OpKind.Register && ins.Op0Register.IsXMM())
                {
                    Node value = ins.Op1Kind == OpKind.Register && ins.Op1Register.IsXMM()
                        ? Qword(ins.Op1Register, 0)
                        : ReadOp(ins, 1, VT.I64);
                    SetQword(ins.Op0Register, 0, value);
                    SetLane(ins.Op0Register, 2, ZeroLane());
                    SetLane(ins.Op0Register, 3, ZeroLane());
                }
                else WriteOp(ins, 0, Qword(ins.Op1Register, 0));
                return true;

            case Mnemonic.Movlps or Mnemonic.Movlpd:
                if (ins.Op0Kind == OpKind.Memory) _b.Store(Address(ins), Qword(ins.Op1Register, 0));
                else SetQword(ins.Op0Register, 0, LoadAt(Address(ins), VT.I64));
                return true;
            case Mnemonic.Movhps or Mnemonic.Movhpd:
                if (ins.Op0Kind == OpKind.Memory) _b.Store(Address(ins), Qword(ins.Op1Register, 1));
                else SetQword(ins.Op0Register, 1, LoadAt(Address(ins), VT.I64));
                return true;
            case Mnemonic.Movhlps:
                SetLane(ins.Op0Register, 0, Lane(ins.Op1Register, 2));
                SetLane(ins.Op0Register, 1, Lane(ins.Op1Register, 3));
                return true;
            case Mnemonic.Movlhps:
                SetLane(ins.Op0Register, 2, Lane(ins.Op1Register, 0));
                SetLane(ins.Op0Register, 3, Lane(ins.Op1Register, 1));
                return true;

            case Mnemonic.Addss or Mnemonic.Subss or Mnemonic.Mulss or Mnemonic.Divss or Mnemonic.Minss or Mnemonic.Maxss:
            {
                Op op = m switch
                {
                    Mnemonic.Addss => Op.FAdd, Mnemonic.Subss => Op.FSub, Mnemonic.Mulss => Op.FMul,
                    Mnemonic.Divss => Op.FDiv, Mnemonic.Minss => Op.FMin, _ => Op.FMax,
                };
                SetF32(ins.Op0Register, _b.Raw(op, VT.F32, F32(ins, 0), F32(ins, 1)));
                return true;
            }
            case Mnemonic.Addsd or Mnemonic.Subsd or Mnemonic.Mulsd or Mnemonic.Divsd or Mnemonic.Minsd or Mnemonic.Maxsd:
            {
                Op op = m switch
                {
                    Mnemonic.Addsd => Op.FAdd, Mnemonic.Subsd => Op.FSub, Mnemonic.Mulsd => Op.FMul,
                    Mnemonic.Divsd => Op.FDiv, Mnemonic.Minsd => Op.FMin, _ => Op.FMax,
                };
                SetF64(ins.Op0Register, _b.Raw(op, VT.F64, F64(ins, 0), F64(ins, 1)));
                return true;
            }
            case Mnemonic.Sqrtss:
                SetF32(ins.Op0Register, _b.Raw(Op.FSqrt, VT.F32, F32(ins, 1)));
                return true;
            case Mnemonic.Sqrtsd:
                SetF64(ins.Op0Register, _b.Raw(Op.FSqrt, VT.F64, F64(ins, 1)));
                return true;

            case Mnemonic.Comiss or Mnemonic.Ucomiss:
                SetFlags(FlagKind.FCompare, F32(ins, 0), F32(ins, 1));
                return true;
            case Mnemonic.Comisd or Mnemonic.Ucomisd:
                SetFlags(FlagKind.FCompare, F64(ins, 0), F64(ins, 1));
                return true;

            case Mnemonic.Cvtsi2ss:
                SetF32(ins.Op0Register, _b.Raw(Op.SIntToF, VT.F32, ReadOp(ins, 1, OperandType(ins, 1))));
                return true;
            case Mnemonic.Cvtsi2sd:
                SetF64(ins.Op0Register, _b.Raw(Op.SIntToF, VT.F64, ReadOp(ins, 1, OperandType(ins, 1))));
                return true;
            case Mnemonic.Cvttss2si:
                WriteReg(ins.Op0Register, _b.Raw(Op.FToSInt, RegType(ins.Op0Register), F32(ins, 1)));
                return true;
            case Mnemonic.Cvttsd2si:
                WriteReg(ins.Op0Register, _b.Raw(Op.FToSInt, RegType(ins.Op0Register), F64(ins, 1)));
                return true;
            case Mnemonic.Cvtss2sd:
                SetF64(ins.Op0Register, _b.Raw(Op.FExt, VT.F64, F32(ins, 1)));
                return true;
            case Mnemonic.Cvtsd2ss:
                SetF32(ins.Op0Register, _b.Raw(Op.FTrunc, VT.F32, F64(ins, 1)));
                return true;
            case Mnemonic.Cvtdq2ps:
            {
                Node[] src = Lanes(ins, 1);
                var result = new Node[4];
                for (int i = 0; i < 4; i++) result[i] = _b.FToBits(_b.Raw(Op.SIntToF, VT.F32, src[i]));
                SetLanes(ins.Op0Register, result);
                return true;
            }
            case Mnemonic.Cvttps2dq:
            {
                Node[] src = Lanes(ins, 1);
                var result = new Node[4];
                for (int i = 0; i < 4; i++) result[i] = _b.Raw(Op.FToSInt, VT.I32, _b.BitsToF(src[i]));
                SetLanes(ins.Op0Register, result);
                return true;
            }
            case Mnemonic.Cvtdq2pd:
            {
                Node[] src = Lanes(ins, 1);
                SetQword(ins.Op0Register, 1, _b.FToBits(_b.Raw(Op.SIntToF, VT.F64, src[1])));
                SetQword(ins.Op0Register, 0, _b.FToBits(_b.Raw(Op.SIntToF, VT.F64, src[0])));
                return true;
            }
            case Mnemonic.Cvtps2pd:
            {
                Node[] src = Lanes(ins, 1);
                SetQword(ins.Op0Register, 1, _b.FToBits(_b.Raw(Op.FExt, VT.F64, _b.BitsToF(src[1]))));
                SetQword(ins.Op0Register, 0, _b.FToBits(_b.Raw(Op.FExt, VT.F64, _b.BitsToF(src[0]))));
                return true;
            }
            case Mnemonic.Cvtpd2ps:
            {
                Node[] src = Lanes(ins, 1);
                Node d0 = _b.BitsToF(_b.Concat(src[1], src[0])), d1 = _b.BitsToF(_b.Concat(src[3], src[2]));
                SetLanes(ins.Op0Register,
                [
                    _b.FToBits(_b.Raw(Op.FTrunc, VT.F32, d0)), _b.FToBits(_b.Raw(Op.FTrunc, VT.F32, d1)), ZeroLane(), ZeroLane(),
                ]);
                return true;
            }

            case Mnemonic.Xorps or Mnemonic.Xorpd or Mnemonic.Pxor or Mnemonic.Andps or Mnemonic.Andpd or Mnemonic.Pand
                or Mnemonic.Orps or Mnemonic.Orpd or Mnemonic.Por or Mnemonic.Andnps or Mnemonic.Andnpd or Mnemonic.Pandn:
            {
                Register dst = ins.Op0Register;
                bool isXor = m is Mnemonic.Xorps or Mnemonic.Xorpd or Mnemonic.Pxor;
                if (isXor && ins.Op1Kind == OpKind.Register && ins.Op1Register == dst)
                {
                    SetLanes(dst, [ZeroLane(), ZeroLane(), ZeroLane(), ZeroLane()]);
                    return true;
                }
                Node[] b = Lanes(ins, 1);
                var result = new Node[4];
                for (int i = 0; i < 4; i++)
                {
                    Node a = Lane(dst, i);
                    result[i] = m switch
                    {
                        Mnemonic.Xorps or Mnemonic.Xorpd or Mnemonic.Pxor => _b.Xor(a, b[i]),
                        Mnemonic.Andps or Mnemonic.Andpd or Mnemonic.Pand => _b.And(a, b[i]),
                        Mnemonic.Orps or Mnemonic.Orpd or Mnemonic.Por => _b.Or(a, b[i]),
                        _ => _b.And(_b.Not(a), b[i]),
                    };
                }
                SetLanes(dst, result);
                return true;
            }

            case Mnemonic.Addps or Mnemonic.Subps or Mnemonic.Mulps or Mnemonic.Divps or Mnemonic.Minps or Mnemonic.Maxps:
            {
                Op op = m switch
                {
                    Mnemonic.Addps => Op.FAdd, Mnemonic.Subps => Op.FSub, Mnemonic.Mulps => Op.FMul,
                    Mnemonic.Divps => Op.FDiv, Mnemonic.Minps => Op.FMin, _ => Op.FMax,
                };
                Register dst = ins.Op0Register;
                Node[] b = Lanes(ins, 1);
                var result = new Node[4];
                for (int i = 0; i < 4; i++)
                    result[i] = _b.FToBits(_b.Raw(op, VT.F32, _b.BitsToF(Lane(dst, i)), _b.BitsToF(b[i])));
                SetLanes(dst, result);
                return true;
            }
            case Mnemonic.Addpd or Mnemonic.Subpd or Mnemonic.Mulpd or Mnemonic.Divpd:
            {
                Op op = m switch { Mnemonic.Addpd => Op.FAdd, Mnemonic.Subpd => Op.FSub, Mnemonic.Mulpd => Op.FMul, _ => Op.FDiv };
                Register dst = ins.Op0Register;
                Node[] b = Lanes(ins, 1);
                for (int half = 0; half < 2; half++)
                {
                    Node x = _b.BitsToF(Qword(dst, half));
                    Node y = _b.BitsToF(_b.Concat(b[half * 2 + 1], b[half * 2]));
                    SetQword(dst, half, _b.FToBits(_b.Raw(op, VT.F64, x, y)));
                }
                return true;
            }
            case Mnemonic.Paddd or Mnemonic.Psubd or Mnemonic.Pmulld:
            {
                Register dst = ins.Op0Register;
                Node[] b = Lanes(ins, 1);
                var result = new Node[4];
                for (int i = 0; i < 4; i++)
                    result[i] = m == Mnemonic.Paddd ? _b.Add(Lane(dst, i), b[i])
                        : m == Mnemonic.Psubd ? _b.Sub(Lane(dst, i), b[i])
                        : _b.Mul(Lane(dst, i), b[i]);
                SetLanes(dst, result);
                return true;
            }
            case Mnemonic.Paddq or Mnemonic.Psubq:
            {
                Register dst = ins.Op0Register;
                Node[] b = Lanes(ins, 1);
                for (int half = 0; half < 2; half++)
                {
                    Node y = _b.Concat(b[half * 2 + 1], b[half * 2]);
                    Node x = Qword(dst, half);
                    SetQword(dst, half, m == Mnemonic.Paddq ? _b.Add(x, y) : _b.Sub(x, y));
                }
                return true;
            }

            case Mnemonic.Shufps:
            {
                Register dst = ins.Op0Register;
                Node[] a = [Lane(dst, 0), Lane(dst, 1), Lane(dst, 2), Lane(dst, 3)];
                Node[] b = Lanes(ins, 1);
                int imm = (int)ins.GetImmediate(2);
                SetLanes(dst, [a[imm & 3], a[(imm >> 2) & 3], b[(imm >> 4) & 3], b[(imm >> 6) & 3]]);
                return true;
            }
            case Mnemonic.Pshufd:
            {
                Node[] b = Lanes(ins, 1);
                int imm = (int)ins.GetImmediate(2);
                SetLanes(ins.Op0Register, [b[imm & 3], b[(imm >> 2) & 3], b[(imm >> 4) & 3], b[(imm >> 6) & 3]]);
                return true;
            }
            case Mnemonic.Unpcklps or Mnemonic.Punpckldq:
            {
                Register dst = ins.Op0Register;
                Node[] b = Lanes(ins, 1);
                SetLanes(dst, [Lane(dst, 0), b[0], Lane(dst, 1), b[1]]);
                return true;
            }
            case Mnemonic.Unpckhps or Mnemonic.Punpckhdq:
            {
                Register dst = ins.Op0Register;
                Node[] b = Lanes(ins, 1);
                SetLanes(dst, [Lane(dst, 2), b[2], Lane(dst, 3), b[3]]);
                return true;
            }
            case Mnemonic.Unpcklpd or Mnemonic.Punpcklqdq:
            {
                Register dst = ins.Op0Register;
                Node[] b = Lanes(ins, 1);
                SetLanes(dst, [Lane(dst, 0), Lane(dst, 1), b[0], b[1]]);
                return true;
            }
            case Mnemonic.Unpckhpd or Mnemonic.Punpckhqdq:
            {
                Register dst = ins.Op0Register;
                Node[] b = Lanes(ins, 1);
                SetLanes(dst, [Lane(dst, 2), Lane(dst, 3), b[2], b[3]]);
                return true;
            }
            case Mnemonic.Psrldq or Mnemonic.Pslldq:
            {
                int bytes = Math.Min(16, (int)ins.GetImmediate(1));
                Register dst = ins.Op0Register;
                if (bytes % 4 == 0)
                {
                    int lanes = bytes / 4;
                    Node[] a = [Lane(dst, 0), Lane(dst, 1), Lane(dst, 2), Lane(dst, 3)];
                    var result = new Node[4];
                    for (int i = 0; i < 4; i++)
                    {
                        int from = m == Mnemonic.Psrldq ? i + lanes : i - lanes;
                        result[i] = from is >= 0 and < 4 ? a[from] : ZeroLane();
                    }
                    SetLanes(dst, result);
                    return true;
                }
                // General byte shift of the 128-bit value, written over its two 64-bit halves.
                Node lo = Qword(dst, 0), hi = Qword(dst, 1);
                Node zero = _b.Const(VT.I64, 0);
                Node Shr(Node v, int bits) => bits >= 64 ? zero : _b.Shift(Op.ShrU, v, _b.Const(VT.I8, bits));
                Node Shl(Node v, int bits) => bits >= 64 ? zero : _b.Shift(Op.Shl, v, _b.Const(VT.I8, bits));
                int shift = bytes * 8;
                if (m == Mnemonic.Psrldq)
                {
                    Node newLo = shift < 64 ? _b.Or(Shr(lo, shift), Shl(hi, 64 - shift)) : Shr(hi, shift - 64);
                    Node newHi = shift < 64 ? Shr(hi, shift) : zero;
                    SetQword(dst, 0, newLo);
                    SetQword(dst, 1, newHi);
                }
                else
                {
                    Node newHi = shift < 64 ? _b.Or(Shl(hi, shift), Shr(lo, 64 - shift)) : Shl(lo, shift - 64);
                    Node newLo = shift < 64 ? Shl(lo, shift) : zero;
                    SetQword(dst, 0, newLo);
                    SetQword(dst, 1, newHi);
                }
                return true;
            }
            case Mnemonic.Pextrw when ins.Op1Kind == OpKind.Register && ins.Op1Register.IsXMM():
            {
                int word = (int)ins.GetImmediate(2) & 7;
                Node lane = Lane(ins.Op1Register, word / 2);
                Node value = _b.And(_b.Shift(Op.ShrU, lane, _b.Const(VT.I8, word % 2 * 16)), _b.Const(VT.I32, 0xFFFF));
                WriteReg(ins.Op0Register.GetSize() == 8 ? ins.Op0Register.GetFullRegister32() : ins.Op0Register, value);
                return true;
            }
            case Mnemonic.Sqrtpd:
            {
                Node[] src = Lanes(ins, 1);
                for (int half = 0; half < 2; half++)
                {
                    Node x = _b.BitsToF(_b.Concat(src[half * 2 + 1], src[half * 2]));
                    SetQword(ins.Op0Register, half, _b.FToBits(_b.Raw(Op.FSqrt, VT.F64, x)));
                }
                return true;
            }
            case Mnemonic.Sqrtps:
            {
                Node[] src = Lanes(ins, 1);
                var result = new Node[4];
                for (int i = 0; i < 4; i++) result[i] = _b.FToBits(_b.Raw(Op.FSqrt, VT.F32, _b.BitsToF(src[i])));
                SetLanes(ins.Op0Register, result);
                return true;
            }
        }
        return false;
    }
}
