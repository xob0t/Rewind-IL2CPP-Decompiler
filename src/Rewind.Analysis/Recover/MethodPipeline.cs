using Rewind.Analysis.Abi;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;
using Rewind.Analysis.Runtime;
using Rewind.Analysis.X64;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>One method after lifting and cleanup, ready for translation into managed terms.</summary>
public sealed class LiftedMethod
{
    public MethodDef Method = null!;
    public TypeSig[] ClassArguments = [];
    public TypeSig[] MethodArguments = [];
    public MethodAbi Abi = null!;
    public Function Function = null!;
    public NormalizeResult Normalization = null!;
    public List<FrameObject> Frame = [];
}

/// <summary>Runs the per-method stages in order: lift, apply the calling convention, normalize, promote the stack.</summary>
public sealed class MethodPipeline
{
    private readonly ProgramAnalysis _program;
    private readonly IMachineLifter _lifter;
    private readonly Normalizer _normalizer;

    public MethodPipeline(ProgramAnalysis program) : this(program, forAccessors: false)
    {
    }

    /// <summary>
    /// <paramref name="forAccessors"/>: the pipeline that reads the candidates for a field's accessor
    /// (AccessorIndex). While it runs, no field has an accessor to ask for, so what it recovers on the way is not
    /// what another pipeline would recover: it is kept apart.
    /// </summary>
    internal MethodPipeline(ProgramAnalysis program, bool forAccessors)
    {
        _program = program;
        _lifter = program.NewLifter();
        _normalizer = new Normalizer(program);
        Kept = forAccessors ? program.KeptForAccessors : program.Kept;
    }

    /// <summary>What this pipeline's recoveries ask each other for, kept for every pipeline of its kind and every thread.</summary>
    internal RecoveryCache Kept { get; }

    /// <summary>
    /// What a recovered body uses, whatever the order and the temporaries: the methods it calls, the fields it
    /// touches, the types it makes and tests for, the numbers and texts in it, the kinds of arithmetic.
    /// </summary>
    internal static string Uses(HMethod h)
    {
        var used = new SortedSet<string>(StringComparer.Ordinal);
        void Note(HExpr e)
        {
            switch (e)
            {
                case HCall call: used.Add("call " + call.Method.FullName + "/" + call.Method.Parameters.Length); break;
                case HNewObject made: used.Add("new " + made.Constructor.DeclaringType.FullName + "/" + made.Constructor.Parameters.Length); break;
                case HNewArray array: used.Add("array of " + array.ElementType.Key); break;
                case HField field: used.Add("field " + field.Field.DeclaringType.FullName + "::" + field.Field.Name); break;
                case HTypeExpr type: used.Add("type " + type.Op + " " + type.Target.Key); break;
                case HMethodPointer pointer: used.Add("pointer to " + pointer.Method.FullName); break;
                case HMemberToken token: used.Add("token " + (token.Method?.FullName ?? token.Field?.Name)); break;
                case HOpaque native: used.Add("native " + native.Text); break;
                case HElement: used.Add("element"); break;
                case HArrayLength: used.Add("length"); break;
                case HBinary { Op: var op }: used.Add("op " + op); break;
                case HConst { Value: string text }: used.Add("text " + text); break;
                case HConst { Value: float or double } real: used.Add("real " + Convert.ToDouble(real.Value).ToString("R", System.Globalization.CultureInfo.InvariantCulture)); break;
                case HConst { Value: int or long or uint or ulong or short or ushort or byte or sbyte } number:
                {
                    long value = number.Value is ulong u ? unchecked((long)u) : Convert.ToInt64(number.Value);
                    if (value is < -1 or > 1) used.Add("number " + value);
                    break;
                }
            }
        }
        foreach (HBlock block in h.Blocks)
            foreach (HStmt s in block.Statements)
            {
                if (s is HThrow) used.Add("throw");
                if (s is HSwitch) used.Add("switch");
                FinallyFolding.Visit(s, Note);
            }
        return string.Join("\n", used);
    }

    /// <summary>
    /// The check for a function its caller names (it hands it a method's descriptor where that method takes its
    /// own): the caller says what the function is; what remains to be told is that it is not some other
    /// function that happens to take a descriptor there. A copy made for one source file is compiled apart
    /// from the original, so the two need not come out statement for statement alike. Read as the method - both
    /// completely - they must use the same things (<see cref="Uses"/>), and something at all.
    /// </summary>
    private bool VerifyNamed(ulong address, ulong[] originals)
    {
        foreach (ulong original in originals)
        {
            MethodDef? method = null;
            TypeSig[] classArgs = [], methodArgs = [];
            if (_program.Model.MethodsByAddress.TryGetValue(original, out List<MethodDef>? defs))
                method = defs.FirstOrDefault(m => m.DeclaringType.GenericParameters.Length == 0 && m.GenericParameters.Length == 0);
            if (method == null && _program.Model.InstsByAddress.TryGetValue(original, out List<MethodInst>? insts) && insts.Count != 0)
                (method, classArgs, methodArgs) = (insts[0].Method, insts[0].ClassArguments, insts[0].MethodArguments);
            if (method == null) continue;
            try
            {
                if (!_program.OwnUses.TryGetValue(original, out string? own))
                {
                    HMethod recovered = RecoverAt(method, classArgs, methodArgs, original);
                    _program.OwnUses[original] = own = recovered.Problems.Count == 0 ? Uses(recovered) : null;
                }
                if (string.IsNullOrEmpty(own)) return false;
                HMethod copy = RecoverAt(method, classArgs, methodArgs, address);
                return copy.Problems.Count == 0 && Uses(copy) == own;
            }
            catch (Exception e) when (e is not OutOfMemoryException and not StackOverflowException)
            {
                return false;
            }
        }
        return false;
    }

    /// <summary>For inspection: the listed method at <paramref name="original"/> recovered from its own code and from the code at <paramref name="address"/>.</summary>
    public (MethodDef? Method, HMethod? Own, HMethod? Copy, string? Error) RecoverBoth(ulong address, ulong original)
    {
        MethodDef? method = null;
        TypeSig[] classArgs = [], methodArgs = [];
        if (_program.Model.MethodsByAddress.TryGetValue(original, out List<MethodDef>? defs))
            method = defs.FirstOrDefault(m => m.DeclaringType.GenericParameters.Length == 0 && m.GenericParameters.Length == 0);
        if (method == null && _program.Model.InstsByAddress.TryGetValue(original, out List<MethodInst>? insts) && insts.Count != 0)
            (method, classArgs, methodArgs) = (insts[0].Method, insts[0].ClassArguments, insts[0].MethodArguments);
        if (method == null) return (null, null, null, "no listed method at that address");
        try
        {
            HMethod own = Build(Lift(method, classArgs, methodArgs, original));
            HMethod copy = Build(Lift(method, classArgs, methodArgs, address));
            return (method, own, copy, null);
        }
        catch (Exception e)
        {
            return (method, null, null, e.GetType().Name + ": " + e.Message + " @ " + e.StackTrace?.Split('\n').FirstOrDefault()?.Trim());
        }
    }

    /// <summary>Lifts and builds the method from the code at <paramref name="address"/>.</summary>
    private HMethod RecoverAt(MethodDef method, TypeSig[]? classArgs, TypeSig[]? methodArgs, ulong address)
    {
        // A definition's own type parameters as the arguments: the body its reference-type instantiations share
        // is being read, and there each of them stands for a reference type.
        HashSet<GenericParam>? own = null;
        foreach (TypeSig argument in (classArgs ?? []).Concat(methodArgs ?? []))
            if (argument is GenericParamSig parameter)
                (own ??= []).Add(parameter.Parameter);
        // (None of its own: none at all - also where this recovery was started from within such a one.)
        (HashSet<GenericParam>? builder, HashSet<GenericParam>? layouts) = (HirBuilder.OwnParameters, _program.Layouts.ReferenceParameters);
        (HirBuilder.OwnParameters, _program.Layouts.ReferenceParameters) = (own, own);
        ForgetOpen();
        long started = RecoveryStats.Begin();
        try
        {
            HMethod built = Build(Lift(method, classArgs, methodArgs, address));
            // Written as nothing but a call of a method that is itself nothing but such a call: see TwinOf.
            for (int round = 0; round < 8 && !NoTwins && !_probing && (TwinOf(built, address != 0 ? address : method.Address) ?? CallerPutBack(built)) is { } twin; round++)
            {
                if (!_barred.TryGetValue(method, out HashSet<MethodDef>? barred)) _barred[method] = barred = [];
                if (!barred.Add(twin)) break;
                built = Build(Lift(method, classArgs, methodArgs, address));
            }
            return built;
        }
        finally
        {
            RecoveryStats.End(RecoveryStats.Kind.Method, started);
            (HirBuilder.OwnParameters, _program.Layouts.ReferenceParameters) = (builder, layouts);
            ForgetOpen();
        }
    }

    private static readonly bool NoTwins = Environment.GetEnvironmentVariable("REWIND_NO_TWIN_CHECK") != null;
    private readonly Dictionary<MethodDef, HashSet<MethodDef>> _barred = [];
    private readonly Dictionary<MethodDef, MethodDef?> _passesOn = [];
    private bool _probing;

    /// <summary>The methods a method must not be written as a call of (null while the question is how it reads without that rule).</summary>
    internal HashSet<MethodDef>? BarredFor(MethodDef method) => _probing ? null : _barred.GetValueOrDefault(method);

    /// <summary>
    /// The method called, when the whole of a method was found to be the pasted-in statements of another and
    /// is now nothing but a call of that one.
    /// </summary>
    private static MethodDef? PassedOnTo(HMethod h)
    {
        if (h.PutBack == null || h.Problems.Count != 0 || h.Blocks.Count == 0 || h.TryRegions.Count != 0) return null;
        // (Its statements, through the jumps that only lead on to the next block.)
        var statements = new List<HStmt>();
        HBlock? block = h.Blocks[0];
        for (int guard = 0; block != null && guard < 8; guard++)
        {
            HBlock? next = null;
            foreach (HStmt s in block.Statements)
            {
                if (s is HJump jump) next = jump.Target;
                else statements.Add(s);
            }
            block = next;
        }
        if (block != null) return null;
        HExpr? only = statements switch
        {
            [HEval { Expression: var e }, HReturn { Value: null }] => e,
            [HReturn { Value: { } e }] => e,
            [HAssign { Target: HLocal { Variable: var set }, Value: var e }, HReturn { Value: HLocal { Variable: var returned } }] when ReferenceEquals(set, returned) => e,
            _ => null,
        };
        return only is HCall call && h.PutBack.Contains(call.Method) && !ReferenceEquals(call.Method, h.Method) ? call.Method : null;
    }

    /// <summary>The method that a method, read without the rules below, comes out as nothing but a call of (having its statements); null when it is more than that.</summary>
    private MethodDef? PassesOnTo(MethodDef method)
    {
        if (_passesOn.TryGetValue(method, out MethodDef? known)) return known;
        if (method.Address == 0 || method.DeclaringType.GenericParameters.Length != 0 || method.GenericParameters.Length != 0) return null;
        _passesOn[method] = null; // asked again while it is being read: no
        MethodDef? passes = null;
        (HashSet<GenericParam>? builder, HashSet<GenericParam>? layouts) = (HirBuilder.OwnParameters, _program.Layouts.ReferenceParameters);
        (HirBuilder.OwnParameters, _program.Layouts.ReferenceParameters) = (null, null);
        ForgetOpen();
        bool probing = _probing;
        _probing = true;
        // (How the method reads on its own: a check for a copy of a method that is under way where this was
        // asked is not under way here.)
        _program.Auxiliary++;
        long started = RecoveryStats.Begin();
        try
        {
            passes = PassedOnTo(Build(Lift(method)));
        }
        catch (Exception e) when (e is not OutOfMemoryException and not StackOverflowException)
        {
            passes = null;
        }
        finally
        {
            RecoveryStats.End(RecoveryStats.Kind.Passing, started);
            _program.Auxiliary--;
            _probing = probing;
            (HirBuilder.OwnParameters, _program.Layouts.ReferenceParameters) = (builder, layouts);
            ForgetOpen();
        }
        return _passesOn[method] = passes;
    }

    /// <summary>
    /// How much a method looks like one whose source was a single call of another, where the code of the two
    /// is the same and cannot tell: one the compiler made (a lambda), one with more parameters (a call from one
    /// with fewer would have to make their values up), one the engine or a base class calls by name or slot, one
    /// that more code can see.
    /// </summary>
    private static int PassingRank(MethodDef m)
    {
        bool made = m.Name.Contains('<') || m.DeclaringType.Name.Contains('<');
        bool message = !m.IsStatic && (m.IsVirtual || m.Name is "Awake" or "Start" or "Update" or "FixedUpdate" or "LateUpdate" or "OnEnable" or "OnDisable" or "OnDestroy"
            or "OnValidate" or "Reset" or "OnGUI" or "OnApplicationQuit" or "OnApplicationPause" or "OnApplicationFocus" or "Spawned" or "Despawned" or "FixedUpdateNetwork" or "Render");
        int access = (m.Flags & MethodDef.AccessMask) switch { 6 => 3, 5 or 4 => 2, 3 or 2 => 1, _ => 0 };
        return (made ? 1000 : 0) + Math.Min(m.Parameters.Length, 9) * 100 + (message ? 10 : 0) + access;
    }

    /// <summary>
    /// Two methods with the same statements - one function in the image (the linker keeps one copy of identical
    /// code), or each with the other, or the same third one, pasted in - would each be found to be the pasted-in
    /// statements of the other, and each be written as a call of the other: a method that calls itself without
    /// end. Which of them called which, the code does not say. So a method that has become nothing but a call of
    /// another, which read on its own would be such a call too, stays that only if it looks more like the
    /// caller of the two (PassingRank); otherwise it keeps its statements. Returns the method it must not be a
    /// call of.
    /// </summary>
    private MethodDef? TwinOf(HMethod built, ulong address)
    {
        if (PassedOnTo(built) is not { } target) return null;
        MethodDef method = built.Method;
        bool generic = target.DeclaringType.GenericParameters.Length != 0 || target.GenericParameters.Length != 0;
        bool twin = generic ? target.Address != 0 && target.Address == address : PassesOnTo(target) != null;
        if (!twin) return null;
        return PassingRank(method) > PassingRank(target) ? null : target;
    }

    /// <summary>
    /// The same in part: statements of a method were found to be the pasted-in statements of another and put
    /// back as a call of it - of one that is itself nothing but a call of this method ("int Count => _count;"
    /// seen in the getter of _count). Those statements are this method's own: the other one has them because
    /// this one was pasted into it. Returns that other method, which this one must not be written as a call of.
    /// </summary>
    private MethodDef? CallerPutBack(HMethod built)
    {
        if (built.PutBack == null) return null;
        MethodDef method = built.Method;
        foreach (MethodDef other in built.PutBack)
        {
            if (ReferenceEquals(other, method) || (_barred.TryGetValue(method, out HashSet<MethodDef>? barred) && barred.Contains(other))) continue;
            // (A method that only passes a call on to one of another class does so through something of its
            // own - a field, a parameter: its statements are not found in that one as they stand.)
            if (!Related(other.DeclaringType, method.DeclaringType)) continue;
            if (ReferenceEquals(PassesOnTo(other), method)) return other;
        }
        return null;
    }

    private static bool Related(TypeDef a, TypeDef b)
    {
        int guard = 0;
        for (TypeDef? t = a; t != null && guard++ < 64; t = t.BaseType?.Definition)
            if (ReferenceEquals(t, b)) return true;
        guard = 0;
        for (TypeDef? t = b; t != null && guard++ < 64; t = t.BaseType?.Definition)
            if (ReferenceEquals(t, a)) return true;
        return false;
    }

    public LiftedMethod Lift(MethodDef method, TypeSig[]? classArgs = null, TypeSig[]? methodArgs = null, ulong address = 0)
    {
        classArgs ??= [];
        methodArgs ??= [];
        MethodAbi abi = _program.Abi.For(method, classArgs, methodArgs);
        Function fn = _lifter.Lift(address != 0 ? address : method.Address);
        CheckShape(fn, "lifting");
        // (Landing pads: only calls raise exceptions, so what a try statement stores before its first call is
        // stored before it.)
        if (!fn.Regs.SharedPositions && Environment.GetEnvironmentVariable("REWIND_NO_TRY_PROLOGUES") == null) TryPrologues.Run(fn);
        MathCalls.Run(fn, _program.Helpers);
        TrimReturns(fn, abi);
        NormalizeResult normalization = _normalizer.Run(fn);
        CheckShape(fn, "normalizing");
        if (Environment.GetEnvironmentVariable("REWIND_NO_CONSTANT_DIVISIONS") == null && ConstantDivisions.Run(fn)) DeadCode.Run(fn);
        if (Environment.GetEnvironmentVariable("REWIND_NO_ARG_TRIM") == null && TrimCallArguments(fn))
        {
            DeadCode.Run(fn);
            _normalizer.Cleanup(fn);
        }
        if (Environment.GetEnvironmentVariable("REWIND_NO_LEFTOVERS") == null && UndefinedValues.Run(fn, Leftovers(fn, abi), deadArguments: !fn.Regs.SharedPositions))
        {
            DeadCode.Run(fn);
            _normalizer.Cleanup(fn);
        }
        if (Environment.GetEnvironmentVariable("REWIND_NO_BLOCK_COPIES") == null)
        {
            if (BlockCopies.CollapseLoops(fn)) _normalizer.Cleanup(fn);
            if (BlockCopies.Extend(fn)) DeadCode.Run(fn);
            CheckShape(fn, "block copies");
        }
        if (Environment.GetEnvironmentVariable("REWIND_NO_LEAVE_TARGETS") == null && LeaveTargets.Run(fn)) _normalizer.Cleanup(fn);
        if (Environment.GetEnvironmentVariable("REWIND_NO_EXCEPTION_STACKS") == null && ExceptionStacks.Run(fn, _program.Helpers)) _normalizer.Cleanup(fn);
        CheckShape(fn, "exception stacks");
        Dictionary<int, int> boxes = InPlaceBoxes(fn);
        if (Environment.GetEnvironmentVariable("REWIND_NO_PARKED") == null && ParkedAddresses.Run(fn, (call, input) => EscapeExtent(call, input, fn, boxes)))
        {
            DeadCode.Run(fn);
            _normalizer.Cleanup(fn);
        }
        CheckShape(fn, "parked addresses");
        ParkedAddresses.Canonicalize(fn);
        Dictionary<int, int>? stackArguments = StackArguments(abi, fn.Regs);
        List<FrameObject> frame = StackPromotion.Run(fn, (call, input) => EscapeExtent(call, input, fn, boxes), stackArguments);
        DeadCode.Run(fn);
        // A promoted slot that held a stack address turns what was read through it into direct stack accesses:
        // with those in view, more can be promoted.
        for (int again = 0; again < 2 && ParkedAddresses.Canonicalize(fn); again++)
        {
            frame = StackPromotion.Run(fn, (call, input) => EscapeExtent(call, input, fn, boxes), stackArguments);
            DeadCode.Run(fn);
        }
        _normalizer.Cleanup(fn);
        CheckShape(fn, "stack promotion");
        if (LoopValues.Run(fn, ArgumentBits)) _normalizer.Cleanup(fn);
        CheckShape(fn, "loop values");
        if (Environment.GetEnvironmentVariable("REWIND_NO_CLASS_SPLIT") == null && ClassMerges.Run(fn, IsClassOrMethodSlot,
                fn.Regs.SharedPositions ? null : slot => _program.Model.ResolveUsageSlot(slot) != null))
        {
            // The copies read their own slots now: those reads are the slots' values.
            _normalizer.CanonicalizeSlots(fn);
            _normalizer.Cleanup(fn);
        }
        CheckShape(fn, "class merges");
        if (Environment.GetEnvironmentVariable("REWIND_NO_WIDENED_CONSTANTS") == null) FoldWidenedConstants(fn);
        return new LiftedMethod
        {
            Method = method,
            ClassArguments = classArgs,
            MethodArguments = methodArgs,
            Abi = abi,
            Function = fn,
            Normalization = normalization,
            Frame = frame,
        };
    }

    /// <summary>
    /// A constant made wider or narrower is a constant. The passes above can leave one standing as an operation
    /// (a register found to hold zero wherever it is read, behind the "mov ecx, r13d" that reads it): what asks
    /// "is this a constant?" - the slot number handed to an interface call, a size, a shift count - then says no.
    /// </summary>
    private static void FoldWidenedConstants(Function fn)
    {
        Dictionary<Node, Node>? replace = null;
        for (int round = 0; round < 4; round++)
        {
            bool any = false;
            foreach (Block b in fn.Blocks)
                foreach (Node n in b.Nodes)
                {
                    if (n.Dead || n.Op is not (Op.ZExt or Op.SExt or Op.Trunc) || n.In.Length != 1 || !n.Type.IsInt()) continue;
                    Node from = n.In[0];
                    while (replace != null && replace.TryGetValue(from, out Node? known)) from = known;
                    if (!from.IsConst || !from.Type.IsInt() || from.Type == VT.I1 || n.Type == VT.I1) continue;
                    long value = n.Op == Op.SExt ? IrBuilder.SImm(from) : (long)from.UImm;
                    Node constant = fn.NewNode(Op.Const, n.Type, null);
                    constant.Imm = n.Type.Bits() >= 64 ? value : (long)((ulong)value & n.Type.Mask());
                    (replace ??= [])[n] = constant;
                    n.Dead = true;
                    any = true;
                }
            if (!any) break;
        }
        if (replace == null) return;
        Node Resolve(Node n)
        {
            while (replace.TryGetValue(n, out Node? next)) n = next;
            return n;
        }
        foreach (Block b in fn.Blocks)
        {
            foreach (Node n in b.Phis)
                for (int i = 0; i < n.In.Length; i++) n.In[i] = Resolve(n.In[i]);
            foreach (Node n in b.Nodes)
                for (int i = 0; i < n.In.Length; i++) n.In[i] = Resolve(n.In[i]);
            b.Nodes.RemoveAll(n => n.Dead);
        }
    }

    /// <summary>The arguments a method is handed on the stack: where (from the entry stack pointer), and how many bytes of the slot they are.</summary>
    private static Dictionary<int, int>? StackArguments(MethodAbi abi, RegisterModel regs)
    {
        if (!abi.Known) return null;
        Dictionary<int, int>? result = null;
        foreach (AbiParam p in abi.Params)
        {
            if (p.Role != ParamRole.Argument || !regs.IsStackPosition(p.Position)) continue;
            int bytes = p.Pass switch
            {
                PassKind.Indirect => 8,
                PassKind.Float => p.IsDouble ? 8 : 4,
                _ => p.Size is 1 or 2 or 4 or 8 ? p.Size : 8,
            };
            // (Win64: above the return address and the four slots kept for the arguments that come in registers.)
            (result ??= [])[regs.StackOffsetOf(p.Position)] = bytes;
        }
        return result;
    }

    private static readonly bool CheckShapes = Environment.GetEnvironmentVariable("REWIND_CHECK_SHAPE") != null;

    /// <summary>
    /// Debugging aid (REWIND_CHECK_SHAPE): after each stage, every merged value must have one input per way into
    /// its block, and edges must be recorded at both ends. Reports the first stage that breaks this.
    /// </summary>
    private static void CheckShape(Function fn, string stage)
    {
        if (!CheckShapes || fn.Problems.Any(p => p.StartsWith("shape broken", StringComparison.Ordinal))) return;
        foreach (Block b in fn.Blocks)
        {
            foreach (Node phi in b.Phis)
                if (!phi.Dead && phi.In.Length != b.Preds.Count)
                {
                    fn.Problems.Add($"shape broken after {stage}: {phi} in {b} has {phi.In.Length} inputs for {b.Preds.Count} predecessors");
                    return;
                }
            foreach (Block s in b.Succs)
                if (!s.Preds.Contains(b) || !fn.Blocks.Contains(s))
                {
                    fn.Problems.Add($"shape broken after {stage}: edge {b} -> {s} is not recorded at its target");
                    return;
                }
            foreach (Block p in b.Preds)
                if (!p.Succs.Contains(b) || !fn.Blocks.Contains(p))
                {
                    fn.Problems.Add($"shape broken after {stage}: edge {p} -> {b} is not recorded at its source");
                    return;
                }
        }
    }

    public HMethod Recover(MethodDef method) => RecoverAt(method, null, null, 0);

    /// <summary>Recovers the body compiled for one instantiation of a generic method (or method of a generic type).</summary>
    public HMethod Recover(MethodInst inst) => RecoverAt(inst.Method, inst.ClassArguments, inst.MethodArguments, inst.Address);

    private GuardedAccessorFolding? _guardedAccessors;
    private InlineFolding? _inlineFolding;
    private static readonly bool NoStructsAgain = Environment.GetEnvironmentVariable("REWIND_NO_STRUCTS_AFTER_GUARDS") != null;

    private HMethod Build(LiftedMethod lifted)
    {
        _program.Building++;
        try
        {
            return BuildAll(lifted);
        }
        finally
        {
            _program.Building--;
        }
    }

    private static readonly bool NoUnkeptFolds = Environment.GetEnvironmentVariable("REWIND_NO_UNKEPT_FOLDS") != null;

    /// <summary>
    /// An instance method called on an object the code did not keep (see HirBuilder.UnkeptReceiver): the code
    /// the method shares never reads its object. Where the method's own recovered body is one "return E", and
    /// E names nothing of the method's own - no argument, not the object, no variable - the call gives E
    /// whatever it was called on, and is E. The mark goes with the call.
    /// </summary>
    private void FoldUnkeptReceivers(HMethod result)
    {
        if (NoUnkeptFolds) return;
        int marked = result.Problems.Count(p => p == HirBuilder.UnkeptReceiver);
        // (Problems past the 64th are not kept: then it cannot be told which calls are marked.)
        if (marked == 0 || result.Problems.Count >= 64) return;
        int folded = 0;
        HExpr? Map(HExpr e)
        {
            if (e is not HCall { This: HConst { Value: null }, Method: { IsStatic: false } method, DeclaringType: null, MethodArguments.Length: 0 } call ||
                call.Arguments.Any(a => !HirBuilder.IsPure(a)))
                return null;
            if (CoreBody(method) is not { Blocks: [{ Statements: [HReturn { Value: { } value }] }] }) return null;
            bool own = false;
            FinallyFolding.Visit(value, x => own |= x is HArg or HLocal);
            if (own) return null;
            folded++;
            return HirCopy.Of(value);
        }
        foreach (HBlock block in result.Blocks)
            foreach (HStmt s in block.Statements)
                EnumeratorLoops.Rewrite(s, Map);
        for (int i = 0; i < Math.Min(folded, marked); i++) result.Problems.Remove(HirBuilder.UnkeptReceiver);
    }

    private HMethod BuildAll(LiftedMethod lifted)
    {
        // The method asked for: nothing else is being built around it.
        bool before = _program.OwnTranslation;
        Func<ulong, ulong[], bool>? verifier = _program.NamedVerifier;
        _program.OwnTranslation = _program.Building == 1;
        _program.NamedVerifier = VerifyNamed; // asked while this pipeline translates (it is not lifting then): it can do the reading
        HMethod result;
        try
        {
            result = BuildCore(lifted);
        }
        finally
        {
            _program.OwnTranslation = before;
            _program.NamedVerifier = verifier;
        }
        FoldUnkeptReceivers(result);
        // A networked property read in the middle of a struct being filled kept the stores apart (its check is a
        // branch): with the read put back they are one run, which may be one struct made in one go.
        if ((_guardedAccessors ??= new GuardedAccessorFolding(this)).Run(result) && !NoStructsAgain) StructFolding.Run(result, _program, this);
        ElementParts.Run(result);
        Inline.Run(result);
        if (WrapperFolding.Lift(result, this))
        {
            StructFolding.Run(result, _program, this);
            _inlineFolding.Run(result);
        }
        StructFromParts.Run(result, this);
        WriteBacks.Run(result, _program);
        AccessorFolding.Run(result, _program);
        LibraryInternals.Run(result, _program);
        HiddenImplementations.Run(result, _program);
        BaseConstructorCalls.Run(result, this, _program);
        InitializerOrder.Run(result);
        UnsetLocals.Run(result);
        FlagMarkers(result);
        return result;
    }

    /// <summary>
    /// Whatever is still expressed as a native operation in the finished method is a gap, whether or not the
    /// step that left it there said so: the rebuilt code stops when it gets there. Only the filler after a
    /// call that never returns is exempt, since nothing reaches it.
    ///
    /// The other way round, a problem reported with a marker at its site (HMethod.SiteProblems) whose markers
    /// are all gone went with the code that had it: what is left was recovered, and a note saying otherwise
    /// would point at no gap in it.
    /// </summary>
    private static readonly bool NoSiteProblems = Environment.GetEnvironmentVariable("REWIND_NO_SITE_PROBLEMS") != null;

    private static void FlagMarkers(HMethod method)
    {
        HashSet<string>? found = null;
        HashSet<string>? sited = null;
        void Visit(HExpr? e)
        {
            switch (e)
            {
                case null: return;
                case HOpaque o:
                    if (o.Text != "unreachable") (found ??= []).Add(o.Text);
                    if (o.Problem != null) (sited ??= []).Add(o.Problem);
                    foreach (HExpr a in o.Operands) Visit(a);
                    return;
                case HField f: Visit(f.Object); return;
                case HElement el: Visit(el.Array); Visit(el.Index); return;
                case HArrayLength len: Visit(len.Array); return;
                case HAddressOf a: Visit(a.Target); return;
                case HDeref d: Visit(d.Pointer); return;
                case HUnary u: Visit(u.Operand); return;
                case HBinary b: Visit(b.Left); Visit(b.Right); return;
                case HCompare c: Visit(c.Left); Visit(c.Right); return;
                case HConv c: Visit(c.Operand); return;
                case HCall call: Visit(call.This); foreach (HExpr a in call.Arguments) Visit(a); return;
                case HNewObject n: foreach (HExpr a in n.Arguments) Visit(a); return;
                case HNewArray na: Visit(na.Length); return;
                case HTypeExpr t: Visit(t.Operand); return;
                case HSelect s: Visit(s.Condition); Visit(s.WhenTrue); Visit(s.WhenFalse); return;
            }
        }
        foreach (HBlock block in method.Blocks)
        {
            foreach (HStmt s in block.Statements)
            {
                switch (s)
                {
                    case HAssign a: Visit(a.Target); Visit(a.Value); break;
                    case HEval e: Visit(e.Expression); break;
                    case HReturn r: Visit(r.Value); break;
                    case HThrow t: Visit(t.Exception); break;
                    case HBranch b: Visit(b.Condition); break;
                    case HSwitch sw: Visit(sw.Value); break;
                }
            }
        }
        // (Not when problems were dropped for want of room: then it cannot be told which are left.)
        if (!NoSiteProblems && method.SiteProblems.Count != 0 && method.Problems.Count < 64)
            method.Problems.RemoveAll(p => method.SiteProblems.Contains(p) && !(sited?.Contains(p) ?? false));
        if (found == null || method.Problems.Count != 0) return;
        // Nothing reported this method as incomplete, yet it is.
        foreach (string text in found) method.Problems.Add($"native operation left in the code ({text})");
    }

    private static readonly bool NoSharedConstructors = Environment.GetEnvironmentVariable("REWIND_NO_SHARED_CONSTRUCTORS") != null;

    /// <summary>The type argument whose code a type argument's code is shared with: "object" for a reference type (in a struct's arguments too).</summary>
    private TypeSig Shared(TypeSig type)
    {
        if (type is PointerSig or ByRefSig or GenericParamSig or OpaqueSig) return type;
        if (!type.IsValueType) return _program.Model.Sigs.Primitive(Rewind.Runtime.Il2CppTypeEnum.Object);
        if (type is GenericInstSig g)
        {
            TypeSig[] arguments = g.Arguments.Select(Shared).ToArray();
            return arguments.SequenceEqual(g.Arguments) ? type : _program.Model.Sigs.GenericInst(g.Definition, arguments);
        }
        return type;
    }

    internal static readonly bool NoConstructorFlows = Environment.GetEnvironmentVariable("REWIND_NO_CONSTRUCTOR_FLOWS") != null;

    // ---- what recoveries ask each other for -------------------------------------------------------------------
    //
    // The recovered statements of another method - to compare pasted code with, to read an accessor from, to put
    // a constructor back - are the same for whoever asks, so they are kept, and kept for every thread
    // (RecoveryCache). For that they must not depend on who asked first, on the order the methods are recovered
    // in, or on the thread. One thing could make them: a recovery for another's use asks for others in turn (a
    // constructor makes an object, whose constructor makes another ...), and that has to end somewhere - two
    // constructors may each make the other. It ends by depth: the method asked for may ask so many deep
    // (Depth), what it asks for one less, and so on down to a recovery that is refused whatever it asks for. A
    // body is then what it is for the depth it has left, and for nothing else.
    //
    // Most never get near the end. A body that was recovered with nothing refused below it is the same at every
    // depth that is at least what it used, and is kept once for all of them; only one that something was
    // refused to is kept for its depth alone. (Ending at what is under way further up instead - a constructor
    // is not recovered inside itself - makes a body depend on everything under way when it was asked for: among
    // many constructors that make each other that is a different body for every way to get there.)

    /// <summary>How many recoveries for the use of another may be under way inside one another.</summary>
    private static readonly int Depth =
        int.TryParse(Environment.GetEnvironmentVariable("REWIND_ASK_DEPTH"), out int depth) && depth >= 0 ? depth : 4;

    private sealed class Asking
    {
        /// <summary>How deep the recoveries went that this one asked for (0: it asked for none).</summary>
        public int Used;
        /// <summary>Whether this one, or one it asked for, was refused something because the depth was used up.</summary>
        public bool Cut;
    }

    private readonly List<Asking> _asking = [];
    /// <summary>How deep recoveries for the use of another may still go from here.</summary>
    private int _left = Depth;

    /// <summary>Whether no recovery for the use of another is under way: what is made now is made the same anywhere.</summary>
    internal bool NothingUnderWay => _asking.Count == 0;

    private static void Note(Asking? outer, int used, bool cut)
    {
        if (outer == null) return;
        outer.Used = Math.Max(outer.Used, used + 1);
        outer.Cut |= cut;
    }

    /// <summary>
    /// The statements of a method, for another recovery: the kept ones, else recovered now and kept. Null also
    /// where the depth is used up. <paramref name="kept"/> null: made anew every time, for the caller to change.
    /// </summary>
    private HMethod? Ask<TKey>(IDictionary<(TKey Key, int Left), RecoveryCache.Body>? kept, TKey key, RecoveryStats.Kind kind, Func<HMethod?> recover)
        where TKey : notnull
    {
        Asking? outer = _asking.Count != 0 ? _asking[^1] : null;
        if (_left == 0)
        {
            if (outer != null) outer.Cut = true;
            return null;
        }
        int left = _left - 1; // how deep what is asked for may ask in turn
        if (kept != null &&
            ((kept.TryGetValue((key, RecoveryCache.Whole), out RecoveryCache.Body? known) && known.Used <= left) || kept.TryGetValue((key, left), out known)))
        {
            Note(outer, known.Used, known.Cut);
            return known.Statements;
        }
        var asking = new Asking();
        _asking.Add(asking);
        _left = left;
        _program.Auxiliary++;
        HMethod? body = null;
        long started = RecoveryStats.Begin();
        try
        {
            body = recover();
        }
        catch (Exception)
        {
            body = null;
        }
        finally
        {
            RecoveryStats.End(kind, started);
            _program.Auxiliary--;
            _left = left + 1;
            _asking.RemoveAt(_asking.Count - 1);
            Note(outer, asking.Used, asking.Cut);
        }
        if (kept == null) return body;
        var made = new RecoveryCache.Body(body, asking.Used, asking.Cut);
        if (RecoveryCache.Check && body != null) made.Text = HirPrinter.Print(body);
        (TKey, int) at = (key, asking.Cut ? left : RecoveryCache.Whole);
        if (kept is System.Collections.Concurrent.ConcurrentDictionary<(TKey Key, int Left), RecoveryCache.Body> shared) return shared.GetOrAdd(at, made).Statements;
        kept[at] = made;
        return body;
    }

    /// <summary>
    /// Bodies for type arguments that name a type parameter: constructors of a generic class, and methods. What
    /// a type parameter stands for is known only to the recovery under way (RecoverAt): these are kept for that
    /// one alone.
    /// </summary>
    private readonly Dictionary<((MethodDef Constructor, string Arguments) Key, int Left), RecoveryCache.Body> _openConstructors = [];
    private readonly Dictionary<(MethodInst Key, int Left), RecoveryCache.Body> _openInstances = [];

    private void ForgetOpen()
    {
        if (_openConstructors.Count != 0) _openConstructors.Clear();
        if (_openInstances.Count != 0) _openInstances.Clear();
    }

    private InlineFolding Inline => _inlineFolding ??= new InlineFolding(this, _program);

    /// <summary>
    /// The recovered statements of a constructor, when they are complete and a plain run without branches:
    /// what a creation site is compared with to put an inlined constructor back.
    /// </summary>
    internal HMethod? ConstructorBody(MethodDef constructor, TypeSig[] classArguments) =>
        ConstructorFlow(constructor, classArguments) is { Blocks: [{ Statements: [.., HReturn { Value: null }] }] } body ? body : null;

    /// <summary>
    /// The recovered statements of a constructor, when they are complete, branches and all: what a creation site
    /// is compared with along every way through it (ConstructorFolding).
    /// </summary>
    internal HMethod? ConstructorFlow(MethodDef constructor, TypeSig[] classArguments)
    {
        string key = classArguments.Length == 0 ? "" : string.Join(",", classArguments.Select(a => a.Key));
        bool open = false;
        foreach (TypeSig argument in classArguments) open |= argument.ContainsGenericParameter;
        IDictionary<((MethodDef Constructor, string Arguments) Key, int Left), RecoveryCache.Body> kept = open ? _openConstructors : Kept.Constructors;
        return Ask(kept, (constructor, key), RecoveryStats.Kind.Constructor, () =>
        {
            LiftedMethod? lifted = null;
            if (constructor.DeclaringType.GenericParameters.Length == 0)
            {
                if (constructor.Address != 0) lifted = Lift(constructor);
            }
            else
            {
                // The instantiation's own code - or, for reference types among the type arguments, the code
                // they share (every class runs what was made for "object").
                for (int form = 0; form < (NoSharedConstructors ? 1 : 2) && lifted == null; form++)
                {
                    TypeSig[] wanted = form == 0 ? classArguments : classArguments.Select(Shared).ToArray();
                    if (form == 1 && wanted.SequenceEqual(classArguments)) break;
                    foreach (MethodInst inst in _program.InstsOf(constructor))
                    {
                        if (inst.Address == 0 || inst.MethodArguments.Length != 0 || inst.ClassArguments.Length != wanted.Length) continue;
                        bool same = true;
                        for (int i = 0; i < wanted.Length && same; i++) same = ReferenceEquals(inst.ClassArguments[i], wanted[i]);
                        if (!same) continue;
                        lifted = Lift(inst.Method, inst.ClassArguments, inst.MethodArguments, inst.Address);
                        break;
                    }
                }
            }
            if (lifted == null) return null;
            HMethod h = BuildCore(lifted);
            return h.Problems.Count == 0 && h.Blocks.Count != 0 && h.TryRegions.Count == 0 &&
                   (h.Blocks.Count == 1 ? h.Blocks[0].Statements is [.., HReturn { Value: null }] : !NoConstructorFlows)
                ? h
                : null;
        });
    }

    /// <summary>
    /// The recovered statements of a method as they stand before accessors are put back into them - what code
    /// pasted from that method into another looks like there - with a struct parameter that arrives in pieces
    /// whole again (InlineFolding.WholeParameters). Null when the method has no code of its own or was not
    /// recovered completely. They are everybody's: not to be changed (see FreshCoreBody).
    /// </summary>
    internal HMethod? CoreBody(MethodDef method)
    {
        if (method.Address == 0 || method.DeclaringType.GenericParameters.Length != 0 || method.GenericParameters.Length != 0) return null;
        return Ask(Kept.Methods, method, RecoveryStats.Kind.Body, () =>
        {
            HMethod h = BuildCore(Lift(method));
            if (h.Problems.Count != 0) return null;
            if (!method.IsConstructor && method.Name != ".cctor") Inline.WholeParameters(h);
            return h;
        });
    }

    /// <summary>
    /// CoreBody for one instantiation of a method of a generic class: the statements the code compiled for those
    /// type arguments gives. Null when it was not recovered completely.
    /// </summary>
    internal HMethod? CoreBody(MethodInst inst)
    {
        if (inst.Address == 0) return null;
        bool open = false;
        foreach (TypeSig argument in inst.ClassArguments) open |= argument.ContainsGenericParameter;
        foreach (TypeSig argument in inst.MethodArguments) open |= argument.ContainsGenericParameter;
        IDictionary<(MethodInst Key, int Left), RecoveryCache.Body> kept = open ? _openInstances : Kept.Instances;
        return Ask(kept, inst, RecoveryStats.Kind.Body, () =>
        {
            HMethod h = BuildCore(Lift(inst.Method, inst.ClassArguments, inst.MethodArguments, inst.Address));
            if (h.Problems.Count != 0) return null;
            if (!inst.Method.IsConstructor && inst.Method.Name != ".cctor") Inline.WholeParameters(h);
            return h;
        });
    }

    /// <summary>The same statements as CoreBody gives before a parameter is made whole, made anew: the caller's own, to change as it likes.</summary>
    internal HMethod? FreshCoreBody(MethodDef method)
    {
        if (method.Address == 0 || method.DeclaringType.GenericParameters.Length != 0 || method.GenericParameters.Length != 0) return null;
        return Ask<MethodDef>(null, method, RecoveryStats.Kind.Fresh, () =>
        {
            HMethod h = BuildCore(Lift(method));
            return h.Problems.Count == 0 ? h : null;
        });
    }

    /// <summary>Everything up to, but not including, the rewriting of private field accesses into accessor calls.</summary>
    private HMethod BuildCore(LiftedMethod lifted)
    {
        _program.Translations++;
        try
        {
            return BuildCoreOf(lifted);
        }
        finally
        {
            _program.Translations--;
        }
    }

    private static readonly bool NoLoopValuesAgain = Environment.GetEnvironmentVariable("REWIND_NO_LOOP_VALUES_AGAIN") != null;
    private static readonly bool NoAssumedReach = Environment.GetEnvironmentVariable("REWIND_NO_ASSUMED_REACH") != null;
    private static readonly bool NoUntakenInputs = Environment.GetEnvironmentVariable("REWIND_NO_UNTAKEN_INPUTS") != null;

    private HMethod BuildCoreOf(LiftedMethod lifted)
    {
        (HirBuilder builder, HMethod result) = BuildRounds(lifted);
        // Code for two classes merged because their fields sit at the same offsets: un-merge and build again.
        for (int round = 0; round < 2 && builder.MergedObjects.Count != 0; round++)
        {
            if (!ClassMerges.SplitAt(lifted.Function, builder.MergedObjects)) break;
            _normalizer.Cleanup(lifted.Function);
            (builder, result) = BuildRounds(lifted);
        }
        // Stack memory that reads as two different things is usually a slot the compiler reused: give each
        // lifetime its own memory and build again.
        // (Separating one pair of lifetimes can show the next - a temporary that serves as the result of one
        // call and then of another - so this repeats a few times.)
        Function fn = lifted.Function;
        // A call nothing is known about, handed the address of a stack object: it is taken to reach that
        // object as far as its other uses show it to extend, not everything above it - an unknown call would
        // otherwise make one object of the whole frame, and what keeps the call unknown may be the very slot
        // that needs separating (a delegate kept where a struct was). Checked against the last build (below).
        var assumed = new List<(Node Call, int Input, int Reach)>();
        for (int round = 0; round < 3 && builder.FrameConflicts.Count != 0; round++)
        {
            ParkedAddresses.Canonicalize(fn);
            Dictionary<int, int> boxes = InPlaceBoxes(fn);
            HirBuilder current = builder;
            int Extent(Node call, int input)
            {
                int extent = EscapeExtent(call, input, fn, boxes, current);
                if (extent > 0 || extent == StackPromotion.NotTaken || NoAssumedReach || call.Aux is not CallInfo { Indirect: true } ||
                    current.ChosenCalls.ContainsKey(call)) return extent;
                if (!fn.Params.TryGetValue(fn.Regs.StackPointer, out Node? sp0) || StackOffset(sp0, call.In[input]) is not int at) return extent;
                int reach = current.ReachThrough(at);
                if (reach <= 0) return extent;
                assumed.Add((call, input, reach));
                return reach;
            }
            if (StackSplitting.Run(fn, current.FrameConflicts, Extent,
                    (call, input) => WritesOnly(call, input, current), ReadsOnly, WritesAndNothingElse, current.ReachThrough,
                    (call, input) => TakesLowHalf(current, call, input), current.ScalarSlotConflicts) <= 0)
                break;
            Dictionary<int, int> after = InPlaceBoxes(fn);
            ParkedAddresses.Canonicalize(fn);
            lifted.Frame = StackPromotion.Run(fn, (call, input) => EscapeExtent(call, input, fn, after, current), StackArguments(lifted.Abi, fn.Regs),
                (call, input) => TakesLowHalf(current, call, input));
            DeadCode.Run(fn);
            _normalizer.Cleanup(fn);
            // A loop variable that was kept in the memory just separated is a merged value only now.
            if (!NoLoopValuesAgain && LoopValues.Run(fn, ArgumentBits)) _normalizer.Cleanup(fn);
            (builder, result) = BuildRounds(lifted);
        }
        // What the merged addresses could not be written as in C#: build without them.
        FieldOwners.Run(result, _program.Model);
        ConstantTyping.Run(result, _program);
        AddressMerges.Run(result);
        if (builder.MergedAddressVariables.Count != 0 && !NoMergedFallback && StillReferences(result, builder.MergedAddressVariables))
        {
            (builder, result) = BuildRounds(lifted, mergedAddresses: false);
            FieldOwners.Run(result, _program.Model);
            ConstantTyping.Run(result, _program);
            AddressMerges.Run(result);
        }
        // A bool's stack slot that still holds another number in the last build: read through the bool, that number
        // would come out as 0 or 1.
        if (builder.BoolSlotConflicts.Count != 0 && result.Problems.Count < 64)
            result.Problems.Add("a number kept in the stack slot of a bool");
        // A call taken to reach no more than one object that turns out to take more - or that is still not
        // known, so that nothing says what it takes: the lifetimes were told apart on a footing that does not hold.
        if (assumed.Count != 0 && !AssumedReachHolds(assumed, fn, builder) && result.Problems.Count < 64)
            result.Problems.Add("a stack object handed to a call may be larger than it was taken to be");
        FusionWeaving.Run(result);
        FinallyFolding.Run(result, _program);
        WrapperFolding.Retype(result, _program);
        StructFolding.Run(result, _program, this);
        StructConstruction.Run(result);
        ConstructorFolding.Run(result, _program, this);
        DelegateFolding.Run(result, _program);
        // A constructor that hands a lambda to its base class reads as one run of statements only now, and
        // so does the place it was pasted into.
        if (LambdaCacheFolding.Run(result)) ConstructorFolding.Run(result, _program, this, again: true);
        DeadStores.Run(result);
        EnumeratorLoops.Run(result, _program);
        if (LateMoves.Run(result)) StructConstruction.Run(result);
        SwitchRanges.Run(result);
        return result;
    }

    private static readonly bool NoMergedFallback = Environment.GetEnvironmentVariable("REWIND_NO_MERGED_FALLBACK") != null;
    private static readonly bool AssumedTrace = Environment.GetEnvironmentVariable("REWIND_ASSUMED_TRACE") != null;

    /// <summary>A reference variable made of a merged address that is still one, and given a place more than once.</summary>
    private static bool StillReferences(HMethod method, HashSet<HVar> made)
    {
        var assigned = new Dictionary<HVar, int>();
        foreach (HBlock block in method.Blocks)
            foreach (HStmt s in block.Statements)
                if (s is HAssign { Target: HLocal { Variable: var v } } && made.Contains(v) && v.Type is ByRefSig)
                    assigned[v] = assigned.GetValueOrDefault(v) + 1;
        return assigned.Values.Any(n => n > 1);
    }

    /// <summary>Every call taken to reach a known stack object reaches no more than that, by the method it was found to call.</summary>
    private bool AssumedReachHolds(List<(Node Call, int Input, int Reach)> assumed, Function fn, HirBuilder built)
    {
        Dictionary<int, int> boxes = InPlaceBoxes(fn);
        foreach (var (call, input, reach) in assumed)
        {
            if (call.Dead) continue;
            if (!Chosen(built, call, input, out _, out _, out AbiParam? taken))
            {
                if (AssumedTrace) Console.Error.WriteLine($"[assumed] not known: {Function.Describe(call)}");
                return false;
            }
            if (taken == null) continue; // the method takes nothing there
            int real = EscapeExtent(call, input, fn, boxes, built);
            if (real == StackPromotion.NotTaken) continue;
            if (real <= 0 || real > reach)
            {
                if (AssumedTrace) Console.Error.WriteLine($"[assumed] reaches {real}, taken as {reach}: {Function.Describe(call)}");
                return false;
            }
        }
        return true;
    }

    private (HirBuilder Builder, HMethod Result) BuildRounds(LiftedMethod lifted, bool mergedAddresses = true)
    {
        var builder = new HirBuilder(_program, lifted, null, _program.FrameHints?.Invoke(lifted.Function.Address)) { MergedAddresses = mergedAddresses };
        HMethod result = builder.Build();
        // Types of merged values and of stack objects are discovered while building; when any was, build
        // again knowing them.
        for (int round = 0; round < 4 && (builder.PhiTypesRefined || builder.FrameTypesRefined || builder.DispatchRefined); round++)
        {
            builder = new HirBuilder(_program, lifted, builder.PhiTypes, builder.RefinedFrameTypes, builder.DispatchPhis) { MergedAddresses = mergedAddresses };
            result = builder.Build();
        }
        // Each build may learn types the next one starts from. Still learning after the last one means this
        // result was translated with types that have since changed: it cannot be trusted as it is.
        if (builder.FrameTypesRefined && result.Problems.Count < 64) result.Problems.Add("types of stack objects did not settle");
        return (builder, result);
    }

    /// <summary>
    /// A return captures rax and xmm0; keep only what this method's return type actually uses. A value narrower
    /// than the register is cut to its size, which also discards whatever the upper register bits held.
    /// </summary>
    private static void TrimReturns(Function fn, MethodAbi abi)
    {
        var builder = new IrBuilder(fn) { InsertBeforeTerminator = true };
        foreach (Block b in fn.Blocks)
        {
            Node? ret = b.Terminator;
            if (ret?.Op == Op.Return && ret.In.Length == 10)
            {
                TrimArm64Return(ret, abi, builder, b);
                continue;
            }
            if (ret?.Op != Op.Return || ret.In.Length != 3) continue;
            switch (abi.Return)
            {
                case ReturnKind.Void:
                    ret.In = [];
                    break;
                case ReturnKind.Float:
                    ret.In = [ret.In[1]];
                    break;
                case ReturnKind.Double:
                    ret.In = [ret.In[1], ret.In[2]];
                    break;
                default:
                {
                    Node value = ret.In[0];
                    if (abi.ReturnSize is 1 or 2 or 4)
                    {
                        builder.Current = b;
                        builder.CurrentAddr = ret.Addr;
                        value = builder.Trunc(value, VTExtensions.IntOfBytes(abi.ReturnSize));
                    }
                    ret.In = [value];
                    break;
                }
            }
        }
    }

    /// <summary>
    /// An AArch64 return captures x0, x1 and lanes 0-1 of v0-v3 (in that order: x0, v0.0, v0.1, x1, v1.0, v1.1,
    /// v2.0, v2.1, v3.0, v3.1); keep what the return type uses, in byte order.
    /// </summary>
    private static void TrimArm64Return(Node ret, MethodAbi abi, IrBuilder builder, Block b)
    {
        Node[] all = ret.In;
        switch (abi.Return)
        {
            case ReturnKind.Void or ReturnKind.Buffer:
                ret.In = [];
                return;
            case ReturnKind.Float:
                ret.In = [all[1]];
                return;
            case ReturnKind.Double:
                ret.In = [all[1], all[2]];
                return;
            case ReturnKind.StructInRegisterPair:
                ret.In = [all[0], all[3]];
                return;
            case ReturnKind.FloatAggregate:
            {
                int[] lane0 = [1, 4, 6, 8], lane1 = [2, 5, 7, 9];
                var kept = new List<Node>();
                for (int k = 0; k < Math.Min(4, abi.ReturnCount); k++)
                {
                    kept.Add(all[lane0[k]]);
                    if (abi.ReturnIsDouble) kept.Add(all[lane1[k]]);
                }
                ret.In = kept.ToArray();
                return;
            }
            default:
            {
                Node value = all[0];
                if (abi.ReturnSize is 1 or 2 or 4)
                {
                    builder.Current = b;
                    builder.CurrentAddr = ret.Addr;
                    value = builder.Trunc(value, VTExtensions.IntOfBytes(abi.ReturnSize));
                }
                ret.In = [value];
                return;
            }
        }
    }

    /// <summary>
    /// How many low bits of <paramref name="value"/> a call looks at, given the parameters it is passed as:
    /// a bool or byte parameter is read as 8 bits no matter what else the register holds.
    /// </summary>
    private int ArgumentBits(Node call, Node value)
    {
        if (call.Aux is not CallInfo info || info.Indirect || info.Intrinsic != null) return 64;
        CallTarget target = _program.Resolve(info.Target);
        if (target.Helper != null || !target.IsManaged) return 64;
        int bits = 0;
        for (int i = 0; i < call.In.Length && i < info.Slots.Count; i++)
        {
            if (!ReferenceEquals(call.In[i], value)) continue;
            ArgSlot slot = info.Slots[i];
            int position = _program.Abi.Regs.IntPositionOfSlot(slot);
            if (position < 0) return 64;
            void Consider(MethodAbi abi)
            {
                if (!abi.Known)
                {
                    bits = 64;
                    return;
                }
                foreach (AbiParam p in abi.Params)
                {
                    if (p.Position != position) continue;
                    bool small = p.Role == ParamRole.Argument && p.Pass == PassKind.Integer && p.Size is 1 or 2 or 4 && p.Type is not ByRefSig;
                    bits = Math.Max(bits, small ? p.Size * 8 : 64);
                    return;
                }
                bits = 64; // not a parameter of this candidate at all
            }
            foreach (MethodDef m in target.Methods) Consider(_program.Abi.For(m, [], []));
            foreach (MethodInst inst in target.Insts) Consider(_program.Abi.For(inst));
        }
        return bits == 0 ? 64 : bits;
    }

    /// <summary>
    /// How many bytes a callee may touch through a stack address passed as an argument: the size of the struct
    /// for by-reference struct parameters and return buffers, unknown otherwise.
    /// </summary>
    /// <summary>
    /// True when the callee only writes the memory a pointer argument points to before anything reads it: the
    /// return buffer, or an "out" parameter (C# requires the callee to assign it first).
    /// </summary>
    private bool WritesOnly(Node call, int inputIndex)
    {
        if (BlockCopies.Access(call, inputIndex, _program.Helpers, out _, out bool blockReads, out _)) return !blockReads;
        if (call.Aux is not CallInfo info || info.Indirect || info.Intrinsic != null || inputIndex >= info.Slots.Count) return false;
        ArgSlot slot = info.Slots[inputIndex];
        int position = _program.Abi.Regs.IntPositionOfSlot(slot);
        if (position < 0) return false;
        CallTarget target = _program.Resolve(info.Target);
        if (target.Helper != null || !target.IsManaged) return false;
        bool all = true, any = false;
        void Consider(MethodDef method, MethodAbi abi)
        {
            foreach (AbiParam p in abi.Params)
            {
                if (p.Position != position) continue;
                any = true;
                bool writes = p.Role == ParamRole.ReturnBuffer ||
                              (p.Role == ParamRole.Argument && p.ArgumentIndex >= 0 && p.ArgumentIndex < method.Parameters.Length && method.Parameters[p.ArgumentIndex].IsOut);
                all &= writes;
            }
        }
        foreach (MethodDef m in target.Methods) Consider(m, _program.Abi.For(m, [], []));
        foreach (MethodInst inst in target.Insts) Consider(inst.Method, _program.Abi.For(inst));
        return any && all;
    }

    /// <summary>True for a fill, or a copy seen from its destination: without that memory being read, the call does nothing.</summary>
    private bool WritesAndNothingElse(Node call, int inputIndex) =>
        BlockCopies.Access(call, inputIndex, _program.Helpers, out _, out bool blockReads, out bool blockWrites) && blockWrites && !blockReads;

    /// <summary>True when the callee only reads the memory a pointer argument points to (the source of a copy, a value being boxed).</summary>
    private bool ReadsOnly(Node call, int inputIndex)
    {
        if (BlockCopies.Access(call, inputIndex, _program.Helpers, out _, out _, out bool blockWrites)) return !blockWrites;
        if (call.Aux is not CallInfo { Indirect: false, Intrinsic: null } info || inputIndex >= info.Slots.Count ||
            info.Slots[inputIndex] is not { Kind: ArgSlotKind.IntReg } slot || _program.Resolve(info.Target).Helper is not { } helper)
            return false;
        return HelperReads(call, info, helper.Kind, slot.Index) > 0;
    }

    /// <summary>
    /// How many bytes a runtime helper reads through the stack address in argument <paramref name="position"/>, and
    /// does nothing else with: Box(klass, &amp;value) one value of the class, a C++ throw the wrapper of the exception
    /// (one pointer). -1 when that is not known (the unbox helpers write a value whose size is not the class's).
    /// </summary>
    private int HelperReads(Node call, CallInfo info, HelperKind kind, int position)
    {
        if (NoHelperExtents) return -1;
        if (kind == HelperKind.CxxThrow && position == 0) return _program.Model.Image.PointerSize;
        if (kind != HelperKind.Box || position != 1) return -1;
        for (int i = 0; i < info.Slots.Count && i < call.In.Length; i++)
        {
            if (info.Slots[i] is not { Kind: ArgSlotKind.IntReg, Index: 0 }) continue;
            if (SlotClass(call.In[i]) is not { IsValueType: true } type || type.ContainsGenericParameter) return -1;
            var (size, _, known) = _program.Layouts.SizeOf(type);
            return known && size > 0 ? size : -1;
        }
        return -1;
    }

    private static readonly bool NoHelperExtents = Environment.GetEnvironmentVariable("REWIND_NO_HELPER_EXTENTS") != null;

    /// <summary>The class a metadata slot value names, when it names one.</summary>
    private TypeSig? SlotClass(Node value)
    {
        if (value.Op != Op.SlotValue) return null;
        ulong slot = (ulong)value.Imm;
        return _program.Defaults.Slots.TryGetValue(slot, out TypeDef? def) ? def.Sig
            : _program.Model.ResolveUsageSlot(slot) is { Kind: UsageKind.TypeInfo, Type: { } usage } ? usage : null;
    }

    /// <summary>
    /// Values boxed in place: generated code writes an object header (the class, then a mark) on the stack in
    /// front of a copy of the value and passes that address where an object is expected. Stack offset of each
    /// such header -> the size of the whole (header and the largest value given that header there).
    /// </summary>
    private Dictionary<int, int> InPlaceBoxes(Function fn)
    {
        var boxes = new Dictionary<int, int>();
        if (!fn.Params.TryGetValue(fn.Regs.StackPointer, out Node? sp0)) return boxes;
        int header = 2 * _program.Model.Image.PointerSize;
        foreach (Block b in fn.Blocks)
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op != Op.Store || n.In[1].Op != Op.SlotValue || StackOffset(sp0, n.In[0]) is not int at) continue;
                TypeSig? type = SlotClass(n.In[1]);
                if (type is not { IsValueType: true } || type.ContainsGenericParameter) continue;
                var (size, _, known) = _program.Layouts.SizeOf(type);
                if (!known) continue;
                boxes[at] = Math.Max(boxes.GetValueOrDefault(at), header + Math.Max(1, size));
            }
        return boxes;
    }

    /// <summary>
    /// A call is lifted with whatever the argument registers and the first stack slots held: the callee's
    /// signature is not known at that point. What no method the target can be takes as a parameter is not an
    /// argument but a leftover of earlier code - and as long as the call "uses" it, that leftover (a class
    /// pointer, a stack address, a merge of unrelated values) has to be explained for nothing.
    /// </summary>
    private bool TrimCallArguments(Function fn)
    {
        bool changed = false;
        foreach (Block b in fn.Blocks)
            foreach (Node call in b.Nodes)
            {
                if (call.Dead || call.Op is not (Op.Call or Op.TailCall) || call.Aux is not CallInfo { Indirect: false, Intrinsic: null } info) continue;
                if (info.Slots.Count != call.In.Length || call.In.Length == 0) continue;
                CallTarget target = _program.Resolve(info.Target);
                if (!target.IsManaged || target.Helper != null || target.Forwarded) continue;
                var integer = new HashSet<int>();
                var floating = new HashSet<int>();
                var exact = new HashSet<ArgSlot>();
                bool unknown = false;
                void Consider(MethodAbi abi)
                {
                    if (!abi.Known)
                    {
                        unknown = true;
                        return;
                    }
                    // (Where integer and floating-point registers are counted apart, the slots each parameter takes.)
                    if (!fn.Regs.SharedPositions && ProgramAnalysis.SlotsFrom(abi, fn.Regs).Slots is { } taken) exact.UnionWith(taken);
                    foreach (AbiParam p in abi.Params) (p.Pass == PassKind.Float ? floating : integer).Add(p.Position);
                }
                foreach (MethodDef m in target.Methods) Consider(_program.Abi.For(m, [], []));
                foreach (MethodInst inst in target.Insts) Consider(_program.Abi.For(inst));
                if (unknown) continue;

                var inputs = new List<Node>(call.In.Length);
                var slots = new List<ArgSlot>(call.In.Length);
                for (int i = 0; i < call.In.Length; i++)
                {
                    ArgSlot slot = info.Slots[i];
                    bool taken = !fn.Regs.SharedPositions ? slot.Kind == ArgSlotKind.Target || exact.Contains(slot) : slot.Kind switch
                    {
                        ArgSlotKind.IntReg => integer.Contains(slot.Index),
                        ArgSlotKind.Stack => integer.Contains(slot.Index + 4) || floating.Contains(slot.Index + 4),
                        ArgSlotKind.FloatReg => floating.Contains(slot.Index / 4),
                        _ => true,
                    };
                    if (!taken) continue;
                    inputs.Add(call.In[i]);
                    slots.Add(slot);
                }
                if (inputs.Count == call.In.Length) continue;
                call.In = inputs.ToArray();
                info.Slots = slots;
                changed = true;
            }
        return changed;
    }

    /// <summary>
    /// The entry values the calling convention gives no meaning: the scratch registers, and the argument
    /// registers this method has no parameter for.
    /// </summary>
    private static readonly bool NoSavedLeftovers = Environment.GetEnvironmentVariable("REWIND_NO_SAVED_LEFTOVERS") != null;

    private static Func<Node, bool> Leftovers(Function fn, MethodAbi abi)
    {
        var leftovers = new HashSet<Node>();
        void Add(int variable)
        {
            if (fn.Params.TryGetValue(variable, out Node? entry)) leftovers.Add(entry);
        }
        RegisterModel regs = fn.Regs;
        if (regs.SharedPositions)
        {
            Add(0);   // rax
            Add(10);  // r10
            Add(11);  // r11
        }
        else
        {
            for (int r = 9; r <= 18; r++) Add(r); // x9-x18: scratch
            Add(30);                              // the link register: the return address, never a value
        }
        // What the caller left in a register this method must preserve means nothing to the method itself: it
        // is only saved and put back. Writing one byte of such a register ("mov bl, [rcx+18h]") keeps the caller's
        // other seven, which no one reads.
        if (!NoSavedLeftovers)
            foreach (int saved in regs.CalleeSaved)
                if (saved != regs.StackPointer)
                    Add(saved);
        if (abi.Known)
        {
            var taken = new HashSet<int>();
            foreach (AbiParam p in abi.Params)
                if (p.Pass != PassKind.Float && regs.IntRegisterOf(p.Position) is int r and >= 0) taken.Add(r);
            for (int position = 0; position < regs.IntArgs.Length; position++)
                if (!taken.Contains(position)) Add(regs.IntArgs[position]);
        }
        return leftovers.Contains;
    }

    private bool IsClassOrMethodSlot(ulong slot) =>
        _program.Defaults.Slots.ContainsKey(slot) ||
        _program.Model.ResolveUsageSlot(slot) is { Kind: UsageKind.TypeInfo or UsageKind.MethodDef or UsageKind.MethodRef };

    private static int? StackOffset(Node sp0, Node n)
    {
        if (ReferenceEquals(n, sp0)) return 0;
        if (n.Op == Op.Add && ReferenceEquals(n.In[0], sp0) && n.In[1].IsConst && IrBuilder.SImm(n.In[1]) is > -0x4000000 and < 0x4000000)
            return (int)IrBuilder.SImm(n.In[1]);
        return null;
    }

    private int EscapeExtent(Node call, int inputIndex, Function fn, Dictionary<int, int> boxes)
    {
        int extent = EscapeExtent(call, inputIndex, out bool asObject);
        if (extent > 0 || !asObject || boxes.Count == 0 || !fn.Params.TryGetValue(fn.Regs.StackPointer, out Node? sp0)) return extent;
        // A stack address where an object is expected: the value boxed in place there.
        return StackOffset(sp0, call.In[inputIndex]) is int at && boxes.TryGetValue(at, out int box) ? box : -1;
    }

    private int EscapeExtent(Node call, int inputIndex) => EscapeExtent(call, inputIndex, out _);

    /// <summary>
    /// The parameter a call input is, by the method the call was found to mean when the function was built:
    /// exact where the call's target alone names several methods sharing one body. False when the call was not
    /// resolved that way; a null parameter means the method takes nothing in that position.
    /// </summary>
    private bool Chosen(HirBuilder built, Node call, int inputIndex, out MethodDef method, out MethodAbi abi, out AbiParam? parameter)
    {
        method = null!;
        abi = null!;
        parameter = null;
        if (!built.ChosenCalls.TryGetValue(call, out var chosen) || call.Aux is not CallInfo info || inputIndex >= info.Slots.Count) return false;
        ArgSlot slot = info.Slots[inputIndex];
        int position = _program.Abi.Regs.IntPositionOfSlot(slot);
        if (position < 0) return false;
        method = chosen.Method;
        abi = chosen.Abi;
        foreach (AbiParam p in abi.Params)
            if (p.Position + chosen.Shift == position)
            {
                parameter = p;
                break;
            }
        return true;
    }

    private int Position(ArgSlot slot) => _program.Abi.Regs.IntPositionOfSlot(slot);

    /// <summary>The call takes a value of four bytes or fewer in that input (an int, a float, a small struct): the bottom half of the slot.</summary>
    private bool TakesLowHalf(HirBuilder built, Node call, int inputIndex)
    {
        if (!Chosen(built, call, inputIndex, out _, out _, out AbiParam? p) || p == null) return false;
        if (p.Role != ParamRole.Argument || p.Pass == PassKind.Indirect || p.Type is null or ByRefSig or PointerSig) return false;
        var (size, _, known) = _program.Layouts.SizeOf(p.Type);
        return known && size is >= 1 and <= 4 && p.Type.IsValueType;
    }

    private long _delegateCode = -2, _delegateMethod = -2;

    /// <summary>
    /// The argument position of the method a call hands over last, where the call has the shape of a delegate's
    /// invocation - "d.invoke_impl(d.method_code, arguments.., d.method)": the code is read from an object and
    /// the method from the same object. That holds whatever is known of the object. -1 when the call is not that.
    /// </summary>
    private int DelegateShapeLast(Node call, CallInfo info)
    {
        if (_delegateCode == -2)
        {
            TypeDef? type = _program.Model.FindType("System.Delegate");
            _delegateCode = type?.Fields.FirstOrDefault(f => !f.IsStatic && f.Name == "invoke_impl")?.Offset ?? -1;
            _delegateMethod = type?.Fields.FirstOrDefault(f => !f.IsStatic && f.Name == "method")?.Offset ?? -1;
        }
        if (_delegateCode <= 0 || _delegateMethod <= 0) return -1;
        static Node? ReadOf(Node n, long offset) =>
            n.Op == Op.Load && n.In[0] is { Op: Op.Add } address && address.In[1].IsConst && IrBuilder.SImm(address.In[1]) == offset ? address.In[0] : null;
        Node? from = null;
        for (int i = 0; i < info.Slots.Count && i < call.In.Length; i++)
            if (info.Slots[i].Kind == ArgSlotKind.Target) from = ReadOf(call.In[i], _delegateCode);
        if (from == null) return -1;
        int last = -1;
        for (int i = 0; i < info.Slots.Count && i < call.In.Length; i++)
            if (Position(info.Slots[i]) is >= 0 and var position && ReferenceEquals(ReadOf(call.In[i], _delegateMethod), from))
                last = Math.Max(last, position);
        return last;
    }

    private int EscapeExtent(Node call, int inputIndex, Function fn, Dictionary<int, int> boxes, HirBuilder built)
    {
        if (!Chosen(built, call, inputIndex, out _, out MethodAbi abi, out AbiParam? p))
        {
            // A call that was not resolved but has the shape of a delegate's invocation takes nothing after
            // the method it hands over last.
            if (!NoUntakenInputs && call.Aux is CallInfo { Indirect: true } unresolved && inputIndex < unresolved.Slots.Count &&
                !built.ChosenCalls.ContainsKey(call) && DelegateShapeLast(call, unresolved) is >= 0 and var lastTaken &&
                Position(unresolved.Slots[inputIndex]) > lastTaken)
                return StackPromotion.NotTaken;
            return EscapeExtent(call, inputIndex, fn, boxes);
        }
        if (p == null)
        {
            // Past the last thing the method takes: what the register or the stack slot held before the call
            // (the address handed to an earlier one, say), no argument of this one. The call reaches nothing
            // through it.
            if (!NoUntakenInputs && built.ChosenCalls.TryGetValue(call, out var chosen) && call.Aux is CallInfo info && inputIndex < info.Slots.Count)
            {
                ArgSlot slot = info.Slots[inputIndex];
                int position = _program.Abi.Regs.IntPositionOfSlot(slot);
                int last = -1;
                foreach (AbiParam taken in chosen.Abi.Params)
                    if (chosen.Shift == 0 || taken.Role != ParamRole.MethodInfo)
                        last = Math.Max(last, taken.Position + chosen.Shift);
                if (last >= 0 && position > last) return StackPromotion.NotTaken;
            }
            return EscapeExtent(call, inputIndex, fn, boxes);
        }
        // (The helper that calls a method by its slot finds the method itself: its caller hands over none.)
        if (p.Role == ParamRole.MethodInfo && !NoUntakenInputs && built.ChosenCalls.TryGetValue(call, out var through) && through.Shift > 0)
            return StackPromotion.NotTaken;
        int size = -1;
        if (p.Role == ParamRole.ReturnBuffer) size = abi.ReturnSize;
        else if (p.Pass == PassKind.Indirect) size = p.Size;
        else if (p.Type is ByRefSig byRef) size = _program.Layouts.SizeOf(byRef.ElementType).Size;
        else if (p.Role == ParamRole.This && p.Type?.Definition is { IsValueType: true }) size = _program.Layouts.SizeOf(p.Type).Size;
        if (size > 0) return size;
        bool asObject = p.Role is ParamRole.This or ParamRole.Argument && p.Pass == PassKind.Integer &&
                        p.Type is { IsValueType: false } and not ByRefSig and not PointerSig && !p.Type.ContainsGenericParameter;
        if (asObject && fn.Params.TryGetValue(fn.Regs.StackPointer, out Node? sp0) && StackOffset(sp0, call.In[inputIndex]) is int at &&
            boxes.TryGetValue(at, out int box))
            return box;
        return -1;
    }

    private bool WritesOnly(Node call, int inputIndex, HirBuilder built)
    {
        if (!Chosen(built, call, inputIndex, out MethodDef method, out _, out AbiParam? p) || p == null) return WritesOnly(call, inputIndex);
        return p.Role == ParamRole.ReturnBuffer ||
               (p.Role == ParamRole.Argument && p.ArgumentIndex >= 0 && p.ArgumentIndex < method.Parameters.Length && method.Parameters[p.ArgumentIndex].IsOut);
    }

    /// <param name="asObject">Set when every method the call may reach takes an object reference in that position.</param>
    private int EscapeExtent(Node call, int inputIndex, out bool asObject)
    {
        asObject = false;
        if (BlockCopies.Access(call, inputIndex, _program.Helpers, out int blockBytes, out _, out _)) return blockBytes;
        if (call.Aux is not CallInfo info || info.Indirect || info.Intrinsic != null) return -1;
        if (inputIndex >= info.Slots.Count) return -1;
        ArgSlot slot = info.Slots[inputIndex];
        int position = _program.Abi.Regs.IntPositionOfSlot(slot);
        if (position < 0) return -1;

        CallTarget target = _program.Resolve(info.Target);
        if (target.Helper != null)
        {
            // modf(x, &whole) writes the whole part there, one number as wide as x, and nothing else. (Without a
            // bound, the address of a pasted Math.Round's local reached the whole frame, and nothing on the stack
            // became a value: the registers a catch handler saves stayed stores, of what it cannot know.)
            if (!NoHelperExtents && target.Helper.Kind == HelperKind.Modf && position == 1) return target.Helper.IsDouble ? 8 : 4;
            return HelperReads(call, info, target.Helper.Kind, position);
        }

        int extent = -1, objects = 0, others = 0;
        void Consider(MethodAbi abi)
        {
            foreach (AbiParam p in abi.Params)
            {
                if (p.Position != position) continue;
                int size = -1;
                if (p.Role == ParamRole.ReturnBuffer) size = abi.ReturnSize;
                else if (p.Pass == PassKind.Indirect) size = p.Size;
                else if (p.Type is ByRefSig byRef) size = _program.Layouts.SizeOf(byRef.ElementType).Size;
                else if (p.Role == ParamRole.This && p.Type?.Definition is { IsValueType: true }) size = _program.Layouts.SizeOf(p.Type).Size;
                if (size > 0)
                {
                    extent = Math.Max(extent, size);
                    others++;
                }
                else
                {
                    extent = int.MinValue; // some candidate gives no bound
                    if (p.Role is ParamRole.This or ParamRole.Argument && p.Pass == PassKind.Integer &&
                        p.Type is { IsValueType: false } and not ByRefSig and not PointerSig && !p.Type.ContainsGenericParameter)
                        objects++;
                    else others++;
                }
            }
        }
        foreach (MethodDef m in target.Methods) Consider(_program.Abi.For(m, [], []));
        foreach (MethodInst inst in target.Insts) Consider(_program.Abi.For(inst));
        asObject = objects > 0 && others == 0;
        return extent > 0 ? extent : -1;
    }
}
