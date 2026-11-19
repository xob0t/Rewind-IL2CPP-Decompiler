using System.Globalization;
using System.Text;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Hir;

/// <summary>A local variable of the recovered method (also used for temporaries and merged values).</summary>
public sealed class HVar
{
    public int Index;
    public TypeSig Type = null!;
    public string Name = "";
    /// <summary>True when the variable's address is taken (struct locals, out arguments).</summary>
    public bool AddressTaken;
    public override string ToString() => Name;
}

public enum HUnaryOp { Neg, Not, LogicalNot }

public enum HBinaryOp
{
    Add, Sub, Mul, Div, DivUn, Rem, RemUn, And, Or, Xor, Shl, Shr, ShrUn,
    AddOvf, AddOvfUn, SubOvf, SubOvfUn, MulOvf, MulOvfUn,
}

public enum HCompareOp { Eq, Ne, Lt, Le, Gt, Ge, LtUn, LeUn, GtUn, GeUn }

/// <summary>Numeric conversions, named after the IL instruction they become.</summary>
public enum HConvKind { I1, U1, I2, U2, I4, U4, I8, U8, R4, R8, RUn, I, U, OvfI1, OvfU1, OvfI2, OvfU2, OvfI4, OvfU4, OvfI8, OvfU8 }

// ---- expressions ---------------------------------------------------------------------------------------------

public abstract class HExpr
{
    /// <summary>Static type of the value, when known.</summary>
    public TypeSig? Type;
}

public sealed class HConst : HExpr
{
    public object? Value;   // int, long, float, double, string, bool or null
    public HConst(object? value, TypeSig? type) { Value = value; Type = type; }
}

public sealed class HLocal(HVar variable) : HExpr
{
    public HVar Variable = variable;
}

/// <summary>A method argument; index -1 is "this".</summary>
public sealed class HArg(int index) : HExpr
{
    public int Index = index;
}

/// <summary>An instance field (Object set) or a static field (Object null).</summary>
public sealed class HField : HExpr
{
    public HExpr? Object;
    public FieldDef Field = null!;
    /// <summary>The instantiated declaring type when the field belongs to a generic instance.</summary>
    public TypeSig? DeclaringType;
}

public sealed class HElement : HExpr
{
    public HExpr Array = null!;
    public HExpr Index = null!;
}

public sealed class HArrayLength(HExpr array) : HExpr
{
    public HExpr Array = array;
}

/// <summary>Managed pointer to a local, field or array element.</summary>
public sealed class HAddressOf(HExpr target) : HExpr
{
    public HExpr Target = target;
}

/// <summary>Reads through a managed or native pointer.</summary>
public sealed class HDeref(HExpr pointer) : HExpr
{
    public HExpr Pointer = pointer;
}

public sealed class HUnary(HUnaryOp op, HExpr operand) : HExpr
{
    public HUnaryOp Op = op;
    public HExpr Operand = operand;
}

public sealed class HBinary(HBinaryOp op, HExpr left, HExpr right) : HExpr
{
    public HBinaryOp Op = op;
    public HExpr Left = left, Right = right;
}

public sealed class HCompare(HCompareOp op, HExpr left, HExpr right) : HExpr
{
    public HCompareOp Op = op;
    public HExpr Left = left, Right = right;
}

public sealed class HConv(HConvKind kind, HExpr operand) : HExpr
{
    public HConvKind Kind = kind;
    public HExpr Operand = operand;
}

public sealed class HCall : HExpr
{
    public MethodDef Method = null!;
    public TypeSig? DeclaringType;         // instantiated declaring type, for methods of generic instances
    public TypeSig[] MethodArguments = []; // generic method arguments
    public HExpr? This;
    public HExpr[] Arguments = [];
    public bool Virtual;
    /// <summary>
    /// Set for an interface method called on a struct where it is ("constrained."): the struct's type, by which
    /// the implementation is found. Method is then the interface's method and This the struct's location.
    /// </summary>
    public TypeSig? Constrained;
    /// <summary>Other methods that share the same machine code and also fit this call site.</summary>
    public List<MethodDef> Alternatives = [];
}

public sealed class HNewObject : HExpr
{
    public MethodDef Constructor = null!;
    public TypeSig? DeclaringType;
    public HExpr[] Arguments = [];
}

public sealed class HNewArray(TypeSig elementType, HExpr length) : HExpr
{
    public TypeSig ElementType = elementType;
    public HExpr Length = length;
}

public enum HTypeOp
{
    Box, UnboxAny, IsInst, CastClass, Default, SizeOf, TypeToken,
    /// <summary>A new, zeroed object of the type on which no constructor has run.</summary>
    Allocate,
    /// <summary>"stackalloc T[n]": n elements on the stack (the operand), zeroed; the value is a T*.</summary>
    StackAlloc,
}

/// <summary>Operations parameterized by a type: box, unbox.any, isinst, castclass, default(T), sizeof, typeof.</summary>
public sealed class HTypeExpr(HTypeOp op, TypeSig target, HExpr? operand) : HExpr
{
    public HTypeOp Op = op;
    public TypeSig Target = target;
    public HExpr? Operand = operand;
}

/// <summary>The address of a method's code, as "ldftn" produces it (the second argument of a delegate constructor).</summary>
public sealed class HMethodPointer : HExpr
{
    public MethodDef Method = null!;
    public TypeSig? DeclaringType;
    public TypeSig[] MethodArguments = [];
    /// <summary>
    /// Set for "ldvirtftn": the code is what this object's class fills the virtual method's slot with (a
    /// delegate made from a virtual method). Only ever an argument of the method ("this" included).
    /// </summary>
    public HArg? VirtualOn;
}

/// <summary>The runtime handle of a method or field, as "ldtoken" produces it.</summary>
public sealed class HMemberToken : HExpr
{
    public MethodDef? Method;
    public FieldDef? Field;
    public TypeSig? DeclaringType;
    public TypeSig[] MethodArguments = [];
}

/// <summary>
/// "Cache ?? (Cache = new D(...))": a delegate that is made once and kept in a static field, as the compiler
/// writes a lambda that captures nothing.
/// </summary>
public sealed class HCachedDelegate(HField cache, HNewObject creation) : HExpr
{
    public HField Cache = cache;
    public HNewObject Creation = creation;
}

/// <summary>cond ? a : b.</summary>
public sealed class HSelect(HExpr condition, HExpr whenTrue, HExpr whenFalse) : HExpr
{
    public HExpr Condition = condition, WhenTrue = whenTrue, WhenFalse = whenFalse;
}

/// <summary>A native operation with no managed counterpart found; kept visible rather than dropped.</summary>
public sealed class HOpaque(string text, params HExpr[] operands) : HExpr
{
    public string Text = text;
    public HExpr[] Operands = operands;
    /// <summary>The problem reported where this marker was made, if any (see HMethod.SiteProblems).</summary>
    public string? Problem;
}

// ---- statements ----------------------------------------------------------------------------------------------

public abstract class HStmt
{
    public ulong Address;
}

public sealed class HAssign(HExpr target, HExpr value) : HStmt
{
    public HExpr Target = target, Value = value;
}

public sealed class HEval(HExpr expression) : HStmt
{
    public HExpr Expression = expression;
}

public sealed class HReturn(HExpr? value) : HStmt
{
    public HExpr? Value = value;
}

public sealed class HThrow(HExpr? exception) : HStmt
{
    /// <summary>Null means rethrow.</summary>
    public HExpr? Exception = exception;
}

public sealed class HJump(HBlock target) : HStmt
{
    public HBlock Target = target;
}

public sealed class HBranch(HExpr condition, HBlock whenTrue, HBlock whenFalse) : HStmt
{
    public HExpr Condition = condition;
    public HBlock WhenTrue = whenTrue, WhenFalse = whenFalse;
}

public sealed class HSwitch(HExpr value, HBlock[] targets, HBlock fallback) : HStmt
{
    public HExpr Value = value;
    public HBlock[] Targets = targets;
    public HBlock Default = fallback;
}

/// <summary>The end of a finally handler: control goes on to wherever the protected code was being left for.</summary>
public sealed class HEndFinally : HStmt
{
}

public sealed class HBlock
{
    public int Id;
    public List<HStmt> Statements = [];
    /// <summary>Where the block sits among the try regions: -1 outside all, 2r in region r's protected code, 2r+1 in its handler.</summary>
    public int Scope = -1;
    public override string ToString() => "L" + Id;
}

/// <summary>
/// A try/catch. The protected code is the blocks whose scope chain reaches 2*Index, entered only at Entry; the
/// handler is the blocks whose chain reaches 2*Index+1, entered only by an exception, at HandlerEntry, with the
/// caught exception in Exception. Outer is the scope of the try statement itself.
/// </summary>
public sealed class HTryRegion
{
    public int Index;
    public int Outer = -1;
    public HBlock Entry = null!, HandlerEntry = null!;
    public HVar Exception = null!;
    /// <summary>
    /// True for try/finally: the handler runs whenever the protected code is left, by an exception or not; its
    /// blocks end with HEndFinally, and Exception is not used.
    /// </summary>
    public bool Finally;
}

public sealed class HMethod
{
    public MethodDef Method = null!;
    public List<HVar> Locals = [];
    public List<HBlock> Blocks = [];
    /// <summary>Things the recovery could not express faithfully; an empty list means a clean translation.</summary>
    public List<string> Problems = [];
    /// <summary>
    /// Problems that are each reported together with the marker (HOpaque.Problem) standing in for what was not
    /// recovered. When no such marker is left in the finished method, the code that had the problem is no part
    /// of it (a copy into a merged value nothing reads, a register a call turned out not to take), and the
    /// problem goes with it.
    /// </summary>
    public HashSet<string> SiteProblems = [];
    /// <summary>Remarks that do not affect what the code does (for instance: it contains inlined code).</summary>
    public List<string> Notes = [];
    /// <summary>The methods whose statements, pasted in here, were put back as a call of the method.</summary>
    public HashSet<MethodDef>? PutBack;
    /// <summary>Try regions by index (see HBlock.Scope).</summary>
    public Dictionary<int, HTryRegion> TryRegions = [];
    /// <summary>For inspection: the types the recovery gave stack memory, by offset from the entry stack pointer.</summary>
    public Dictionary<int, TypeSig> FrameTypes = [];

    /// <summary>The scope that directly encloses <paramref name="scope"/> (-1 at the top).</summary>
    public int OuterOf(int scope) => scope >= 0 && TryRegions.TryGetValue(scope >> 1, out HTryRegion? r) ? r.Outer : -1;

    /// <summary>True when <paramref name="outer"/> is <paramref name="scope"/> or encloses it.</summary>
    public bool Encloses(int outer, int scope)
    {
        for (int s = scope, guard = 0; guard < 64; guard++, s = OuterOf(s))
        {
            if (s == outer) return true;
            if (s < 0) return false;
        }
        return false;
    }

    public HVar NewLocal(TypeSig type, string prefix = "v")
    {
        var v = new HVar { Index = Locals.Count, Type = type };
        v.Name = prefix + v.Index;
        Locals.Add(v);
        return v;
    }
}

/// <summary>Readable rendering of HIR for inspection. Not C#, but close to it.</summary>
public static class HirPrinter
{
    public static string Print(HMethod m)
    {
        var sb = new StringBuilder();
        sb.Append(m.Method.ReturnType.ShortName).Append(' ').Append(m.Method.DeclaringType.Name).Append("::").Append(m.Method.Name).Append('(');
        sb.Append(string.Join(", ", m.Method.Parameters.Select((p, i) => p.Type.ShortName + " " + ParameterName(m.Method, i)))).AppendLine(")");
        foreach (HVar v in m.Locals) sb.AppendLine($"    {v.Type.ShortName} {v.Name};");
        foreach (HTryRegion r in m.TryRegions.Values.OrderBy(r => r.Index))
            sb.AppendLine(r.Finally
                ? $"    try {r.Index}: starts at {r.Entry}, finally at {r.HandlerEntry}"
                : $"    try {r.Index}: starts at {r.Entry}, catch (Exception {r.Exception.Name}) at {r.HandlerEntry}");
        foreach (HBlock b in m.Blocks)
        {
            string part = (b.Scope & 1) == 0 ? "try" : m.TryRegions.TryGetValue(b.Scope >> 1, out HTryRegion? region) && region.Finally ? "finally" : "catch";
            sb.AppendLine(b.Scope < 0 ? $"  {b}:" : $"  {b}: ({part} {b.Scope >> 1})");
            foreach (HStmt s in b.Statements) sb.Append("    ").AppendLine(Print(s, m));
        }
        foreach (string p in m.Problems) sb.AppendLine("  ! " + p);
        return sb.ToString();
    }

    private static readonly System.Text.RegularExpressions.Regex VariableName = new(@"\b(?:m|t|s|o|e|v|local|result)\d+\b"),
        BlockName = new(@"\bL(\d+)\b");

    /// <summary>
    /// The method's statements in a form that does not depend on how its machine code was laid out: blocks in the
    /// order control reaches them from the start, blocks and variables numbered by first appearance, each
    /// variable with its type. Two bodies with the same canonical text are the same code.
    /// </summary>
    public static string Canonical(HMethod m)
    {
        if (m.Blocks.Count == 0) return "";
        var order = new List<HBlock>();
        var index = new Dictionary<HBlock, int>();
        var pending = new Stack<HBlock>();
        pending.Push(m.Blocks[0]);
        while (pending.Count > 0)
        {
            HBlock b = pending.Pop();
            if (!index.TryAdd(b, order.Count)) continue;
            order.Add(b);
            var next = new List<HBlock>();
            if (b.Statements.Count > 0)
                switch (b.Statements[^1])
                {
                    case HJump j: next.Add(j.Target); break;
                    case HBranch br: next.Add(br.WhenTrue); next.Add(br.WhenFalse); break;
                    case HSwitch sw: next.AddRange(sw.Targets); next.Add(sw.Default); break;
                }
            foreach (HTryRegion r in m.TryRegions.Values.OrderBy(r => r.Index))
                if (ReferenceEquals(r.Entry, b)) next.Add(r.HandlerEntry);
            for (int i = next.Count - 1; i >= 0; i--) pending.Push(next[i]); // first named, first visited
        }
        var byId = new Dictionary<int, HBlock>();
        foreach (HBlock b in m.Blocks) byId[b.Id] = b;
        var names = new Dictionary<string, string>();
        var types = new List<string>();
        var locals = new Dictionary<string, HVar>();
        foreach (HVar v in m.Locals) locals[v.Name] = v;
        var sb = new StringBuilder();
        foreach (HBlock b in order)
        {
            sb.Append('B').Append(index[b]).AppendLine(":");
            foreach (HStmt s in b.Statements)
            {
                string text = Print(s, m);
                text = BlockName.Replace(text, match =>
                    byId.TryGetValue(int.Parse(match.Groups[1].Value), out HBlock? target) && index.TryGetValue(target, out int at) ? "B" + at : match.Value);
                text = VariableName.Replace(text, match =>
                {
                    if (!locals.TryGetValue(match.Value, out HVar? variable)) return match.Value; // a field or parameter that merely looks like one
                    if (!names.TryGetValue(match.Value, out string? canonical))
                    {
                        names[match.Value] = canonical = "x" + names.Count;
                        types.Add(canonical + ": " + variable.Type.DisplayName);
                    }
                    return canonical;
                });
                sb.Append("  ").AppendLine(text);
            }
        }
        foreach (HTryRegion r in m.TryRegions.Values.Where(r => index.ContainsKey(r.Entry)).OrderBy(r => index[r.Entry]))
            sb.AppendLine($"try B{index[r.Entry]} {(r.Finally ? "finally" : "catch")} B{(index.TryGetValue(r.HandlerEntry, out int h) ? h : -1)}");
        foreach (string t in types) sb.AppendLine(t);
        return sb.ToString();
    }

    /// <summary>A parameter's name; compiler-generated methods can have parameters without one.</summary>
    public static string ParameterName(MethodDef method, int index)
    {
        if (index >= 0 && index < method.Parameters.Length && method.Parameters[index].Name.Length != 0) return method.Parameters[index].Name;
        return "arg" + index;
    }

    public static string Print(HStmt s, HMethod m) => s switch
    {
        HAssign a => $"{Print(a.Target, m)} = {Print(a.Value, m)};",
        HEval e => Print(e.Expression, m) + ";",
        HReturn r => r.Value == null ? "return;" : $"return {Print(r.Value, m)};",
        HThrow t => t.Exception == null ? "throw;" : $"throw {Print(t.Exception, m)};",
        HJump j => $"goto {j.Target};",
        HBranch b => $"if ({Print(b.Condition, m)}) goto {b.WhenTrue}; else goto {b.WhenFalse};",
        HSwitch sw => $"switch ({Print(sw.Value, m)}) {{ {string.Join(", ", sw.Targets.Select((t, i) => i + " => " + t))}, default => {sw.Default} }}",
        HEndFinally => "endfinally;",
        _ => s.GetType().Name,
    };

    private static string Binary(HBinaryOp op) => op switch
    {
        HBinaryOp.Add => "+", HBinaryOp.Sub => "-", HBinaryOp.Mul => "*", HBinaryOp.Div => "/", HBinaryOp.DivUn => "/u",
        HBinaryOp.Rem => "%", HBinaryOp.RemUn => "%u", HBinaryOp.And => "&", HBinaryOp.Or => "|", HBinaryOp.Xor => "^",
        HBinaryOp.Shl => "<<", HBinaryOp.Shr => ">>", HBinaryOp.ShrUn => ">>>",
        HBinaryOp.AddOvf => "+checked", HBinaryOp.AddOvfUn => "+checked.un", HBinaryOp.SubOvf => "-checked",
        HBinaryOp.SubOvfUn => "-checked.un", HBinaryOp.MulOvf => "*checked", _ => "*checked.un",
    };

    private static string Compare(HCompareOp op) => op switch
    {
        HCompareOp.Eq => "==", HCompareOp.Ne => "!=", HCompareOp.Lt => "<", HCompareOp.Le => "<=", HCompareOp.Gt => ">",
        HCompareOp.Ge => ">=", HCompareOp.LtUn => "<u", HCompareOp.LeUn => "<=u", HCompareOp.GtUn => ">u", _ => ">=u",
    };

    public static string Print(HExpr e, HMethod m)
    {
        switch (e)
        {
            case HConst c:
                return c.Value switch
                {
                    null => "null",
                    string s => "\"" + s.Replace("\\", "\\\\").Replace("\"", "\\\"").Replace("\n", "\\n") + "\"",
                    bool b => b ? "true" : "false",
                    float f => f.ToString("R", CultureInfo.InvariantCulture) + "f",
                    double d => d.ToString("R", CultureInfo.InvariantCulture) + "d",
                    long l => l.ToString(CultureInfo.InvariantCulture) + "L",
                    IFormattable f => f.ToString(null, CultureInfo.InvariantCulture),
                    _ => c.Value.ToString() ?? "?",
                };
            case HLocal l: return l.Variable.Name;
            case HArg a:
                return a.Index < 0 ? "this" : ParameterName(m.Method, a.Index);
            case HMethodPointer p:
                return (p.VirtualOn != null ? $"&virtual({Print(p.VirtualOn, m)}) " : "&") + $"{(p.DeclaringType ?? p.Method.DeclaringType.Sig).ShortName}.{p.Method.Name}";
            case HMemberToken t:
                return t.Method != null ? $"methodof({t.Method.DeclaringType.Name}.{t.Method.Name})" : $"fieldof({t.Field!.DeclaringType.Name}.{t.Field.Name})";
            case HField f:
                return f.Object == null ? f.Field.DeclaringType.Name + "." + f.Field.Name : Print(f.Object, m) + "." + f.Field.Name;
            case HElement el: return $"{Print(el.Array, m)}[{Print(el.Index, m)}]";
            case HArrayLength len: return Print(len.Array, m) + ".Length";
            case HAddressOf addr: return "&" + Print(addr.Target, m);
            case HDeref d: return "*" + Print(d.Pointer, m);
            case HUnary u:
                return (u.Op == HUnaryOp.Neg ? "-" : u.Op == HUnaryOp.Not ? "~" : "!") + "(" + Print(u.Operand, m) + ")";
            case HBinary b: return $"({Print(b.Left, m)} {Binary(b.Op)} {Print(b.Right, m)})";
            case HCompare c: return $"({Print(c.Left, m)} {Compare(c.Op)} {Print(c.Right, m)})";
            case HConv c: return $"conv.{c.Kind.ToString().ToLowerInvariant()}({Print(c.Operand, m)})";
            case HCall call:
            {
                string target = call.This != null ? Print(call.This, m) : (call.DeclaringType ?? call.Method.DeclaringType.Sig).ShortName;
                // A virtual method called as it is in a base class, not as the object's class has it.
                if (call.This is HArg { Index: -1 } && !call.Virtual && call.Method.IsVirtual && !call.Method.DeclaringType.IsValueType) target = "base";
                string generic = call.MethodArguments.Length == 0 ? "" : "<" + string.Join(", ", call.MethodArguments.Select(a => a.ShortName)) + ">";
                string alt = call.Alternatives.Count == 0 ? "" : $" /*or {call.Alternatives.Count} more*/";
                return $"{target}.{call.Method.Name}{generic}({string.Join(", ", call.Arguments.Select(a => Print(a, m)))}){alt}";
            }
            case HNewObject n:
                return $"new {(n.DeclaringType ?? n.Constructor.DeclaringType.Sig).ShortName}({string.Join(", ", n.Arguments.Select(a => Print(a, m)))})";
            case HNewArray na: return $"new {na.ElementType.ShortName}[{Print(na.Length, m)}]";
            case HTypeExpr t:
                return t.Op switch
                {
                    HTypeOp.Box => $"box<{t.Target.ShortName}>({Print(t.Operand!, m)})",
                    HTypeOp.UnboxAny => $"unbox<{t.Target.ShortName}>({Print(t.Operand!, m)})",
                    HTypeOp.IsInst => $"({Print(t.Operand!, m)} as {t.Target.ShortName})",
                    HTypeOp.CastClass => $"(({t.Target.ShortName}){Print(t.Operand!, m)})",
                    HTypeOp.Default => $"default({t.Target.ShortName})",
                    HTypeOp.SizeOf => $"sizeof({t.Target.ShortName})",
                    HTypeOp.Allocate => $"__allocate({t.Target.ShortName})",
                    HTypeOp.StackAlloc => $"stackalloc {t.Target.ShortName}[{Print(t.Operand!, m)}]",
                    _ => $"typeof({t.Target.ShortName})",
                };
            case HSelect s: return $"({Print(s.Condition, m)} ? {Print(s.WhenTrue, m)} : {Print(s.WhenFalse, m)})";
            case HCachedDelegate cached: return $"({Print(cached.Cache, m)} ?? ({Print(cached.Cache, m)} = {Print(cached.Creation, m)}))";
            case HOpaque o: return $"__{o.Text}({string.Join(", ", o.Operands.Select(a => Print(a, m)))})";
            default: return e.GetType().Name;
        }
    }
}
