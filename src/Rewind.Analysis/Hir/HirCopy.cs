// Modified by xob0t (2026): gaps always marked, inlined constructor folding. See FORK.md.
namespace Rewind.Analysis.Hir;

/// <summary>
/// Copies of expressions and statements: the same thing written a second time, sharing no nodes with the first,
/// so that either can be changed without the other.
/// </summary>
internal static class HirCopy
{
    /// <summary>
    /// A copy of an expression. Where <paramref name="map"/> gives something for a node, that stands in the copy
    /// in the node's place (as it is: what the map gives is not copied again).
    /// </summary>
    public static HExpr Of(HExpr e, Func<HExpr, HExpr?>? map = null)
    {
        if (map?.Invoke(e) is { } replaced) return replaced;
        HExpr Sub(HExpr x) => Of(x, map);
        HExpr[] All(HExpr[] list) => list.Select(Sub).ToArray();
        HExpr copy = e switch
        {
            HConst c => new HConst(c.Value, c.Type),
            HLocal l => new HLocal(l.Variable),
            HArg a => new HArg(a.Index),
            HField f => new HField { Object = f.Object == null ? null : Sub(f.Object), Field = f.Field, DeclaringType = f.DeclaringType },
            HElement el => new HElement { Array = Sub(el.Array), Index = Sub(el.Index) },
            HArrayLength len => new HArrayLength(Sub(len.Array)),
            HAddressOf a => new HAddressOf(Sub(a.Target)),
            HDeref d => new HDeref(Sub(d.Pointer)),
            HUnary u => new HUnary(u.Op, Sub(u.Operand)),
            HBinary b => new HBinary(b.Op, Sub(b.Left), Sub(b.Right)),
            HCompare c => new HCompare(c.Op, Sub(c.Left), Sub(c.Right)),
            HConv c => new HConv(c.Kind, Sub(c.Operand)),
            HCall call => new HCall
            {
                Method = call.Method, DeclaringType = call.DeclaringType, MethodArguments = call.MethodArguments,
                This = call.This == null ? null : Sub(call.This), Arguments = All(call.Arguments), Virtual = call.Virtual,
                Constrained = call.Constrained, Alternatives = [.. call.Alternatives],
            },
            HNewObject n => new HNewObject { Constructor = n.Constructor, DeclaringType = n.DeclaringType, Arguments = All(n.Arguments) },
            HNewArray na => new HNewArray(na.ElementType, Sub(na.Length)),
            HTypeExpr t => new HTypeExpr(t.Op, t.Target, t.Operand == null ? null : Sub(t.Operand)),
            HMethodPointer p => new HMethodPointer
            {
                Method = p.Method, DeclaringType = p.DeclaringType, MethodArguments = p.MethodArguments,
                VirtualOn = p.VirtualOn == null ? null : new HArg(p.VirtualOn.Index) { Type = p.VirtualOn.Type },
            },
            HMemberToken m => new HMemberToken { Method = m.Method, Field = m.Field, DeclaringType = m.DeclaringType, MethodArguments = m.MethodArguments },
            HCachedDelegate d => new HCachedDelegate((HField)Of(d.Cache), (HNewObject)Of(d.Creation)),
            HSelect s => new HSelect(Sub(s.Condition), Sub(s.WhenTrue), Sub(s.WhenFalse)),
            HOpaque o => new HOpaque(o.Text, All(o.Operands)) { Problem = o.Problem, Remark = o.Remark },
            _ => throw new NotSupportedException("no copy of " + e.GetType().Name),
        };
        copy.Type = e.Type;
        return copy;
    }

    /// <summary>A copy of a statement that does not say where control goes next (see <see cref="Of(HExpr, Func{HExpr, HExpr?}?)"/>); null for one that does.</summary>
    public static HStmt? Of(HStmt s, Func<HExpr, HExpr?>? map = null)
    {
        HStmt? copy = s switch
        {
            HAssign a => new HAssign(Of(a.Target, map), Of(a.Value, map)),
            HEval e => new HEval(Of(e.Expression, map)),
            _ => null,
        };
        if (copy != null) copy.Address = s.Address;
        return copy;
    }
}
