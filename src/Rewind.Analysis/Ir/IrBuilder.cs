namespace Rewind.Analysis.Ir;

/// <summary>
/// Creates IR nodes in the current block, folding constants and applying local algebraic identities as it goes
/// so that addresses and comparisons come out in a canonical shape.
/// </summary>
public sealed class IrBuilder(Function fn)
{
    public Function Fn { get; } = fn;
    public Block Current = null!;
    public ulong CurrentAddr;

    /// <summary>When set, new nodes go in front of the block's terminator instead of after it.</summary>
    public bool InsertBeforeTerminator;

    /// <summary>When not negative, new nodes are inserted at this position of the block (and it advances).</summary>
    public int InsertIndex = -1;

    /// <summary>Positions the builder so that new nodes land just before <paramref name="before"/>.</summary>
    public void PositionBefore(Block block, Node before)
    {
        Current = block;
        InsertIndex = block.Nodes.IndexOf(before);
        CurrentAddr = before.Addr;
    }

    public Node Raw(Op op, VT type, params Node[] inputs)
    {
        Node n = Fn.NewNode(op, type, Current, inputs);
        n.Addr = CurrentAddr;
        List<Node> nodes = Current.Nodes;
        if (InsertIndex >= 0) nodes.Insert(InsertIndex++, n);
        else if (InsertBeforeTerminator && nodes.Count != 0 && nodes[^1].IsTerminator)
        {
            // A noreturn call sits just before the Unreachable marker; stay ahead of both.
            int at = nodes.Count - 1;
            if (nodes[at].Op == Op.Unreachable && at > 0 && nodes[at - 1].Op == Op.Call) at--;
            nodes.Insert(at, n);
        }
        else nodes.Add(n);
        return n;
    }

    public Node Const(VT type, long value)
    {
        Node n = Fn.NewNode(Op.Const, type, null);
        n.Imm = type.Bits() >= 64 || type.Bits() == 0 ? value : (long)((ulong)value & type.Mask());
        return n;
    }

    public Node Undef(VT type) => Fn.NewNode(Op.Undef, type, null);

    private static long SignExtend(ulong value, VT type)
    {
        int bits = type.Bits();
        if (bits >= 64) return (long)value;
        ulong sign = 1UL << (bits - 1);
        value &= type.Mask();
        return (long)((value ^ sign) - sign);
    }

    public static long SImm(Node n) => SignExtend((ulong)n.Imm, n.Type);

    // ---- integer arithmetic ------------------------------------------------------------------------------------

    public Node Add(Node a, Node b)
    {
        if (a.IsConst && !b.IsConst) (a, b) = (b, a);
        if (b.IsConst)
        {
            if (a.IsConst) return Const(a.Type, a.Imm + b.Imm);
            if (b.UImm == 0) return a;
            if (a.Op == Op.Add && a.In[1].IsConst) return Add(a.In[0], Const(a.Type, a.In[1].Imm + b.Imm));
        }
        return Raw(Op.Add, a.Type, a, b);
    }

    public Node Sub(Node a, Node b)
    {
        if (b.IsConst) return Add(a, Const(a.Type, -b.Imm));
        if (ReferenceEquals(a, b)) return Const(a.Type, 0);
        return Raw(Op.Sub, a.Type, a, b);
    }

    public Node Mul(Node a, Node b)
    {
        if (a.IsConst && !b.IsConst) (a, b) = (b, a);
        if (b.IsConst)
        {
            if (a.IsConst) return Const(a.Type, a.Imm * b.Imm);
            if (b.UImm == 1) return a;
            if (b.UImm == 0) return Const(a.Type, 0);
        }
        return Raw(Op.Mul, a.Type, a, b);
    }

    public Node And(Node a, Node b)
    {
        if (a.IsConst && !b.IsConst) (a, b) = (b, a);
        if (b.IsConst)
        {
            if (a.IsConst) return Const(a.Type, a.Imm & b.Imm);
            if (b.UImm == a.Type.Mask()) return a;
            if (b.UImm == 0) return Const(a.Type, 0);
            // (zext x) & mask keeps x when the mask covers every bit x can have
            if (a.Op == Op.ZExt && (b.UImm & a.In[0].Type.Mask()) == a.In[0].Type.Mask()) return a;
        }
        if (ReferenceEquals(a, b)) return a;
        return Raw(Op.And, a.Type, a, b);
    }

    public Node Or(Node a, Node b)
    {
        if (a.IsConst && !b.IsConst) (a, b) = (b, a);
        if (b.IsConst)
        {
            if (a.IsConst) return Const(a.Type, a.Imm | b.Imm);
            if (b.UImm == 0) return a;
        }
        if (ReferenceEquals(a, b)) return a;
        return Raw(Op.Or, a.Type, a, b);
    }

    public Node Xor(Node a, Node b)
    {
        if (ReferenceEquals(a, b)) return Const(a.Type, 0);
        if (a.IsConst && !b.IsConst) (a, b) = (b, a);
        if (b.IsConst)
        {
            if (a.IsConst) return Const(a.Type, a.Imm ^ b.Imm);
            if (b.UImm == 0) return a;
        }
        return Raw(Op.Xor, a.Type, a, b);
    }

    public Node Not(Node a) => a.IsConst ? Const(a.Type, ~a.Imm) : Raw(Op.Not, a.Type, a);
    public Node Neg(Node a) => a.IsConst ? Const(a.Type, -a.Imm) : Raw(Op.Neg, a.Type, a);

    public Node Shift(Op op, Node a, Node count)
    {
        if (count.IsConst)
        {
            // The CPU uses 6 bits of the count for 64-bit operands and 5 bits otherwise; a rotation wraps at
            // the operand's width.
            int bits = a.Type.Bits();
            int c = (int)(count.UImm & (ulong)(bits == 64 ? 63 : 31));
            if (op is Op.Rol or Op.Ror) c %= bits;
            if (c == 0) return a;
            if (a.IsConst && op is Op.Shl or Op.ShrU or Op.ShrS)
            {
                ulong v = a.UImm;
                long r = op switch
                {
                    Op.Shl => c >= bits ? 0 : (long)(v << c),
                    Op.ShrU => c >= bits ? 0 : (long)(v >> c),
                    _ => SImm(a) >> Math.Min(c, 63),
                };
                return Const(a.Type, r);
            }
            count = Const(VT.I8, c);
        }
        return Raw(op, a.Type, a, count);
    }

    public Node Binary(Op op, Node a, Node b) => op switch
    {
        Op.Add => Add(a, b),
        Op.Sub => Sub(a, b),
        Op.Mul => Mul(a, b),
        Op.And => And(a, b),
        Op.Or => Or(a, b),
        Op.Xor => Xor(a, b),
        Op.Shl or Op.ShrU or Op.ShrS or Op.Rol or Op.Ror => Shift(op, a, b),
        _ => Raw(op, a.Type, a, b),
    };

    // ---- comparisons -------------------------------------------------------------------------------------------

    public Node Cmp(Op op, Node a, Node b)
    {
        if (a.IsConst && b.IsConst && a.Type.IsInt())
        {
            long sa = SImm(a), sb = SImm(b);
            ulong ua = a.UImm, ub = b.UImm;
            bool r = op switch
            {
                Op.CmpEq => ua == ub,
                Op.CmpNe => ua != ub,
                Op.CmpLtS => sa < sb,
                Op.CmpLeS => sa <= sb,
                Op.CmpLtU => ua < ub,
                Op.CmpLeU => ua <= ub,
                _ => false,
            };
            return Const(VT.I1, r ? 1 : 0);
        }
        return Raw(op, VT.I1, a, b);
    }

    /// <summary>Logical negation of an I1 value, kept as a comparison where possible.</summary>
    public Node NotBool(Node c)
    {
        if (c.IsConst) return Const(VT.I1, c.Imm == 0 ? 1 : 0);
        switch (c.Op)
        {
            case Op.CmpEq: return Raw(Op.CmpNe, VT.I1, c.In[0], c.In[1]);
            case Op.CmpNe: return Raw(Op.CmpEq, VT.I1, c.In[0], c.In[1]);
            case Op.CmpLtS: return Raw(Op.CmpLeS, VT.I1, c.In[1], c.In[0]);
            case Op.CmpLeS: return Raw(Op.CmpLtS, VT.I1, c.In[1], c.In[0]);
            case Op.CmpLtU: return Raw(Op.CmpLeU, VT.I1, c.In[1], c.In[0]);
            case Op.CmpLeU: return Raw(Op.CmpLtU, VT.I1, c.In[1], c.In[0]);
            case Op.Xor when c.In[1].IsConstValue(1): return c.In[0];
            default: return Raw(Op.Xor, VT.I1, c, Const(VT.I1, 1));
        }
    }

    public Node Select(Node cond, Node whenTrue, Node whenFalse)
    {
        if (cond.IsConst) return cond.Imm != 0 ? whenTrue : whenFalse;
        if (ReferenceEquals(whenTrue, whenFalse)) return whenTrue;
        return Raw(Op.Select, whenTrue.Type, cond, whenTrue, whenFalse);
    }

    // ---- conversions -------------------------------------------------------------------------------------------

    public Node ZExt(Node a, VT to)
    {
        if (a.Type == to) return a;
        if (a.IsConst) return Const(to, (long)a.UImm);
        if (a.Op == Op.ZExt) return ZExt(a.In[0], to);
        return Raw(Op.ZExt, to, a);
    }

    public Node SExt(Node a, VT to)
    {
        if (a.Type == to) return a;
        if (a.IsConst) return Const(to, SImm(a));
        if (a.Op == Op.SExt) return SExt(a.In[0], to);
        if (a.Op == Op.ZExt) return ZExt(a.In[0], to); // sign bit is known clear
        return Raw(Op.SExt, to, a);
    }

    public Node Trunc(Node a, VT to)
    {
        if (a.Type == to) return a;
        if (a.IsConst) return Const(to, a.Imm);
        switch (a.Op)
        {
            case Op.ZExt or Op.SExt:
            {
                Node inner = a.In[0];
                if (inner.Type == to) return inner;
                if (inner.Type.Bits() > to.Bits()) return Trunc(inner, to);
                return a.Op == Op.ZExt ? ZExt(inner, to) : SExt(inner, to);
            }
            case Op.Trunc:
                return Trunc(a.In[0], to);
            case Op.Concat when to.Bits() <= 32:
                return Trunc(a.In[1], to);
            // The low bits of these depend only on the low bits of their operands, so the narrowing can move
            // inside. This turns 64-bit register arithmetic on 32-bit values back into 32-bit arithmetic.
            case Op.Add or Op.Sub or Op.Mul or Op.And or Op.Or or Op.Xor:
                return Binary(a.Op, Trunc(a.In[0], to), Trunc(a.In[1], to));
            case Op.Neg:
                return Neg(Trunc(a.In[0], to));
            case Op.Not:
                return Not(Trunc(a.In[0], to));
            case Op.Shl when a.In[1].IsConst && (int)a.In[1].UImm < to.Bits():
                return Shift(Op.Shl, Trunc(a.In[0], to), a.In[1]);
            case Op.Select:
                return Select(a.In[0], Trunc(a.In[1], to), Trunc(a.In[2], to));
            // High half of a 64-bit value built from two 32-bit halves.
            case Op.ShrU when to == VT.I32 && a.In[1].IsConstValue(32) && a.In[0].Op == Op.Concat:
                return a.In[0].In[0];
        }
        return Raw(Op.Trunc, to, a);
    }

    public Node Concat(Node hi, Node lo)
    {
        if (hi.IsConst && lo.IsConst) return Const(VT.I64, (long)(hi.UImm << 32 | lo.UImm));
        // The top half of a value under a mask, next to its untouched bottom half: the mask on the whole value
        // (the sign of a double is in its top half: "-d" and "Abs(d)").
        if (hi.Op is Op.Xor or Op.And && hi.In.Length == 2 && hi.In[1].IsConst && lo.Op == Op.Trunc && lo.In[0].Type == VT.I64 &&
            hi.In[0].Op == Op.Trunc && hi.In[0].In[0].Op == Op.ShrU && hi.In[0].In[0].In[1].IsConstValue(32) &&
            ReferenceEquals(hi.In[0].In[0].In[0], lo.In[0]))
        {
            ulong mask = hi.In[1].UImm & 0xFFFFFFFFUL;
            return hi.Op == Op.Xor
                ? Xor(lo.In[0], Const(VT.I64, (long)(mask << 32)))
                : And(lo.In[0], Const(VT.I64, (long)(mask << 32 | 0xFFFFFFFFUL)));
        }
        // Concat(x >> 32, trunc x) is x again.
        if (lo.Op == Op.Trunc && lo.In[0].Type == VT.I64 && hi.Op == Op.Trunc && hi.In[0].Op == Op.ShrU &&
            hi.In[0].In[1].IsConstValue(32) && ReferenceEquals(hi.In[0].In[0], lo.In[0]))
            return lo.In[0];
        // The same where the bottom half was narrowed further in (a stack address: "trunc(rsp) + c").
        if (!NoSumHalves && hi.Op == Op.Trunc && hi.In[0].Op == Op.ShrU && hi.In[0].In[1].IsConstValue(32) &&
            IsLowHalf(lo, hi.In[0].In[0]))
            return hi.In[0].In[0];
        if (hi.IsConstValue(0)) return ZExt(lo, VT.I64);
        return Raw(Op.Concat, VT.I64, hi, lo);
    }

    internal static readonly bool NoSumHalves = Environment.GetEnvironmentVariable("REWIND_NO_SUM_HALVES") != null;
    private static readonly bool NoBottomMasks = Environment.GetEnvironmentVariable("REWIND_NO_BOTTOM_MASKS") != null;

    /// <summary>
    /// Is "low" the bottom 32 bits of the 64-bit "whole"? Narrowing moves inside sums and the like when it is
    /// built (see <see cref="Trunc"/>), so the bottom half of "a + c" is written "trunc(a) + c": the same
    /// operation on the bottom halves of the operands.
    /// </summary>
    internal static bool IsLowHalf(Node low, Node whole, Func<Node, Node>? resolve = null, int depth = 0)
    {
        if (resolve != null) { low = resolve(low); whole = resolve(whole); }
        if (low.Type != VT.I32 || whole.Type != VT.I64) return false;
        if (whole.IsConst) return low.IsConst && (uint)low.UImm == (uint)whole.UImm;
        if (low.Op == Op.Trunc && ReferenceEquals(resolve != null ? resolve(low.In[0]) : low.In[0], whole)) return true;
        if (depth >= 4) return false;
        // A mask that leaves the bottom half alone ("x ^ 8000000000000000h", the sign of a double): the bottom
        // half of x is the bottom half of the masked x.
        if (!NoBottomMasks && whole.Op is Op.Xor or Op.Or or Op.And && whole.In.Length == 2 && whole.In[1].IsConst && low.Op != whole.Op &&
            (uint)whole.In[1].UImm == (whole.Op == Op.And ? uint.MaxValue : 0u))
            return IsLowHalf(low, whole.In[0], resolve, depth + 1);
        if (low.Op != whole.Op || low.In.Length != 2 || whole.In.Length != 2) return false;
        if (whole.Op is not (Op.Add or Op.Sub or Op.Mul or Op.And or Op.Or or Op.Xor)) return false;
        return IsLowHalf(low.In[0], whole.In[0], resolve, depth + 1) && IsLowHalf(low.In[1], whole.In[1], resolve, depth + 1);
    }

    public Node BitsToF(Node bits)
    {
        VT to = bits.Type == VT.I32 ? VT.F32 : VT.F64;
        if (bits.Op == Op.FToBits) return bits.In[0];
        if (bits.IsConst)
        {
            Node c = Fn.NewNode(Op.Const, to, null);
            c.Imm = bits.Imm;
            return c;
        }
        return Raw(Op.BitsToF, to, bits);
    }

    public Node FToBits(Node f)
    {
        VT to = f.Type == VT.F32 ? VT.I32 : VT.I64;
        if (f.Op == Op.BitsToF) return f.In[0];
        if (f.IsConst) return Const(to, f.Imm);
        return Raw(Op.FToBits, to, f);
    }

    // ---- memory ------------------------------------------------------------------------------------------------

    public Node Load(Node address, VT type) => Raw(Op.Load, type, address);
    public Node Store(Node address, Node value) => Raw(Op.Store, VT.None, address, value);
}
