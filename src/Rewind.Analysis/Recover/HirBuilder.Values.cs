using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Analysis.X64;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

public sealed partial class HirBuilder
{
    // ---- constants and leaves ----------------------------------------------------------------------------------

    private Sem ConstSem(Node n)
    {
        switch (n.Type)
        {
            case VT.F32: return new SVal(new HConst(BitConverter.Int32BitsToSingle((int)n.Imm), _float));
            case VT.F64: return new SVal(new HConst(BitConverter.Int64BitsToDouble(n.Imm), _double));
            case VT.I1: return new SVal(new HConst(n.Imm != 0, _bool));
            case VT.I64: return new SVal(new HConst(n.Imm, _long));
            default: return new SVal(new HConst((int)IrBuilder.SImm(n), _int));
        }
    }

    private Sem SlotSem(Node n)
    {
        ulong va = (ulong)n.Imm;
        if (_p.Defaults.Slots.TryGetValue(va, out TypeDef? def)) return new SKlass(def.Sig);
        MetadataUsage? usage = _m.ResolveUsageSlot(va);
        if (usage == null) return SJunk.Instance;
        switch (usage.Kind)
        {
            case UsageKind.TypeInfo: return new SKlass(usage.Type!);
            case UsageKind.Il2CppType: return new SType(usage.Type!);
            case UsageKind.MethodDef: return new SMethod(usage.Method!, null);
            case UsageKind.MethodRef: return new SMethod(usage.Method!, usage.MethodInst);
            case UsageKind.FieldInfo or UsageKind.FieldRva: return new SFieldInfo(usage.Field!);
            case UsageKind.StringLiteral: return new SVal(new HConst(usage.String ?? "", _string));
            default: return SJunk.Instance;
        }
    }

    private Sem ParamSem(Node n)
    {
        if (n.Imm == _fn.Regs.StackPointer) return new SFrame(0);
        return SJunk.Instance; // a register the calling convention gives no meaning on entry
    }

    // ---- the main evaluator ------------------------------------------------------------------------------------

    private Sem Compute(Node n)
    {
        switch (n.Op)
        {
            case Op.Const: return ConstSem(n);
            case Op.Undef: return SJunk.Instance;
            case Op.Param: return ParamSem(n);
            case Op.SlotValue: return SlotSem(n);
            case Op.Phi: return SJunk.Instance; // declared phis already have a meaning; others are flag merges
            case Op.Idiom when (IdiomKind)n.Imm == IdiomKind.InternalCall:
            {
                MethodDef? method = _p.InternalCallNamed((ulong)n.In[0].Imm, out string name);
                if (method != null) return new SNativeCode(method);
                Problem($"internal call not matched to a method ({name})");
                return SJunk.Instance;
            }
            case Op.Idiom when (IdiomKind)n.Imm == IdiomKind.PInvokeTarget:
            {
                if (_p.PInvokeAtSlot((ulong)n.In[0].Imm) is { } import) return new SPInvoke(import.Method);
                Problem("P/Invoke target not matched to a declaration");
                return SJunk.Instance;
            }
            case Op.Idiom when (IdiomKind)n.Imm == IdiomKind.LostRegister:
                if (NoLazyLostRegisters) Problem(LostRegisterUsed);
                return NoLazyLostRegisters ? SJunk.Instance : SLostRegister.Instance;
            case Op.Idiom when (IdiomKind)n.Imm == IdiomKind.CaughtWrapper:
                // The catch object itself (not the exception read through it) means nothing to the program. It
                // turns up where a call captured whatever the stack slots held; used for real, it shows as an
                // undefined value and is reported as such.
                return SJunk.Instance;
            case Op.Idiom when (IdiomKind)n.Imm == IdiomKind.TryEntry:
                Problem("the caught exception is used other than by reading it");
                return SJunk.Instance;
            case Op.Idiom when (IdiomKind)n.Imm == IdiomKind.InterfaceEntry:
            {
                if (EvalKlass(n.In[1]) is not { } iface || !n.In[2].IsConst)
                {
                    Problem("interface of a dispatch not recovered");
                    return SJunk.Instance;
                }
                return new SInterfaceEntry(n.In[0], iface, (int)n.In[2].UImm);
            }
            case Op.Proj: return SJunk.Instance; // set when the call is processed
            case Op.Load: return LoadSem(n);
            case Op.Add: return AddSem(n);
            case Op.Sub or Op.Mul or Op.And or Op.Or or Op.Xor or Op.DivS or Op.DivU or Op.RemS or Op.RemU
                or Op.Shl or Op.ShrU or Op.ShrS:
                return BinarySem(n);
            case Op.Neg: return new SVal(new HUnary(HUnaryOp.Neg, IntValue(n.In[0])) { Type = ResultIntType(n, n.In[0]) });
            case Op.Not: return new SVal(new HUnary(HUnaryOp.Not, IntValue(n.In[0])) { Type = ResultIntType(n, n.In[0]) });
            case Op.CmpEq or Op.CmpNe or Op.CmpLtS or Op.CmpLeS or Op.CmpLtU or Op.CmpLeU:
                return CompareSem(n);
            case Op.FAdd or Op.FSub or Op.FMul or Op.FDiv:
            {
                HBinaryOp op = n.Op switch { Op.FAdd => HBinaryOp.Add, Op.FSub => HBinaryOp.Sub, Op.FMul => HBinaryOp.Mul, _ => HBinaryOp.Div };
                return new SVal(new HBinary(op, FloatValue(n.In[0]), FloatValue(n.In[1])) { Type = n.Type == VT.F32 ? _float : _double });
            }
            case Op.FNeg: return new SVal(new HUnary(HUnaryOp.Neg, FloatValue(n.In[0])) { Type = n.Type == VT.F32 ? _float : _double });
            case Op.FMin or Op.FMax:
            {
                // minss/maxss compute (a < b ? a : b) and (a > b ? a : b) exactly, including for NaN.
                HExpr a = FloatValue(n.In[0]), b = FloatValue(n.In[1]);
                var test = new HCompare(n.Op == Op.FMin ? HCompareOp.Lt : HCompareOp.Gt, a, b) { Type = _bool };
                return new SVal(new HSelect(test, a, b) { Type = a.Type });
            }
            case Op.FAbs: return new SVal(MathCall("Abs", n.Type == VT.F64, FloatValue(n.In[0])));
            case Op.FSqrt: return new SVal(MathCall("Sqrt", n.Type == VT.F64, FloatValue(n.In[0])));
            case Op.FCmpEq: return new SVal(new HCompare(HCompareOp.Eq, FloatValue(n.In[0]), FloatValue(n.In[1])) { Type = _bool });
            case Op.FCmpLt: return new SVal(new HCompare(HCompareOp.Lt, FloatValue(n.In[0]), FloatValue(n.In[1])) { Type = _bool });
            case Op.FCmpLe: return new SVal(new HCompare(HCompareOp.Le, FloatValue(n.In[0]), FloatValue(n.In[1])) { Type = _bool });
            case Op.FCmpUnord:
            {
                HExpr a = FloatValue(n.In[0]), b = FloatValue(n.In[1]);
                var na = new HCompare(HCompareOp.Ne, a, a) { Type = _bool };
                if (Normalizer.SameValue(n.In[0], n.In[1])) return new SVal(na); // "x != x": the NaN test
                var nb = new HCompare(HCompareOp.Ne, b, b) { Type = _bool };
                return new SVal(new HBinary(HBinaryOp.Or, na, nb) { Type = _bool });
            }
            case Op.ZExt or Op.SExt: return ExtendSem(n);
            case Op.Trunc: return TruncSem(n);
            case Op.SIntToF: return new SVal(new HConv(n.Type == VT.F32 ? HConvKind.R4 : HConvKind.R8, IntValue(n.In[0])) { Type = n.Type == VT.F32 ? _float : _double });
            case Op.UIntToF:
            {
                var un = new HConv(HConvKind.RUn, IntValue(n.In[0])) { Type = _double };
                return new SVal(new HConv(n.Type == VT.F32 ? HConvKind.R4 : HConvKind.R8, un) { Type = n.Type == VT.F32 ? _float : _double });
            }
            case Op.FToSInt: return new SVal(new HConv(n.Type == VT.I64 ? HConvKind.I8 : HConvKind.I4, FloatValue(n.In[0])) { Type = n.Type == VT.I64 ? _long : _int });
            case Op.FToUInt: return new SVal(new HConv(n.Type == VT.I64 ? HConvKind.U8 : HConvKind.U4, FloatValue(n.In[0])) { Type = n.Type == VT.I64 ? _ulong : _uint });
            case Op.FExt: return new SVal(new HConv(HConvKind.R8, FloatValue(n.In[0])) { Type = _double });
            case Op.FTrunc: return new SVal(new HConv(HConvKind.R4, FloatValue(n.In[0])) { Type = _float });
            case Op.BitsToF: return BitsToFloatSem(n);
            case Op.FToBits: return Eval(n.In[0]); // same value; consumers decide whether they need the raw bits
            case Op.Concat: return ConcatSem(n);
            case Op.Select:
            {
                if (TypeTestSelect(n) is { } typeTest) return typeTest;
                if (FlaggedTypeTestSelect(n) is { } flaggedTest) return flaggedTest;
                HExpr a = Value(n.In[1]), b = Value(n.In[2]);
                TypeSig? type = a.Type ?? b.Type;
                if (a is HConst { Value: int or long } && b is not HConst && b.Type != null && !NoLowHalves) type = b.Type;
                if (type != null) { a = Coerce(a, type); b = Coerce(b, type); }
                return new SVal(new HSelect(Condition(n.In[0]), a, b) { Type = type });
            }
            case Op.MulHiS or Op.MulHiU:
            {
                // High half of a widening multiply: ((long)a * b) >> bits.
                bool signed = n.Op == Op.MulHiS;
                int bits = n.Type.Bits();
                if (bits != 32) return new SVal(new HOpaque(signed ? "mulhi" : "mulhi_un", IntValue(n.In[0]), IntValue(n.In[1])) { Type = TypeForBits(n.Type) });
                HConvKind widen = signed ? HConvKind.I8 : HConvKind.U8;
                var product = new HBinary(HBinaryOp.Mul, new HConv(widen, IntValue(n.In[0])) { Type = _long }, new HConv(widen, IntValue(n.In[1])) { Type = _long }) { Type = _long };
                var shifted = new HBinary(signed ? HBinaryOp.Shr : HBinaryOp.ShrUn, product, new HConst(32, _int)) { Type = _long };
                return new SVal(new HConv(HConvKind.I4, shifted) { Type = _int });
            }
            case Op.Rol or Op.Ror:
            {
                HExpr x = IntValue(n.In[0]), c = IntValue(n.In[1]);
                int bits = n.Type.Bits();
                var back = new HBinary(HBinaryOp.Sub, new HConst(bits, _int), c) { Type = _int };
                HExpr left = new HBinary(HBinaryOp.Shl, x, n.Op == Op.Rol ? c : back) { Type = x.Type };
                HExpr right = new HBinary(HBinaryOp.ShrUn, x, n.Op == Op.Rol ? back : c) { Type = x.Type };
                return new SVal(new HBinary(HBinaryOp.Or, left, right) { Type = x.Type });
            }
            case Op.AddOvfS or Op.AddOvfU or Op.SubOvfS or Op.SubOvfU or Op.MulOvfS or Op.MulOvfU:
                return new SVal(new HOpaque("overflows_" + n.Op.ToString()[..3].ToLowerInvariant(), IntValue(n.In[0]), IntValue(n.In[1])) { Type = _bool });
            default:
                Problem($"operation {n.Op} has no translation yet");
                return new SVal(new HOpaque(n.Op.ToString().ToLowerInvariant(), n.In.Select(Value).ToArray()) { Type = TypeForBits(n.Type) });
        }
    }

    // ---- operand views -----------------------------------------------------------------------------------------

    /// <summary>A node as an integer operand; float values reaching integer operations are bit reinterpretations.</summary>
    private HExpr IntValue(Node n)
    {
        HExpr e = Value(n);
        return IsFloat(e.Type) ? FloatBits(e) : ScalarOf(e, n.Type.Bits());
    }

    /// <summary>
    /// A struct that is one number and nothing else, where a number of that width is asked for: its field.
    /// (Code that computes with such a struct - its own methods above all - computes with the field.)
    /// </summary>
    private HExpr ScalarOf(HExpr e, int bits)
    {
        HExpr inner = e;
        for (int depth = 0; depth < 4 && IsStructType(inner.Type); depth++)
        {
            TypeLayout layout = _p.Layouts.Of(inner.Type!);
            if (!layout.Known || layout.Fields.Length != 1 || layout.Fields[0].Offset != 0 || layout.Fields[0].Size != layout.Size) return e;
            FieldSlot slot = layout.Fields[0];
            inner = new HField { Object = inner, Field = slot.Field, DeclaringType = inner.Type, Type = slot.Type };
            if (IsStructType(slot.Type)) continue;
            // (A narrower field read into a wider register - a ushort struct loaded with movzx - is still the field.)
            return slot.Type is PrimitiveSig && !IsFloat(slot.Type) && (BitsOf(slot.Type) == bits || (!NoNarrowScalars && BitsOf(slot.Type) < bits)) ? inner : e;
        }
        return e;
    }

    private HExpr FloatValue(Node n)
    {
        HExpr e = Value(n);
        // A variable is what it was declared as, whatever register its bits are in at the moment.
        if (e.Type == null && e is HLocal { Variable.Type: { } declared } local && !NoDeclaredFloats)
        {
            e = new HLocal(local.Variable) { Type = declared };
            return IsFloat(declared) ? e : Coerce(e, n.Type is VT.F64 or VT.I64 ? _double : _float);
        }
        if (e.Type == null) e.Type = n.Type == VT.F32 ? _float : _double;
        else if (!IsFloat(e.Type) && n.Type is VT.F32 or VT.F64) e = Coerce(e, n.Type == VT.F32 ? _float : _double);
        return e;
    }

    private TypeSig ResultIntType(Node n, params Node[] operands)
    {
        if (n.Type == VT.I64)
        {
            foreach (Node o in operands)
                if (Eval(o) is SVal { Type: { } t } && (ReferenceEquals(t, _ulong) || ReferenceEquals(t, _nint))) return t;
            return _long;
        }
        if (n.Type == VT.I32)
        {
            bool allUnsigned = operands.Length != 0;
            foreach (Node o in operands)
            {
                if (o.IsConst) continue;
                if (!(Eval(o) is SVal { Type: { } t } && ReferenceEquals(t, _uint))) allUnsigned = false;
            }
            return allUnsigned && operands.Any(o => !o.IsConst) ? _uint : _int;
        }
        return _int;
    }

    // ---- arithmetic ---------------------------------------------------------------------------------------------

    /// <summary>
    /// The sign of a float is its top bit, and that is how the machine changes it: "xorps x, 80000000h" is "-x"
    /// and "andps x, 7FFFFFFFh" is "Abs(x)", exactly (for every value, NaN included). Like the bits of a float
    /// themselves, the result is the float: whoever needs the bits asks for them.
    /// </summary>
    private HExpr? SignOperation(Node n)
    {
        if (n.Type is not (VT.I32 or VT.I64) || n.In.Length != 2) return null;
        Node value = n.In[0], mask = n.In[1];
        if (!mask.IsConst) (value, mask) = (mask, value);
        if (!mask.IsConst || value.IsConst) return null;
        bool wide = n.Type == VT.I64;
        ulong top = wide ? 0x8000000000000000UL : 0x80000000UL;
        ulong bits = wide ? mask.UImm : mask.UImm & 0xFFFFFFFFUL;
        bool negate = n.Op == Op.Xor && bits == top, absolute = n.Op == Op.And && bits == top - 1;
        if (!negate && !absolute) return null;
        if (Eval(value) is not SVal { Expr: { } operand } || operand is HConst || !ReferenceEquals(operand.Type, wide ? _double : _float)) return null;
        if (negate) return new HUnary(HUnaryOp.Neg, operand) { Type = operand.Type };
        HExpr call = MathCall("Abs", wide, operand);
        return call is HCall ? call : null;
    }

    private static readonly bool NoWideShifts = Environment.GetEnvironmentVariable("REWIND_NO_WIDE_SHIFTS") != null;

    private Sem BinarySem(Node n)
    {
        HBinaryOp op = n.Op switch
        {
            Op.Add => HBinaryOp.Add,
            Op.Sub => HBinaryOp.Sub,
            Op.Mul => HBinaryOp.Mul,
            Op.And => HBinaryOp.And,
            Op.Or => HBinaryOp.Or,
            Op.Xor => HBinaryOp.Xor,
            Op.DivS => HBinaryOp.Div,
            Op.DivU => HBinaryOp.DivUn,
            Op.RemS => HBinaryOp.Rem,
            Op.RemU => HBinaryOp.RemUn,
            Op.Shl => HBinaryOp.Shl,
            Op.ShrU => HBinaryOp.ShrUn,
            _ => HBinaryOp.Shr,
        };

        // Checked arithmetic: the overflow test was a guard that normalization removed and recorded.
        var checkedOps = _l.Normalization.CheckedArithmetic;
        if (n.Op is Op.Add or Op.Sub or Op.Mul && checkedOps.Count != 0)
        {
            (Op Signed, Op Unsigned, HBinaryOp S, HBinaryOp U) map = n.Op switch
            {
                Op.Add => (Op.AddOvfS, Op.AddOvfU, HBinaryOp.AddOvf, HBinaryOp.AddOvfUn),
                Op.Sub => (Op.SubOvfS, Op.SubOvfU, HBinaryOp.SubOvf, HBinaryOp.SubOvfUn),
                _ => (Op.MulOvfS, Op.MulOvfU, HBinaryOp.MulOvf, HBinaryOp.MulOvfUn),
            };
            if (checkedOps.Contains((map.Signed, n.In[0], n.In[1]))) op = map.S;
            else if (checkedOps.Contains((map.Unsigned, n.In[0], n.In[1]))) op = map.U;
        }

        // A boolean combination of comparisons stays boolean.
        if (n.Type == VT.I1)
        {
            if (n.Op == Op.Xor && n.In[1].IsConstValue(1)) return new SVal(Negate(Value(n.In[0])));
            return new SVal(new HBinary(op, Value(n.In[0]), Value(n.In[1])) { Type = _bool });
        }

        if (n.Op is Op.Xor or Op.And && SignOperation(n) is { } signed) return new SVal(signed);
        if (n.Op == Op.Mul && ObjectHash(n) is { } hash) return new SVal(hash);

        // Values that travel together, moved down by whole bytes: the ones that lay above are what is left.
        if (n.Op == Op.ShrU && n.Type == VT.I64 && n.In[1].IsConst && n.In[1].UImm is > 0 and < 64 && n.In[1].UImm % 8 == 0 && !n.In[0].IsConst &&
            PartsOf(Eval(n.In[0])) is { } together && MovedDown(together, (int)n.In[1].UImm / 8) is { } above)
            return above;

        // A small struct held in a register, moved down until only its last field is left: that field. "c >> 24"
        // of a Color32 is c.a (the fields before it are cut out of the register, see TruncSem; the last one needs
        // no cutting).
        if (!NoStructPieces && !NoStructTops && n.Op == Op.ShrU && n.In[1].IsConst && n.In[1].UImm is > 0 and < 64 && n.In[1].UImm % 8 == 0 && !n.In[0].IsConst &&
            Eval(n.In[0]) is SVal { Expr: { } held } && IsStructType(held.Type) && _p.Layouts.Of(held.Type!) is { Known: true } heldLayout &&
            heldLayout.Size == n.Type.Bytes() && (int)n.In[1].UImm / 8 is var from && from < heldLayout.Size &&
            _p.Layouts.FieldExactly(held.Type!, from, heldLayout.Size - from) is { } top && !IsStructType(top.Type) && !IsReference(top.Type) && !IsFloat(top.Type))
        {
            HExpr field = new HField { Object = held, Field = top.Field, DeclaringType = held.Type, Type = top.Type };
            // (What was moved down has zeros above it, whatever the field's sign.)
            bool unsigned = top.Type is PrimitiveSig { Element: Il2CppTypeEnum.U1 or Il2CppTypeEnum.U2 or Il2CppTypeEnum.U4 or Il2CppTypeEnum.Boolean or Il2CppTypeEnum.Char };
            if (!unsigned)
                field = top.Size switch
                {
                    1 => new HConv(HConvKind.U1, field) { Type = _byte },
                    2 => new HConv(HConvKind.U2, field) { Type = _ushort },
                    4 => new HConv(HConvKind.U4, field) { Type = _uint },
                    _ => field,
                };
            if (n.Type == VT.I64) field = new HConv(HConvKind.U8, field) { Type = _ulong };
            return new SVal(field);
        }

        bool isShift = n.Op is Op.Shl or Op.ShrU or Op.ShrS;
        HExpr left = IntValue(n.In[0]), right = isShift ? ShiftCount(n.In[1], n.Type.Bits()) : IntValue(n.In[1]);
        // A shift takes its width from the value shifted: a 64-bit shift of what the program holds as a 32-bit
        // number shifts that number made 64 bits wide ("(long)y << 32", not "y << 32", which shifts by 0).
        if (isShift && n.Type == VT.I64 && !NoWideShifts && left is not HConst && left.Type is PrimitiveSig && !IsFloat(left.Type) && !IsBool(left.Type) &&
            BitsOf(left.Type) is > 0 and < 64)
            left = IsUnsigned(left.Type) ? new HConv(HConvKind.U8, left) { Type = _ulong } : new HConv(HConvKind.I8, left) { Type = _long };
        if (n.Op == Op.ShrU && n.Type == VT.I64 && right is HConst { Value: int down } && down is > 0 and < 64 && PartOfCombined(left, down, 64 - down) is { } upper)
            return new SVal(upper);
        // Logic on truth values stays boolean: "b ^ true" is "!b".
        if (n.Op is Op.And or Op.Or or Op.Xor && IsBool(left.Type) && (IsBool(right.Type) || right is HConst { Value: 0 or 1 }))
        {
            if (right is HConst { Value: int bit })
            {
                if (n.Op == Op.Xor) return new SVal(bit == 0 ? left : new HUnary(HUnaryOp.LogicalNot, left) { Type = _bool });
                if (n.Op == Op.And) return new SVal(bit == 0 ? new HConst(false, _bool) : left);
                return new SVal(bit == 0 ? left : new HConst(true, _bool));
            }
            return new SVal(new HBinary(op, left, right) { Type = _bool });
        }
        // A reference is no number: arithmetic on one (other than the idioms above) is marked.
        if (!NoReferenceArithmetic && (IsReference(left.Type) || IsReference(right.Type)))
        {
            Problem(ReferenceArithmetic);
            return new SVal(Site(new HOpaque("reference_arithmetic", new HBinary(op, left, right) { Type = TypeForBits(n.Type) }) { Type = TypeForBits(n.Type) }, ReferenceArithmetic));
        }
        // Nor is a struct whose fields were not found in the bits computed with.
        if (IsStructType(left.Type)) left = StructAsNumber(left, TypeForBits(n.Type));
        if (IsStructType(right.Type)) right = StructAsNumber(right, TypeForBits(n.Type));
        TypeSig type = isShift ? ResultIntType(n, n.In[0]) : ResultIntType(n, n.In[0], n.In[1]);
        if (n.Op is Op.DivU or Op.RemU or Op.ShrU && ReferenceEquals(type, _int)) type = _uint;
        if (n.Op is Op.DivU or Op.RemU or Op.ShrU && ReferenceEquals(type, _long)) type = _ulong;
        if (n.Type is VT.I32 or VT.I64 && op is HBinaryOp.And or HBinaryOp.Or or HBinaryOp.Xor or HBinaryOp.Add or HBinaryOp.Sub or HBinaryOp.Shl or HBinaryOp.ShrUn)
        {
            bool wide = n.Type == VT.I64;
            // Arithmetic on two constants is a constant.
            if (left is HConst { Value: int or long } first && right is HConst { Value: int or long } second)
            {
                long a = Convert.ToInt64(first.Value), b = Convert.ToInt64(second.Value);
                if (!wide) (a, b) = ((int)a, (int)b);
                int count = (int)(b & (wide ? 63 : 31));
                long value = op switch
                {
                    HBinaryOp.And => a & b,
                    HBinaryOp.Or => a | b,
                    HBinaryOp.Xor => a ^ b,
                    HBinaryOp.Add => unchecked(a + b),
                    HBinaryOp.Sub => unchecked(a - b),
                    HBinaryOp.Shl => wide ? a << count : (int)a << count,
                    _ => wide ? (long)((ulong)a >> count) : (int)((uint)(int)a >> count),
                };
                return new SVal(wide ? new HConst(value, type) : new HConst((int)value, type));
            }
            // ... and nothing added, or put in, changes nothing.
            if (right is HConst { Value: int or long } none && Convert.ToInt64(none.Value) == 0 && op != HBinaryOp.And && left is not HConst) return new SVal(left);
            if (left is HConst { Value: int or long } nothing && Convert.ToInt64(nothing.Value) == 0 && op is HBinaryOp.Or or HBinaryOp.Xor or HBinaryOp.Add && right is not HConst) return new SVal(right);
        }
        return new SVal(new HBinary(op, left, right) { Type = type });
    }

    private static readonly bool NoWholeStructTruncation = Environment.GetEnvironmentVariable("REWIND_NO_WHOLE_STRUCT_TRUNCATION") != null;
    private static readonly bool NoStructNumbers = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_NUMBERS") != null;

    /// <summary>
    /// A struct (not one number: see ScalarOf) whose bytes are computed with as a number. Which of its fields
    /// those bits are was not found; IL has no such conversion, so it is marked.
    /// </summary>
    private HExpr StructAsNumber(HExpr e, TypeSig type)
    {
        if (NoStructNumbers) return e;
        string problem = $"{e.Type!.DisplayName} used as a number";
        Problem(problem);
        return Site(new HOpaque("struct_bits", e) { Type = type }, problem);
    }

    private HExpr NumberAsStruct(HExpr e, TypeSig structType)
    {
        if (NoStructNumbers) return e;
        string problem = $"could not rebuild {structType.DisplayName} from a {e.Type?.DisplayName ?? "number"}";
        Problem(problem);
        return Site(new HOpaque("struct_from_value", e) { Type = structType }, problem);
    }

    private static readonly bool NoReferenceArithmetic = Environment.GetEnvironmentVariable("REWIND_NO_REFERENCE_ARITHMETIC") != null;
    private static readonly bool NoObjectHash = Environment.GetEnvironmentVariable("REWIND_NO_OBJECT_HASH") != null;
    internal const string ReferenceArithmetic = "a reference used as a number";

    /// <summary>
    /// The runtime's hash of an object - what object.GetHashCode and RuntimeHelpers.GetHashCode give - pasted in:
    /// the object's address moved down by 3 and multiplied by 2654435761 (Knuth's multiplicative hash), in 32
    /// bits. On "this" it is "base.GetHashCode()" of object (a direct call of object's method); on another
    /// object RuntimeHelpers.GetHashCode(o). Null for anything else.
    /// </summary>
    private HExpr? ObjectHash(Node n)
    {
        if (NoObjectHash || n.Type != VT.I32 || !n.In[1].IsConst || (uint)n.In[1].UImm != 0x9E3779B1u) return null;
        Node shifted = n.In[0];
        while (shifted.Op is Op.Trunc or Op.ZExt or Op.SExt) shifted = shifted.In[0];
        if (shifted.Op != Op.ShrU || !shifted.In[1].IsConstValue(3)) return null;
        Node address = shifted.In[0];
        while (address.Op is Op.Trunc or Op.ZExt or Op.SExt) address = address.In[0];
        HExpr obj = Value(address);
        if (!IsReference(obj.Type)) return null;
        if (obj is HArg { Index: < 0 } && !_method.DeclaringType.IsValueType &&
            _m.FindType("System.Object")?.Methods.FirstOrDefault(m => m.Name == "GetHashCode" && !m.IsStatic && m.Parameters.Length == 0) is { } own &&
            !ReferenceEquals(own, _method))
            return new HCall { Method = own, This = obj, Virtual = false, Type = _int };
        // (Not in the method that is the hash itself: there it would call itself.)
        if (_m.FindType("System.Runtime.CompilerServices.RuntimeHelpers")?.Methods.FirstOrDefault(m =>
                m.Name == "GetHashCode" && m.IsStatic && m.Parameters.Length == 1 && m.Parameters[0].Type is PrimitiveSig { Element: Il2CppTypeEnum.Object }) is { } helper &&
            !ReferenceEquals(helper, _method))
            return new HCall { Method = helper, Arguments = [obj], Type = _int };
        return null;
    }

    /// <summary>
    /// The logical negation of a condition. Integer comparisons flip; floating point comparisons only flip
    /// between == and != (the others differ for NaN and keep an explicit "not").
    /// </summary>
    private HExpr Negate(HExpr e)
    {
        switch (e)
        {
            case HConst { Value: bool b }:
                return new HConst(!b, _bool);
            case HUnary { Op: HUnaryOp.LogicalNot } u:
                return u.Operand;
            case HCompare c:
            {
                bool isFloat = IsFloat(c.Left.Type) || IsFloat(c.Right.Type);
                HCompareOp? flipped = c.Op switch
                {
                    HCompareOp.Eq => HCompareOp.Ne,
                    HCompareOp.Ne => HCompareOp.Eq,
                    _ when isFloat => null,
                    HCompareOp.Lt => HCompareOp.Ge,
                    HCompareOp.Le => HCompareOp.Gt,
                    HCompareOp.Gt => HCompareOp.Le,
                    HCompareOp.Ge => HCompareOp.Lt,
                    HCompareOp.LtUn => HCompareOp.GeUn,
                    HCompareOp.LeUn => HCompareOp.GtUn,
                    HCompareOp.GtUn => HCompareOp.LeUn,
                    _ => HCompareOp.LtUn,
                };
                if (flipped is { } op) return new HCompare(op, c.Left, c.Right) { Type = _bool };
                break;
            }
        }
        return new HUnary(HUnaryOp.LogicalNot, e) { Type = _bool };
    }

    /// <summary>
    /// A shift count as the program wrote it. IL and C# use only the low 5 (or 6) bits of the count, exactly
    /// as the CPU does, so masking and narrowing of the count carry no meaning; a negated count is the
    /// "width - count" of a rotation.
    /// </summary>
    private HExpr ShiftCount(Node count, int bits)
    {
        int needed = bits == 64 ? 63 : 31;
        Node c = count;
        while (true)
        {
            if (c.Op == Op.And && c.In[1].IsConst && ((int)c.In[1].UImm & needed) == needed) c = c.In[0];
            else if (c.Op is Op.Trunc or Op.ZExt or Op.SExt && c.Type.Bits() >= 8 && c.In[0].Type.Bits() >= 8) c = c.In[0];
            else break;
        }
        if (c.Op == Op.Neg)
            return new HBinary(HBinaryOp.Sub, new HConst(bits == 64 ? 64 : 32, _int), ShiftCount(c.In[0], bits)) { Type = _int };
        if (c.IsConst) return new HConst((int)(c.UImm & (ulong)needed), _int);
        return IntValue(c);
    }

    /// <summary>Whether a value compared at 8 or 16 bits is one the program holds as a signed number of that width.</summary>
    private bool HeldSigned(Node n)
    {
        int bits = n.Type.Bits();
        if (bits is not (8 or 16) || n.IsConst) return false;
        HExpr e = ScalarOf(Value(n), bits);
        return e is not HConst && BitsOf(e.Type) == bits && !IsBool(e.Type) && IsSignedSmall(e.Type);
    }

    /// <summary>
    /// An operand of a comparison performed on 8 or 16 bits. Only those bits take part, so a wider expression
    /// is cut down first (with the signedness the comparison uses).
    /// </summary>
    private HExpr CompareOperand(Node n, bool signed)
    {
        int bits = n.Type.Bits();
        HExpr e = ScalarOf(Value(n), bits);
        if (bits is not (8 or 16)) return e;
        // A constant, as a number of the kind the other side is compared as: the byte 0xFF is 255 next to an
        // unsigned value and -1 next to a signed one. ("(byte)x != -1" is always true.)
        if (e is HConst { Value: int or long } constant && !IsBool(constant.Type))
        {
            long value = Convert.ToInt64(constant.Value);
            long ranged = (bits, signed) switch { (8, true) => (sbyte)value, (8, false) => (byte)value, (16, true) => (short)value, _ => (ushort)value };
            return ranged == value ? e : new HConst(constant.Value is long ? ranged : (int)ranged, constant.Type);
        }
        if (e is HConst) return e;
        int known = BitsOf(e.Type);
        if (known == bits && (IsBool(e.Type) || IsSignedSmall(e.Type) == signed)) return e;
        HConvKind kind = (bits, signed) switch
        {
            (8, true) => HConvKind.I1,
            (8, false) => HConvKind.U1,
            (16, true) => HConvKind.I2,
            _ => HConvKind.U2,
        };
        TypeSig type = (bits, signed) switch { (8, true) => _sbyte, (8, false) => _byte, (16, true) => _short, _ => _ushort };
        if (e is HConv { Kind: HConvKind.I1 or HConvKind.U1 or HConvKind.I2 or HConvKind.U2 } c && BitsOf(c.Type) == bits)
            return new HConv(kind, c.Operand) { Type = type };
        return new HConv(kind, e) { Type = type };
    }

    private static readonly bool NoHeldSigned = Environment.GetEnvironmentVariable("REWIND_NO_HELD_SIGNED") != null;

    private Sem CompareSem(Node n)
    {
        HCompareOp op = n.Op switch
        {
            Op.CmpEq => HCompareOp.Eq,
            Op.CmpNe => HCompareOp.Ne,
            Op.CmpLtS => HCompareOp.Lt,
            Op.CmpLeS => HCompareOp.Le,
            Op.CmpLtU => HCompareOp.LtUn,
            _ => HCompareOp.LeUn,
        };
        if (TypeTestCompare(n) is { } typeTest) return typeTest;
        // "x as T" of a struct T against zero, before the operands become numbers: taken as a number, a T that is
        // one number became that number - its field read out of the box, which is null where x is no T.
        if (n.Op is Op.CmpEq or Op.CmpNe && !NoBoxedTests)
        {
            Node x = n.In[0], y = n.In[1];
            if (x.IsConstValue(0)) (x, y) = (y, x);
            if (y.IsConstValue(0) && Eval(x) is SVal { Expr: HTypeExpr { Op: HTypeOp.IsInst, Target: var tested } boxTest } && !IsReference(tested))
                return new SVal(new HCompare(op, boxTest, new HConst(null, _object)) { Type = _bool });
        }
        bool signedCompare = n.Op is Op.CmpLtS or Op.CmpLeS;
        // Equal or not is the same question either way: asked the way the values are held ("x != -1" of an sbyte).
        if (n.Op is Op.CmpEq or Op.CmpNe && !NoHeldSigned) signedCompare = HeldSigned(n.In[0]) || HeldSigned(n.In[1]);
        HExpr left = CompareOperand(n.In[0], signedCompare), right = CompareOperand(n.In[1], signedCompare);

        // A truth value compared with zero is the value itself, or its negation.
        if (n.Op is Op.CmpEq or Op.CmpNe)
        {
            if (IsBool(right.Type) && left is HConst) (left, right) = (right, left);
            if (IsBool(left.Type) && right is HConst { Value: int zeroOrOne } && zeroOrOne is 0 or 1)
            {
                bool wantTrue = (n.Op == Op.CmpNe) == (zeroOrOne == 0);
                return new SVal(wantTrue ? left : new HUnary(HUnaryOp.LogicalNot, left) { Type = _bool });
            }
        }

        // "x as T" is the object or nothing, also where T is a struct (the object is then a boxed one): measured
        // against zero it asks whether there is one. (Taken as a T, the zero became a number, and the test an
        // unboxing of the object as that number.)
        if (n.Op is Op.CmpEq or Op.CmpNe)
        {
            if (right is HTypeExpr { Op: HTypeOp.IsInst } && left is HConst) (left, right) = (right, left);
            if (left is HTypeExpr { Op: HTypeOp.IsInst, Target: var tested } && !IsReference(tested) && right is HConst { Value: null or 0 or 0L or false })
                return new SVal(new HCompare(op, left, new HConst(null, _object)) { Type = _bool });
        }

        // Comparing a reference with the constant 0 is a null test.
        if (IsReference(left.Type) || left.Type is ByRefSig or PointerSig) right = Coerce(right, left.Type!);
        else if (IsReference(right.Type) || right.Type is ByRefSig or PointerSig) left = Coerce(left, right.Type!);
        // A reference measured against nothing, as numbers: "nothing is less than it" is "there is one", "it is
        // no more than nothing" is "there is none".
        if (op == HCompareOp.LtUn && left is HConst { Value: null } && right is not HConst && (IsReference(right.Type) || right.Type is ByRefSig or PointerSig))
            return new SVal(new HCompare(HCompareOp.Ne, right, left) { Type = _bool });
        if (op == HCompareOp.LeUn && right is HConst { Value: null } && left is not HConst && (IsReference(left.Type) || left.Type is ByRefSig or PointerSig))
            return new SVal(new HCompare(HCompareOp.Eq, left, right) { Type = _bool });
        // An unsigned comparison of values the program treats as unsigned reads as a plain comparison.
        if (op == HCompareOp.LtUn && IsUnsigned(left.Type) && (IsUnsigned(right.Type) || right is HConst)) op = HCompareOp.Lt;
        if (op == HCompareOp.LeUn && IsUnsigned(left.Type) && (IsUnsigned(right.Type) || right is HConst)) op = HCompareOp.Le;
        return new SVal(new HCompare(op, left, right) { Type = _bool });
    }

    // ---- conversions --------------------------------------------------------------------------------------------

    private static int BitsOf(TypeSig? t) => t switch
    {
        PrimitiveSig p => p.Element switch
        {
            Il2CppTypeEnum.Boolean or Il2CppTypeEnum.I1 or Il2CppTypeEnum.U1 => 8,
            Il2CppTypeEnum.Char or Il2CppTypeEnum.I2 or Il2CppTypeEnum.U2 => 16,
            Il2CppTypeEnum.I4 or Il2CppTypeEnum.U4 or Il2CppTypeEnum.R4 => 32,
            Il2CppTypeEnum.I8 or Il2CppTypeEnum.U8 or Il2CppTypeEnum.R8 or Il2CppTypeEnum.I or Il2CppTypeEnum.U => 64,
            _ => 0,
        },
        { Definition: { IsEnum: true, EnumUnderlyingType: { } u } } => BitsOf(u),
        _ => 0,
    };

    private static bool IsSignedSmall(TypeSig? t) => t switch
    {
        PrimitiveSig p => p.Element is Il2CppTypeEnum.I1 or Il2CppTypeEnum.I2 or Il2CppTypeEnum.I4 or Il2CppTypeEnum.I8,
        { Definition: { IsEnum: true, EnumUnderlyingType: { } u } } => IsSignedSmall(u),
        _ => false,
    };

    private Sem ExtendSem(Node n)
    {
        Node inner = n.In[0];
        bool zero = n.Op == Op.ZExt;
        Sem s = Eval(inner);
        if (s is not SVal v) return s; // references and other non-numeric meanings pass through unchanged
        HExpr e = v.Expr;
        int from = inner.Type.Bits(), to = n.Type.Bits();
        // A float's bytes made wider are its bits made wider. Converting the float itself would turn 60f into 60.
        if (ReferenceEquals(e.Type, _float) && from <= 32) e = FloatBits(e);
        // A constant made wider is a constant.
        if (to == 64 && from is 8 or 16 or 32 && e is HConst { Value: int or long } constant)
        {
            long bits = Convert.ToInt64(constant.Value) & ((1L << from) - 1);
            if (!zero && (bits & (1L << (from - 1))) != 0) bits |= -1L << from;
            return new SVal(new HConst(bits, _long));
        }
        int known = BitsOf(e.Type);

        // A value whose managed type already has the source width extends implicitly when loaded.
        if (known == from && from < 32)
        {
            bool signed = IsSignedSmall(e.Type);
            if (zero != signed)
            {
                if (to <= 32) return v;
                return new SVal(new HConv(zero ? HConvKind.U8 : HConvKind.I8, e) { Type = zero ? _ulong : _long });
            }
        }
        if (inner.Type == VT.I1) return to <= 32 ? v : new SVal(new HConv(HConvKind.U8, e) { Type = _long });

        if (from < 32)
        {
            HConvKind kind = (from, zero) switch
            {
                (8, true) => HConvKind.U1,
                (8, false) => HConvKind.I1,
                (16, true) => HConvKind.U2,
                _ => HConvKind.I2,
            };
            TypeSig small = (from, zero) switch { (8, true) => _byte, (8, false) => _sbyte, (16, true) => _ushort, _ => _short };
            HExpr narrowed = new HConv(kind, e) { Type = small };
            if (to <= 32) return new SVal(narrowed);
            return new SVal(new HConv(zero ? HConvKind.U8 : HConvKind.I8, narrowed) { Type = zero ? _ulong : _long });
        }
        // 32 -> 64
        if (IsReference(e.Type) || e.Type is ByRefSig or PointerSig) return v;
        // A small struct travelling in a register: clearing the rest of the register does nothing to it.
        if (IsStructType(e.Type)) return v;
        return new SVal(new HConv(zero ? HConvKind.U8 : HConvKind.I8, e) { Type = zero ? _ulong : _long });
    }

    private Sem TruncSem(Node n)
    {
        Node inner = n.In[0];
        int to = n.Type.Bits();

        // A piece of several values that travel together: the one that sits at those bytes.
        {
            Node source = inner;
            int shift = 0;
            if (inner.Op == Op.ShrU && inner.In[1].IsConst && inner.In[1].UImm % 8 == 0)
            {
                source = inner.In[0];
                shift = (int)inner.In[1].UImm / 8;
            }
            if (!source.IsConst && PartsOf(Eval(source)) is { } parts)
            {
                foreach (Part p in parts)
                    if (p.Offset == shift && p.Size * 8 == to)
                        return new SVal(p.Value);
                // ... or the one those bytes are a piece of.
                if (to is 8 or 16 or 32)
                    foreach (Part p in parts)
                        if (p.Offset <= shift && shift + to / 8 <= p.Offset + p.Size && !IsReference(p.Value.Type) && !IsStructType(p.Value.Type))
                            return new SVal(ExtractPart(BitsOfValue(p.Value, p.Size), shift - p.Offset, to / 8, to switch { 8 => _byte, 16 => _ushort, _ => _int }));
            }
        }

        // A piece of a small struct held in a register, or of a field of a struct that other fields are laid
        // over (a union): the field that is exactly those bytes. "(byte)(c.rgba >> 8)" is c.g, "(byte)c" is c.r.
        if (!NoStructPieces && to is 8 or 16 or 32)
        {
            Node source = inner;
            int shift = 0;
            if (inner.Op == Op.ShrU && inner.In[1].IsConst && inner.In[1].UImm % 8 == 0 && inner.In[1].UImm < 64)
            {
                source = inner.In[0];
                shift = (int)inner.In[1].UImm / 8;
            }
            if (!source.IsConst && Eval(source) is SVal { Expr: { } whole })
            {
                if (whole is HField { Object: { } holder, Field: { IsStatic: false } over } && IsStructType(holder.Type) && !IsStructType(whole.Type) &&
                    Array.FindIndex(_p.Layouts.Of(holder.Type!).Fields, x => ReferenceEquals(x.Field, over)) is >= 0 and var at &&
                    _p.Layouts.Of(holder.Type!).Fields[at] is var wide && shift + to / 8 <= wide.Size && (shift != 0 || to / 8 != wide.Size) &&
                    _p.Layouts.FieldExactly(holder.Type!, wide.Offset + shift, to / 8) is { } piece && !ReferenceEquals(piece.Field, over) && !IsStructType(piece.Type))
                    return new SVal(new HField { Object = holder, Field = piece.Field, DeclaringType = holder.Type, Type = piece.Type });
                if (IsStructType(whole.Type) && _p.Layouts.Of(whole.Type!) is { Known: true } layout && shift + to / 8 <= layout.Size &&
                    (shift != 0 || _p.Layouts.FieldAt(whole.Type!, 0) is not { Offset: 0 } first || first.Size * 8 != to) &&
                    _p.Layouts.FieldExactly(whole.Type!, shift, to / 8) is { } part && !IsStructType(part.Type))
                    return new SVal(new HField { Object = whole, Field = part.Field, DeclaringType = whole.Type, Type = part.Type });
            }
        }

        // Halves of a 64-bit quantity: trunc(x) is the low half, trunc(x >> 32) the high half.
        if (to == 32 && inner.Type == VT.I64)
        {
            Node source = inner;
            bool high = false;
            if (inner.Op == Op.ShrU && inner.In[1].IsConstValue(32))
            {
                source = inner.In[0];
                high = true;
            }
            Sem ss = Eval(source);
            if (ss is SPair pair) return new SVal(high ? pair.High : pair.Low);
            if (ss is SVal { Type: { } wide } sv)
            {
                if (ReferenceEquals(wide, _double)) return new SHalf(sv.Expr, high, null);
                if (wide.Definition is { IsValueType: true, IsEnum: false } && wide is not PrimitiveSig)
                {
                    FieldSlot? slot = _p.Layouts.FieldAt(wide, high ? 4 : 0);
                    if (slot is { } fs && fs.Size == 4 && fs.Offset == (high ? 4 : 0))
                        return new SVal(new HField { Object = sv.Expr, Field = fs.Field, DeclaringType = wide, Type = fs.Type });
                }
            }
            if (high) goto general;
        }

        {
            Sem s = Eval(inner);
            // Part of a run of values with no single field at these bytes: cut it out of the combined number.
            if (s is SPair or SParts) s = new SVal(Value(inner));
            if (s is not SVal v) return s;
            HExpr e = v.Expr;
            int known = BitsOf(e.Type);
            // Already no wider than the target: the truncation only drops undefined upper register bits.
            if (known != 0 && known <= to) return v;
            if (IsReference(e.Type)) return v;
            if (e is HConst) return v;
            // A small struct held in a register: taking its low bytes reads its first field.
            if (e.Type?.Definition is { IsValueType: true, IsEnum: false } && e.Type is not PrimitiveSig)
            {
                FieldSlot? slot = _p.Layouts.FieldAt(e.Type, 0);
                if (slot is { } fs && fs.Offset == 0 && fs.Size * 8 == to)
                    return new SVal(new HField { Object = e, Field = fs.Field, DeclaringType = e.Type, Type = fs.Type });
                // All of the struct fits: the truncation only drops the register bits above it.
                if (!NoWholeStructTruncation && _p.Layouts.Of(e.Type) is { Known: true, Size: > 0 } whole && whole.Size * 8 <= to) return v;
                // A struct that is one wider number: its low bytes are that number's ("(byte)delta" is (byte)delta.packed).
                if (!NoNarrowScalars && ScalarOf(e, 64) is { } scalar && !ReferenceEquals(scalar, e))
                {
                    e = scalar;
                    known = BitsOf(e.Type);
                    if (known != 0 && known <= to) return new SVal(e);
                }
                if (IsStructType(e.Type)) return new SVal(StructAsNumber(e, TypeForBits(n.Type)));
            }
            if (known == 0 && inner.Type == VT.I64 && to == 32 && e.Type == null) return v; // untyped 32-bit value in a 64-bit register
            // The low bytes of a float or double are part of its bits, not the number converted.
            if (IsFloat(e.Type)) e = FloatBits(e);
            HConvKind kind = to switch { 8 => HConvKind.U1, 16 => HConvKind.U2, 32 => HConvKind.I4, _ => HConvKind.I8 };
            TypeSig type = to switch { 8 => _byte, 16 => _ushort, 32 => _int, _ => _long };
            if (to == 1) return new SVal(new HCompare(HCompareOp.Ne, new HBinary(HBinaryOp.And, e, new HConst(1, _int)) { Type = _int }, new HConst(0, _int)) { Type = _bool });
            if (to is 8 or 16 or 32) return new SVal(Shortened(kind, type, PartOfCombined(e, 0, to) ?? e, to));
            return new SVal(new HConv(kind, e) { Type = type });
        }

    general:
        {
            HExpr e = IntValue(inner);
            if (IsStructType(e.Type)) return new SVal(StructAsNumber(e, TypeForBits(n.Type)));
            HConvKind kind = to switch { 8 => HConvKind.U1, 16 => HConvKind.U2, 32 => HConvKind.I4, _ => HConvKind.I8 };
            TypeSig type = to switch { 8 => _byte, 16 => _ushort, 32 => _int, _ => _long };
            if (to is 8 or 16 or 32) return new SVal(Shortened(kind, type, PartOfCombined(e, 0, to) ?? e, to));
            return new SVal(new HConv(kind, e) { Type = type });
        }
    }

    private Sem BitsToFloatSem(Node n)
    {
        Sem s = Eval(n.In[0]);
        TypeSig target = n.Type == VT.F32 ? _float : _double;
        switch (s)
        {
            case SVal v when IsFloat(v.Type):
                return v;
            case SVal { Expr: HConst c } when c.Value is int i && n.Type == VT.F32:
                return new SVal(new HConst(BitConverter.Int32BitsToSingle(i), _float));
            case SVal { Expr: HConst c } when c.Value is long l && n.Type == VT.F64:
                return new SVal(new HConst(BitConverter.Int64BitsToDouble(l), _double));
            // A merged value no way in gave a type (each one a number: the bits of 1f here, of -1f there),
            // read as a float: it is a float. Declared as a number all the same, it is noted for the next build
            // to declare it a float (RefineFloatPhis); until then its bits are read as one.
            case SVal { Expr: HLocal { Variable: var merged } } v when v.Type == null && !NoFloatPhiBits && _phiOfVar.TryGetValue(merged, out Node? phi):
                _floatUses[phi] = (_floatUses.GetValueOrDefault(phi).Count + 1, target);
                if (IsFloat(merged.Type)) return new SVal(new HLocal(merged) { Type = merged.Type });
                return new SVal(ValueFromBits(new HLocal(merged) { Type = merged.Type }, target, n.Type == VT.F32 ? 4 : 8));
            case SVal v when v.Type == null:
                // An untyped temporary whose only meaning so far is "bits": it is the float itself.
                v.Expr.Type = target;
                return v;
            case SVal v:
                return new SVal(ValueFromBits(v.Expr, target, n.Type == VT.F32 ? 4 : 8));
            case SHalf h when h.Part != null:
                return new SVal(h.Part);
            default:
                return new SVal(ValueFromBits(Value(n.In[0]), target, n.Type == VT.F32 ? 4 : 8));
        }
    }

    private Sem ConcatSem(Node n)
    {
        Sem hi = Eval(n.In[0]), lo = Eval(n.In[1]);
        if (hi is SHalf { High: true } h && lo is SHalf { High: false } l && ReferenceEquals(h.Whole, l.Whole))
            return _halvedRefs.TryGetValue(h.Whole, out SRef? reference) ? reference : new SVal(h.Whole);
        if (hi is SVal hv && lo is SVal lv)
        {
            // Two 4-byte values side by side. Whether they are one 64-bit number or a pair of fields depends on
            // who consumes them, so keep them separate.
            return new SPair(lv.Expr, hv.Expr);
        }
        if (hi is SHalf { Part: { } hp } && lo is SHalf { Part: { } lp }) return new SPair(lp, hp);
        if (hi is SJunk && lo is SJunk) return SJunk.Instance;
        // Two unrelated 32-bit quantities side by side: keep them apart; whoever needs one number combines them.
        HExpr low = lo is SJunk ? new HConst(0, _int) : Value(n.In[1]);
        HExpr high = hi is SJunk ? new HConst(0, _int) : Value(n.In[0]);
        return new SPair(low, high);
    }

    // ---- addresses ----------------------------------------------------------------------------------------------

    private abstract record Place;
    private sealed record PLocation(HExpr Location, TypeSig Type) : Place;
    private sealed record PPair(HExpr Low, HExpr High) : Place;
    private sealed record PArrayLength(HExpr Array) : Place;
    /// <summary>One of two fields of different classes, chosen by a test: a value to read ("c ? (Renderer)a : b"), no place to write.</summary>
    private sealed record PChosenValue(HExpr Value) : Place;
    private sealed record PObjKlass(Node Object) : Place;
    private sealed record PStatics(TypeSig Type) : Place;
    private sealed record PVTable(Node Object, int Slot, bool MethodInfo) : Place;
    private sealed record PInternal(string What) : Place;
    /// <summary>The class pointer kept in a method's runtime record.</summary>
    private sealed record PKlassOf(TypeSig Type) : Place;
    /// <summary>The code pointer kept in a method's runtime record.</summary>
    private sealed record PMethodCode(SMethod Method) : Place;
    /// <summary>The pointer to a runtime generic context (of a class or a method), and one entry of such a context.</summary>
    private sealed record PRgctx(SRgctx Context) : Place;
    private sealed record PRgctxItem(SRgctx Context, int Index) : Place;
    private sealed record PUnboxed(Node Object, int Offset) : Place;
    private record PUnknown(string Why) : Place;
    /// <summary>
    /// Bytes of a struct that are not one of its fields nor a run of whole fields: [Offset, Offset + Size) of the
    /// struct at Owner. Unknown as a place of its own, but a struct copied in such pieces is a struct copy.
    /// </summary>
    private sealed record PChunk(HExpr Owner, TypeSig OwnerType, int Offset, int Size, string Why) : PUnknown(Why);
    /// <summary>Bytes [Shift, Shift + Size) of an integer variable: part of a stack slot accessed at several widths.</summary>
    private sealed record PBits(HVar Variable, int Shift, int Size) : Place;

    private readonly record struct AddressParts(Node? Base, Sem? BaseSem, long Offset, Node? Index, long Scale);

    private static readonly bool NoStringChars = Environment.GetEnvironmentVariable("REWIND_NO_STRING_CHARS") != null;

    /// <summary>
    /// A character of a string read by index ("s[i]" inlined: the two bytes at the string's first character
    /// plus twice the index), as the string's indexer reads it. Reads only: a string is not written.
    /// </summary>
    private Place? StringChar(HExpr text, TypeSig type, AddressParts a, int size)
    {
        if (type.Key != _string.Key || size != 2 || a.Scale != 2 || a.Index == null) return null;
        FieldSlot? first = null;
        foreach (FieldSlot slot in _p.Layouts.Of(_string).Fields)
            if (slot.Type.Key == _char.Key && slot.Size == 2)
                first = slot;
        if (first is not { } chars || a.Offset < chars.Offset || (a.Offset - chars.Offset) % 2 != 0) return null;
        MethodDef? indexer = _string.Definition?.Methods.FirstOrDefault(m => m.Name == "get_Chars" && !m.IsStatic && m.Parameters.Length == 1 &&
                                                                            m.Parameters[0].Type.Key == _int.Key);
        if (indexer == null) return null;
        HExpr index = IndexValue(a.Index, (a.Offset - chars.Offset) / 2);
        return new PChosenValue(new HCall { Method = indexer, This = text, Arguments = [index], Type = _char });
    }

    private static readonly bool NoChosenFields = Environment.GetEnvironmentVariable("REWIND_NO_CHOSEN_FIELDS") != null;
    private static readonly bool NoFloatPhiBits = Environment.GetEnvironmentVariable("REWIND_NO_FLOAT_PHI_BITS") != null;

    /// <summary>
    /// "c ? o.b : o.a" of two fields side by side: the C++ compiler reads the field at a.Offset + a.Scale * c,
    /// c being 0 or 1. Where the index is a bool (or a bool turned around), that is the address of one field or
    /// the other, chosen by it - provided both are fields of one type, each read whole.
    /// </summary>
    private Place? ChosenField(HExpr obj, TypeSig type, AddressParts a, int size)
    {
        // The index, through the widenings and narrowings that keep a 0 or 1 what it is.
        Node index = a.Index!;
        bool turned = false;
        for (int depth = 0; depth < 8; depth++)
        {
            if (index.Op is Op.ZExt or Op.Trunc && index.In[0].Type.IsInt()) index = index.In[0];
            else if (index.Op == Op.Xor && index.In[1].IsConstValue(1))
            {
                turned = !turned;
                index = index.In[0];
            }
            else break;
        }
        HExpr? condition = null;
        if (index.Type == VT.I1) condition = Condition(index);
        else if (Peek(index) is SVal { Type: var known } && (ReferenceEquals(known, _bool) || known is PrimitiveSig { Element: Il2CppTypeEnum.Boolean })) condition = Value(index);
        if (condition == null) return null;
        if (FieldPlace(obj, type, (int)a.Offset, size) is not PLocation first || FieldPlace(obj, type, (int)(a.Offset + a.Scale), size) is not PLocation second)
            return null;
        if (first.Type.Key != second.Type.Key)
        {
            // Two references of different classes ("skinned ? skinnedRenderer : meshRenderer"): read as the class
            // both are.
            if (NoChosenReferences || !IsReference(first.Type) || !IsReference(second.Type) || size != _p.Model.Image.PointerSize ||
                CommonBase(first.Type, second.Type) is not { } common) return null;
            HExpr one = turned ? first.Location : second.Location, zero = turned ? second.Location : first.Location;
            return new PChosenValue(new HSelect(condition, one, zero) { Type = common });
        }
        if (_p.Layouts.SizeOf(first.Type) is not { Known: true } bytes || (size > 0 && bytes.Size != size)) return null;
        TypeSig reference = _m.Sigs.ByRef(first.Type);
        HExpr whenOne = new HAddressOf(second.Location) { Type = reference }, whenZero = new HAddressOf(first.Location) { Type = reference };
        var picked = new HSelect(condition, turned ? whenZero : whenOne, turned ? whenOne : whenZero) { Type = reference };
        return new PLocation(new HDeref(picked) { Type = first.Type }, first.Type);
    }

    private static readonly bool NoChosenReferences = Environment.GetEnvironmentVariable("REWIND_NO_CHOSEN_REFERENCES") != null;

    /// <summary>The nearest class both classes derive from (object at the latest); null for anything but two classes.</summary>
    private TypeSig? CommonBase(TypeSig a, TypeSig b)
    {
        if (a.Definition is not { IsValueType: false, IsInterface: false } || b.Definition is not { IsValueType: false, IsInterface: false }) return null;
        if (a is GenericInstSig || b is GenericInstSig) return null;
        var ancestors = new List<string>();
        for (TypeSig? t = a; t != null && ancestors.Count < 64; t = t.Definition?.BaseType) ancestors.Add(t.Key);
        for (TypeSig? t = b; t != null && ancestors.Count < 128; t = t.Definition?.BaseType)
            if (ancestors.Contains(t.Key)) return t;
        return _object;
    }

    private static Node StripExtension(Node n)
    {
        while (n.Op is Op.SExt or Op.ZExt) n = n.In[0];
        return n;
    }

    /// <summary>
    /// Splits an address into base + constant + index * scale. The address is first written as a sum of
    /// multiples: compilers build "array + 0x30 + i * 24" in steps such as (i + 2) * 3 * 8, and only the
    /// expanded form shows which element and which field that is.
    /// </summary>
    private AddressParts Decompose(Node address)
    {
        long offset = 0;
        var terms = new List<(Node Node, long Scale)>();
        void Term(Node n, long scale)
        {
            for (int i = 0; i < terms.Count; i++)
                if (ReferenceEquals(terms[i].Node, n))
                {
                    terms[i] = (n, terms[i].Scale + scale);
                    return;
                }
            terms.Add((n, scale));
        }

        var pending = new Stack<(Node Node, long Scale)>();
        pending.Push((address, 1));
        int budget = 96;
        while (pending.Count > 0)
        {
            var (n, k) = pending.Pop();
            if (n.IsConst)
            {
                offset += k * IrBuilder.SImm(n);
                continue;
            }
            // Multiples are followed inward only through full-width arithmetic: a 32-bit product wraps before
            // it is widened, so what is inside it does not distribute.
            bool wide = n.Type == VT.I64 && budget > 0;
            if (n.Op == Op.Add && budget-- > 0)
            {
                pending.Push((n.In[0], k));
                pending.Push((n.In[1], k));
            }
            else if (wide && n.Op == Op.Sub && n.In[1].IsConst)
            {
                pending.Push((n.In[0], k));
                offset -= k * IrBuilder.SImm(n.In[1]);
            }
            else if (n.Op == Op.Mul && n.In[1].IsConst)
            {
                if (wide) pending.Push((n.In[0], k * IrBuilder.SImm(n.In[1])));
                else Term(n.In[0], k * IrBuilder.SImm(n.In[1]));
            }
            else if (n.Op == Op.Shl && n.In[1].IsConst && n.In[1].UImm < 32)
            {
                if (wide) pending.Push((n.In[0], k << (int)n.In[1].UImm));
                else Term(n.In[0], k << (int)n.In[1].UImm);
            }
            else Term(n, k);
        }
        terms.RemoveAll(t => t.Scale == 0);

        Node? baseNode = null;
        Sem? baseSem = null;
        foreach (var (node, scale) in terms)
        {
            if (scale != 1) continue;
            Sem s = node.Op == Op.Phi && MergedObjKlass(node) is { } merged ? merged : Eval(node);
            if (!IsPointerLike(s) && !(s is SVal { Type: { } wrapper } && IsReferenceWrapper(wrapper))) continue;
            baseNode = node;
            baseSem = s;
            break;
        }
        Node? index = null;
        long indexScale = 0;
        foreach (var (node, scale) in terms)
        {
            if (ReferenceEquals(node, baseNode)) continue;
            if (index != null) return CombinedIndex(address, baseNode, baseSem, offset, terms); // more than one index term
            index = node;
            indexScale = scale;
        }
        return new AddressParts(baseNode, baseSem, offset, index, indexScale);
    }

    private static readonly bool NoCombinedIndex = Environment.GetEnvironmentVariable("REWIND_NO_COMBINED_INDEX") != null;
    private readonly Dictionary<Node, Node?> _combinedIndexes = [];

    /// <summary>
    /// An address with several terms besides its base: "grid + (row + col) * 4", which the expansion above takes
    /// apart, or an element reached from a pointer that is already part way into the array ("p = src + offset",
    /// then p[i]). One index stands for all of them: the terms in units of the largest step they share
    /// ("grid[row + col]", "src[offset + i]"). Whether that step is the element's size is for the caller to see.
    /// </summary>
    private AddressParts CombinedIndex(Node address, Node? baseNode, Sem? baseSem, long offset, List<(Node Node, long Scale)> terms)
    {
        var parts = new AddressParts(baseNode, baseSem, offset, null, -1);
        if (NoCombinedIndex || baseNode == null) return parts;
        var indexTerms = terms.Where(t => !ReferenceEquals(t.Node, baseNode)).ToList();
        // (Full-width terms only: what they add up to is then the same as the address computes.)
        if (indexTerms.Any(t => t.Node.Type != VT.I64)) return parts;
        long unit = 0;
        foreach (var (_, scale) in indexTerms) unit = Gcd(unit, Math.Abs(scale));
        if (unit is <= 0 or > 4096) return parts;
        if (!_combinedIndexes.TryGetValue(address, out Node? sum))
        {
            sum = null;
            foreach (var (node, scale) in indexTerms)
            {
                Node term = node;
                if (scale != unit)
                {
                    Node factor = _fn.NewNode(Op.Const, VT.I64, null);
                    factor.Imm = scale / unit;
                    term = _fn.NewNode(Op.Mul, VT.I64, null, node, factor);
                }
                sum = sum == null ? term : _fn.NewNode(Op.Add, VT.I64, null, sum, term);
            }
            _combinedIndexes[address] = sum;
        }
        return sum == null ? parts : new AddressParts(baseNode, baseSem, offset, sum, unit);
    }

    private static readonly bool NoMergedKlass = Environment.GetEnvironmentVariable("REWIND_NO_MERGED_KLASS") != null;

    /// <summary>
    /// The class of an object, merged from ways in that each read it: the compiler moves the read of the class
    /// pointer of a virtual call into the code before the point where several ways meet, and the call after it
    /// takes its method from the merged pointer. Where every way in read the class of the same object, it is
    /// that object's class; where each read the class of the object another merged value is given on the same
    /// way in (the receiver, merged alongside), it is the class of that merged value. Only ways in already
    /// translated are looked at; the merged value itself is not read (its copies go, see SettlePhis). Ways in
    /// that met before (a merge of such merges) count as one.
    /// </summary>
    private SObjKlass? MergedObjKlass(Node phi, int depth = 0)
    {
        if (NoMergedKlass || phi.Block == null || phi.In.Length < 2 || depth > 4) return null;
        var objects = new Node[phi.In.Length];
        for (int i = 0; i < phi.In.Length; i++)
        {
            Node input = phi.In[i];
            // (A way in that is itself such a merge: ways that met before this point.)
            SObjKlass? klass = input.Op == Op.Phi ? MergedObjKlass(input, depth + 1)
                : _sem.TryGetValue(input, out Sem? s) ? s as SObjKlass : null;
            if (klass == null) return null;
            objects[i] = klass.Object;
        }
        if (objects.All(o => ReferenceEquals(o, objects[0]))) return new SObjKlass(objects[0]);
        foreach (Node other in phi.Block.Phis)
        {
            if (ReferenceEquals(other, phi) || other.Dead || other.In.Length != objects.Length || other.Type != VT.I64) continue;
            bool same = true;
            for (int i = 0; i < objects.Length && same; i++) same = ReferenceEquals(other.In[i], objects[i]);
            if (same) return new SObjKlass(other);
        }
        return null;
    }

    private static long Gcd(long a, long b)
    {
        while (b != 0) (a, b) = (b, a % b);
        return a;
    }

    /// <summary>Follows struct fields inward until the accessed bytes line up with one field (or a pair).</summary>
    private static readonly bool NoReplicatedTypes = Environment.GetEnvironmentVariable("REWIND_NO_REPLICATED_TYPES") != null;

    private static bool IsReplicatedStorage(FieldDef f) =>
        f.Name == "Ptr" && f.DeclaringType is { Name: "NetworkBehaviour", Namespace: "Fusion", DeclaringType: null };

    /// <summary>
    /// A place in the replicated memory of a networked object, as (a part of) the property kept there - where
    /// the property is kept as it is: a struct of exactly its words, or a float. (A collection is built around
    /// its words and a yes/no is kept as a number; those stay plain memory.)
    /// </summary>
    private Place? ReplicatedPlace(HExpr storage, TypeSig pointerType, Rewind.Analysis.Runtime.ReplicatedLayout.Slot kept, int offset, int size)
    {
        TypeSig type = kept.Type;
        if (Open(type)) return null;
        bool isStruct = IsStructType(type), real = ReferenceEquals(type, _float);
        if (!isStruct && !real) return null;
        if (isStruct)
        {
            TypeLayout layout = _p.Layouts.Of(type);
            if (!layout.Known || layout.Size != kept.Size) return null;
        }
        else if (kept.Size != 4 || offset != kept.Offset || size != 4) return null;
        HExpr at = kept.Offset == 0 ? storage : new HBinary(HBinaryOp.Add, storage, new HConst(kept.Offset, _int)) { Type = pointerType };
        var whole = new HDeref(at) { Type = type };
        if (real || (offset == kept.Offset && (size < 0 || size == kept.Size))) return new PLocation(whole, type);
        if (size < 0) return null;
        return FieldPlace(whole, type, offset - kept.Offset, size);
    }

    private Place FieldPlace(HExpr owner, TypeSig ownerType, int offset, int size)
    {
        HExpr current = owner;
        TypeSig type = Declared(ownerType);
        int remaining = offset;
        for (int depth = 0; depth < 12; depth++)
        {
            FieldSlot? found = _p.Layouts.FieldAt(type, remaining);
            if (found is not { } slot)
            {
                // The bytes between a struct's fields hold nothing: writing them (the compiler zeroes or copies
                // them along with the fields) is no part of the program.
                if (size > 0 && IsPadding(type, remaining, size)) return new PInternal("padding");
                // Padding and then whole fields (a zeroing write that starts in the gap after a bool): the fields,
                // each taking its bytes of the value; the padding's bytes are nothing.
                var covered = new List<Part>();
                if (!NoPaddedParts && size > 0 && Leaves(current, type, remaining, size, 0, covered) && covered.Count != 0)
                    return new PParts(covered, size) { Owner = current, OwnerType = type, Offset = remaining };
                return new PUnknown($"no field at offset 0x{remaining:X} of {type.DisplayName}");
            }
            // A union: several fields share these bytes. The one of exactly this place and size is the one meant
            // (ULong0 for the first eight bytes of a v128, not Byte0 and its neighbours).
            if (size > 0 && !(slot.Offset == remaining && slot.Size == size) && _p.Layouts.FieldExactly(type, remaining, size) is { } exact)
                return new PLocation(new HField { Object = current, Field = exact.Field, DeclaringType = type, Type = exact.Type }, exact.Type);
            var field = new HField { Object = current, Field = slot.Field, DeclaringType = type, Type = slot.Type };
            int inner = remaining - slot.Offset;
            bool isStruct = slot.Type.Definition is { IsValueType: true, IsEnum: false } && slot.Type is not PrimitiveSig;
            if (inner == 0 && (size < 0 || size == slot.Size || !isStruct))
            {
                // Whole field, or a narrower read of a scalar field (the low bytes of an int, say).
                if (size > 0 && size > slot.Size && !isStruct)
                {
                    // The access runs past this field into the next one: two 4-byte fields read as 8 bytes.
                    FieldSlot? next = _p.Layouts.FieldAt(type, remaining + slot.Size);
                    if (size == 8 && slot.Size == 4 && next is { } ns && ns.Size == 4 && ns.Offset == slot.Offset + 4 && !IsStructType(ns.Type))
                        return new PPair(field, new HField { Object = current, Field = ns.Field, DeclaringType = type, Type = ns.Type });
                    return PartsPlace(current, type, remaining, size);
                }
                if (size > 0 && isStruct && size < slot.Size)
                {
                    // The first bytes of a larger struct: descend.
                }
                else return new PLocation(field, slot.Type);
            }
            // The access starts inside this field. A struct is entered when the bytes lie within it; otherwise
            // the access covers the tail of one field and more.
            if (isStruct && size > 0 && inner + size > slot.Size) return PartsPlace(current, type, remaining, size);
            if (!isStruct)
            {
                string why = $"offset 0x{remaining:X} is inside field {slot.Field.Name} of {type.DisplayName}";
                return IsStructType(type) && size > 0 ? new PChunk(current, type, remaining, size, why) : new PUnknown(why);
            }
            current = field;
            type = slot.Type;
            remaining = inner;
        }
        return new PUnknown("field nesting too deep");
    }

    /// <summary>
    /// True when [offset, offset + size) of a struct lies in the alignment gap between two of its fields (or
    /// after the last). Not for a struct whose size is set explicitly - there the bytes past the fields are
    /// data (a fixed buffer).
    /// </summary>
    private bool IsPadding(TypeSig type, int offset, int size)
    {
        if (!IsStructType(type) || Open(type)) return false;
        TypeLayout layout = _p.Layouts.Of(type);
        if (!layout.Known || layout.Fields.Length == 0 || offset < 0 || offset + size > layout.Size) return false;
        int align = Math.Max(1, layout.Align);
        if (layout.Size > (layout.DataSize + align - 1) / align * align) return false;
        int before = 0, after = layout.Size;
        foreach (FieldSlot slot in layout.Fields)
        {
            int end = slot.Offset + Math.Max(1, slot.Size);
            if (slot.Offset < offset + size && offset < end) return false;
            if (end <= offset) before = Math.Max(before, end);
            if (slot.Offset >= offset + size) after = Math.Min(after, slot.Offset);
        }
        return after - before < 8;
    }

    /// <summary>The fields a wide access covers, when it covers whole fields only.</summary>
    private readonly List<(HExpr Owner, HVar Variable, HBlock Block, int After)> _snapshots = [];

    private sealed class PendingCopy(HExpr destination, HVar snapshot, TypeSig type)
    {
        public HExpr Destination = destination;
        public HVar Snapshot = snapshot;
        public TypeSig Type = type;
        public List<(int Start, int End)> Ranges = [];
    }

    private readonly List<PendingCopy> _pendingCopies = [];

    /// <summary>
    /// A variable holding the struct at <paramref name="owner"/> as it is now: what pieces read from it mean, even
    /// if the struct changes before they are stored. Shared by reads with nothing in between that could change it.
    /// </summary>
    private HVar SnapshotOf(HExpr owner, TypeSig type, ulong address)
    {
        for (int i = _snapshots.Count - 1; i >= 0; i--)
        {
            var s = _snapshots[i];
            if (!ReferenceEquals(s.Block, _cur) || !HirCleanup.Same(s.Owner, owner)) continue;
            bool untouched = true;
            for (int k = s.After; k < _cur.Statements.Count && untouched; k++)
                untouched = _cur.Statements[k] is HAssign { Target: HLocal assigned, Value: var value } && IsPure(value) &&
                            !ConstructorFolding.Mentions(owner, assigned.Variable);
            if (untouched) return s.Variable;
            break;
        }
        HVar variable = _h.NewLocal(type, "s");
        Emit(new HAssign(new HLocal(variable) { Type = type }, owner), address);
        _snapshots.Add((owner, variable, _cur, _cur.Statements.Count));
        return variable;
    }

    /// <summary>
    /// One piece of a struct stored at the same place in a struct of the same type. Once the pieces cover the
    /// struct's data, the whole is one assignment; until then nothing is written (and what stays incomplete is
    /// reported).
    /// </summary>
    private void CopyChunk(PChunk destination, SChunk piece, ulong address)
    {
        PendingCopy? copy = _pendingCopies.FirstOrDefault(c => ReferenceEquals(c.Snapshot, piece.Snapshot) && HirCleanup.Same(c.Destination, destination.Owner));
        if (copy == null) _pendingCopies.Add(copy = new PendingCopy(destination.Owner, piece.Snapshot, piece.Type));
        copy.Ranges.Add((piece.Offset, piece.Offset + piece.Size));
        int covered = 0;
        foreach (var (start, end) in copy.Ranges.OrderBy(r => r.Start))
        {
            if (start > covered) break;
            covered = Math.Max(covered, end);
        }
        if (covered < _p.Layouts.Of(piece.Type).DataSize) return;
        Emit(new HAssign(destination.Owner, new HLocal(copy.Snapshot) { Type = piece.Type }), address);
        _pendingCopies.Remove(copy);
    }

    private Place PartsPlace(HExpr owner, TypeSig type, int offset, int size)
    {
        var leaves = new List<Part>();
        if (Leaves(owner, type, offset, size, 0, leaves) && leaves.Count != 0)
        {
            if (leaves.Count == 2 && size == 8 && leaves[0] is { Offset: 0, Size: 4 } && leaves[1] is { Offset: 4, Size: 4 })
                return new PPair(leaves[0].Value, leaves[1].Value);
            return new PParts(leaves, size) { Owner = owner, OwnerType = type, Offset = offset };
        }
        string why = $"access of {size} bytes spans fields of {type.DisplayName}";
        return IsStructType(type) && size > 0 ? new PChunk(owner, type, offset, size, why) : new PUnknown(why);
    }

    private static readonly bool NoScaledIndexes = Environment.GetEnvironmentVariable("REWIND_NO_SCALED_INDEXES") != null;
    private static readonly bool NoNarrowScalars = Environment.GetEnvironmentVariable("REWIND_NO_NARROW_SCALARS") != null;

    /// <summary>
    /// The index in elements of an array access whose scale is not the element size. A scale that is a multiple
    /// of it: "a[i * 6 + k]" of an int array, the 6 folded into the scale (24). A smaller scale: the index was
    /// multiplied already ("i * 12", or "i &lt;&lt; 4"), by enough to make whole elements. Null otherwise.
    /// </summary>
    private HExpr? ScaledIndex(Node index, long scale, long elementSize)
    {
        HExpr Times(HExpr e, long k) => k == 1 ? e : new HBinary(HBinaryOp.Mul, e, new HConst((int)k, _int)) { Type = _int };
        if (scale > elementSize && scale % elementSize == 0)
            return Times(IntValue(StripExtension(index)), scale / elementSize);
        if (scale < elementSize && Multiple(StripExtension(index)) is ({ } x, var factor) && factor > 0 && factor * scale % elementSize == 0)
            return Times(IntValue(StripExtension(x)), factor * scale / elementSize);
        // An index the compiler keeps already multiplied (a loop counter stepping by 3 for 12-byte elements,
        // an offset stepping by the element size): always a multiple of what it is missing, so the element
        // index is that exact quotient.
        if (scale > 0 && scale < elementSize && !NoProvenMultiples)
        {
            long g = Gcd(scale, elementSize), missing = elementSize / g;
            if (missing > 1 && missing < 1 << 20 && AlwaysMultiple(index, missing, [], 0))
            {
                var quotient = new HBinary(HBinaryOp.Div, IntValue(StripExtension(index)), new HConst((int)missing, _int)) { Type = _int };
                return Times(quotient, scale / g);
            }
        }
        return null;
    }

    private static readonly bool NoProvenMultiples = Environment.GetEnvironmentVariable("REWIND_NO_PROVEN_MULTIPLES") != null;
    private static readonly bool NoFixedBuffers = Environment.GetEnvironmentVariable("REWIND_NO_FIXED_BUFFERS") != null;

    /// <summary>The element of a fixed-size buffer ("fixed ulong bits[64]": a struct of the compiler's with one field, FixedElementField).</summary>
    private bool IsFixedBuffer(TypeSig type, out FieldSlot element)
    {
        element = default;
        if (type.Definition is not { IsValueType: true } definition || !definition.Name.Contains("e__FixedBuffer", StringComparison.Ordinal)) return false;
        TypeLayout layout = _p.Layouts.Of(type);
        if (!layout.Known || layout.Fields.Length != 1 || layout.Fields[0].Field.Name != "FixedElementField" || layout.Fields[0].Offset != 0) return false;
        element = layout.Fields[0];
        return element.Size > 0;
    }

    /// <summary>
    /// An element of a fixed-size buffer inside the struct a reference refers to, reached by index: the
    /// address of the buffer's first element plus the index times the element size, as C# indexes such a
    /// buffer ("bits[i]", which needs no pinning since C# 7.3).
    /// </summary>
    private Place? FixedBufferPlace(HExpr owner, TypeSig type, AddressParts a, int size)
    {
        long offset = a.Offset;
        HExpr at = owner;
        for (int depth = 0; depth < 6; depth++)
        {
            if (!IsStructType(type) || offset < 0 || _p.Layouts.FieldAt(type, (int)offset) is not { } slot) return null;
            var field = new HField { Object = at, Field = slot.Field, DeclaringType = type, Type = slot.Type };
            if (IsFixedBuffer(slot.Type, out FieldSlot element))
            {
                int elementSize = element.Size;
                long inside = offset - slot.Offset;
                if (inside % elementSize != 0 || (size > 0 && size != elementSize) || IsStructType(element.Type)) return null;
                HExpr? index = a.Scale == elementSize ? IntValue(StripExtension(a.Index!)) : ScaledIndex(a.Index!, a.Scale, elementSize);
                if (index == null) return null;
                if (inside != 0) index = new HBinary(HBinaryOp.Add, index, new HConst((int)(inside / elementSize), _int)) { Type = _int };
                // (A reference to the first element moved on by the offset: what C# makes of "bits[i]".)
                TypeSig pointerType = _m.Sigs.ByRef(element.Type);
                var first = new HField { Object = field, Field = element.Field, DeclaringType = slot.Type, Type = element.Type };
                // (The offset as a native integer, as pointer arithmetic takes it: "(nint)i * 8".)
                HExpr wide = new HConv(HConvKind.I, index) { Type = _nint };
                HExpr bytes = elementSize == 1 ? wide : new HBinary(HBinaryOp.Mul, wide, new HConst(elementSize, _int)) { Type = _nint };
                var pointer = new HBinary(HBinaryOp.Add, new HAddressOf(first) { Type = pointerType }, bytes) { Type = pointerType };
                return new PLocation(new HDeref(pointer) { Type = element.Type }, element.Type);
            }
            if (!IsStructType(slot.Type)) return null;
            at = field;
            type = slot.Type;
            offset -= slot.Offset;
        }
        return null;
    }

    /// <summary>
    /// Whether <paramref name="n"/> is a multiple of <paramref name="k"/> however it is reached: constants,
    /// products and shifts with a multiple, sums and differences of multiples, and selects and phis of them (a
    /// phi met again on its own cycle is taken to be one; every way into the cycle must then show it).
    /// </summary>
    private static bool AlwaysMultiple(Node n, long k, HashSet<Node> assumed, int depth)
    {
        if (depth > 24) return false;
        if (n.IsConst) return IrBuilder.SImm(n) % k == 0;
        if (Multiple(n) is ({ } of, var factor) && factor != 0 && (factor % k == 0 || AlwaysMultiple(of, k / Gcd(k, factor), assumed, depth + 1)))
            return true;
        switch (n.Op)
        {
            case Op.ZExt or Op.SExt or Op.Neg:
                return AlwaysMultiple(n.In[0], k, assumed, depth + 1);
            case Op.Add or Op.Sub:
                return AlwaysMultiple(n.In[0], k, assumed, depth + 1) && AlwaysMultiple(n.In[1], k, assumed, depth + 1);
            case Op.Mul:
                return AlwaysMultiple(n.In[0], k, assumed, depth + 1) || AlwaysMultiple(n.In[1], k, assumed, depth + 1);
            case Op.Select:
                return AlwaysMultiple(n.In[1], k, assumed, depth + 1) && AlwaysMultiple(n.In[2], k, assumed, depth + 1);
            case Op.Phi:
            {
                if (assumed.Contains(n)) return true;
                // (What is shown while this phi is assumed rests on it: if it fails, so does all of that.)
                var before = new HashSet<Node>(assumed);
                assumed.Add(n);
                foreach (Node input in n.In)
                    if (!AlwaysMultiple(input, k, assumed, depth + 1))
                    {
                        assumed.IntersectWith(before);
                        return false;
                    }
                return true;
            }
            default:
                return false;
        }
    }

    /// <summary>
    /// A value that is another times a constant: "x * c", "x &lt;&lt; s", and the sums "lea" makes of them
    /// ("x + x * 2" is x * 3).
    /// </summary>
    private static (Node? Of, long Factor) Multiple(Node n)
    {
        static (Node?, long) Simple(Node m) =>
            m.Op == Op.Mul && m.In[1].IsConst ? (m.In[0], IrBuilder.SImm(m.In[1]))
            : m.Op == Op.Shl && m.In[1].IsConst && m.In[1].Imm < 31 ? (m.In[0], 1L << (int)m.In[1].Imm)
            : (null, 0);
        if (Simple(n) is ({ } x, var k)) return (x, k);
        if (n.Op == Op.Add)
        {
            if (ReferenceEquals(n.In[0], n.In[1])) return (n.In[0], 2);
            for (int side = 0; side < 2; side++)
                if (Simple(n.In[side]) is ({ } y, var c) && ReferenceEquals(y, n.In[1 - side])) return (y, c + 1);
        }
        return (null, 0);
    }

    private HExpr IndexValue(Node index, long constant)
    {
        HExpr e = IntValue(StripExtension(index));
        if (constant == 0) return e;
        return new HBinary(HBinaryOp.Add, e, new HConst((int)constant, _int)) { Type = _int };
    }

    /// <summary>An index that takes one of two constant values: a conditional move of two constants, or a condition used as 0 or 1.</summary>
    private static (Node Condition, long WhenTrue, long WhenFalse)? TwoWay(Node index)
    {
        Node n = StripExtension(index);
        if (n.Op == Op.Select && n.In[1].IsConst && n.In[2].IsConst) return (n.In[0], IrBuilder.SImm(n.In[1]), IrBuilder.SImm(n.In[2]));
        if (n.Type == VT.I1) return (n, 1, 0);
        return null;
    }

    private Place ResolvePlace(Node address, int size)
    {
        AddressParts a = Decompose(address);
        if (a.Scale < 0) return new PUnknown("address with several index terms");
        Place place = ResolveParts(a, size);
        // A field that the common type of a merged object does not have: the code for two classes was merged
        // because their fields sit at the same offset. Giving the merge back to each way in separates them.
        if (place is PUnknown { Why: var why } && why.StartsWith("no field at offset", StringComparison.Ordinal) && a.Base is { Op: Op.Phi } mergedBase &&
            a.BaseSem is SVal { Type: { } joined } && IsReference(joined))
            MergedObjects.Add(mergedBase);
        // "(left ? this.a : this.b)": the compiler reads or writes one field at an offset it selects. Each way is
        // a place of its own; the access goes to whichever the condition picks.
        if (place is PUnknown && a.Base != null && a.Index != null && a.Scale > 0 && TwoWay(a.Index) is { } choice &&
            ResolveParts(a with { Offset = a.Offset + a.Scale * choice.WhenTrue, Index = null, Scale = 0 }, size) is PLocation whenTrue &&
            ResolveParts(a with { Offset = a.Offset + a.Scale * choice.WhenFalse, Index = null, Scale = 0 }, size) is PLocation whenFalse &&
            whenTrue.Type.Key == whenFalse.Type.Key && !Open(whenTrue.Type))
        {
            TypeSig reference = _m.Sigs.ByRef(whenTrue.Type);
            var pick = new HSelect(Condition(choice.Condition), new HAddressOf(whenTrue.Location) { Type = reference },
                new HAddressOf(whenFalse.Location) { Type = reference }) { Type = reference };
            return new PLocation(new HDeref(pick) { Type = whenTrue.Type }, whenTrue.Type);
        }
        return place;
    }

    private static readonly bool NoConstrainedDescriptors = Environment.GetEnvironmentVariable("REWIND_NO_CONSTRAINED_DESCRIPTORS") != null;

    /// <summary>What entry <paramref name="index"/> of a runtime generic context holds, for the context's type arguments.</summary>
    private Sem RgctxValue(SRgctx context, int index)
    {
        if (index < 0 || index >= context.Items.Count) return SJunk.Instance;
        Rewind.Runtime.RgctxItem item = context.Items[index];
        TypeSig? Inflate(TypeSig? open)
        {
            if (open == null) return null;
            TypeSig closed = _m.Sigs.Substitute(open, context.ClassArguments, context.MethodArguments);
            return Open(closed) ? null : closed;
        }
        switch (item.Kind)
        {
            case Rewind.Runtime.RgctxKind.Class when Inflate(item.Type) is { } type:
                return new SKlass(type);
            case Rewind.Runtime.RgctxKind.Type when Inflate(item.Type) is { } type:
                return new SType(type);
            case Rewind.Runtime.RgctxKind.Array when Inflate(item.Type) is { } element:
                return new SKlass(_m.Sigs.SzArray(element));
            case Rewind.Runtime.RgctxKind.Constrained when !NoConstrainedDescriptors && Inflate(item.Type) is { } on:
                return new SConstrained(on);
            case Rewind.Runtime.RgctxKind.Method when item.Method is { } open:
            {
                var classArguments = new TypeSig[open.ClassArguments.Length];
                var methodArguments = new TypeSig[open.MethodArguments.Length];
                for (int i = 0; i < classArguments.Length; i++)
                {
                    if (Inflate(open.ClassArguments[i]) is not { } closed) return SJunk.Instance;
                    classArguments[i] = closed;
                }
                for (int i = 0; i < methodArguments.Length; i++)
                {
                    if (Inflate(open.MethodArguments[i]) is not { } closed) return SJunk.Instance;
                    methodArguments[i] = closed;
                }
                return new SMethod(open.Method, new MethodInst { SpecIndex = -1, Method = open.Method, ClassArguments = classArguments, MethodArguments = methodArguments });
            }
            default:
                return SJunk.Instance;
        }
    }

    private static readonly bool NoAddressConflicts = Environment.GetEnvironmentVariable("REWIND_NO_ADDRESS_CONFLICTS") != null;

    private Place ResolveParts(AddressParts a, int size)
    {
        if (a.Base == null)
        {
            if (a.Index == null) return new PUnknown($"absolute address 0x{a.Offset:X}");
            // What was read from the stack is used as an address, and what the stack is known to hold there is
            // no reference (two floats, a number of no known type): the compiler kept two variables in the
            // slot, one after the other, and this one is read as the other. Their lifetimes are told apart for
            // the next build (see StackSplitting).
            if (a.Scale == 1 && a.Index.Op == Op.Load && a.Index.Type == VT.I64 && !NoAddressConflicts &&
                IsFrameAddress(a.Index.In[0], out int reused))
                FrameConflicts.Add(FrameObjectAt(reused) ?? reused);
            return new PUnknown("address without a typed base");
        }

        switch (a.BaseSem)
        {
            case SVal v:
                return ValuePlace(a, v, size);
            case SNewObject o:
                return ValuePlace(a, new SVal(new HLocal(o.Variable) { Type = o.Type }), size);
            case SRef r:
            {
                if (a.Index != null)
                    return !NoFixedBuffers && FixedBufferPlace(r.Location, r.Type, a, size) is { } element ? element
                        : new PUnknown("indexed access through a reference");
                var (refSize, _, _) = _p.Layouts.SizeOf(r.Type);
                bool isStruct = r.Type.Definition is { IsValueType: true, IsEnum: false } && r.Type is not PrimitiveSig;
                if (a.Offset == 0 && (!isStruct || size < 0 || size == refSize)) return new PLocation(r.Location, r.Type);
                if (isStruct) return FieldPlace(r.Location, r.Type, (int)a.Offset, size);
                return new PUnknown($"offset 0x{a.Offset:X} into a {r.Type.DisplayName}");
            }
            case SKlass k:
                if (a.Index == null && a.Offset == _p.Klass.StaticFields) return new PStatics(k.Type);
                if (a.Index == null && a.Offset == _p.Klass.RgctxData && k.Type is GenericInstSig { Definition: { } generic } instance)
                    return new PRgctx(new SRgctx(_m.RgctxOf(generic.Assembly.ImageName, generic.Token), instance.Arguments, []));
                return new PInternal("class data");
            case SMethod method when a.Index == null:
            {
                // A method's runtime record: its code (methodPointer, and from metadata 29 virtualMethodPointer, which
                // is what il2cpp_codegen_get_method_pointer hands out there), its class, and for an instantiated
                // generic method its own context.
                bool twoPointers = _m.Version >= Rewind.Metadata.MetaVersion.V29_0;
                int klassAt = (twoPointers ? 4 : 3) * _ptr;
                TypeSig[] classArguments = method.Inst?.ClassArguments ?? [];
                if (size == _ptr && (a.Offset == 0 || (twoPointers && a.Offset == _ptr))) return new PMethodCode(method);
                if (a.Offset == klassAt)
                    return new PKlassOf(classArguments.Length != 0 ? _m.Sigs.GenericInst(method.Method.DeclaringType, classArguments) : method.Method.DeclaringType.Sig);
                if (a.Offset == klassAt + 3 * _ptr && method.Inst is { MethodArguments.Length: > 0 } inst)
                    return new PRgctx(new SRgctx(_m.RgctxOf(method.Method.DeclaringType.Assembly.ImageName, method.Method.Token), inst.ClassArguments, inst.MethodArguments));
                return new PInternal("method data");
            }
            case SRgctx context when a.Index == null && a.Offset >= 0 && a.Offset % _ptr == 0:
                return new PRgctxItem(context, (int)(a.Offset / _ptr));
            case SObjKlass ok:
            {
                long rel = a.Offset - _p.Klass.VTable;
                if (a.Index == null && rel >= 0 && rel % _ptr == 0)
                {
                    int slot = (int)(rel / _p.Klass.VTableEntrySize);
                    return new PVTable(ok.Object, slot, rel % _p.Klass.VTableEntrySize != 0);
                }
                return new PInternal("class data");
            }
            case SStatics st:
            {
                if (a.Index != null) return new PUnknown("indexed static access");
                foreach (FieldSlot kept in _p.Layouts.Statics(st.Type))
                {
                    TypeSig ft = kept.Type;
                    int fs = kept.Size;
                    if (a.Offset < kept.Offset || a.Offset >= kept.Offset + Math.Max(1, fs)) continue;
                    var field = new HField { Object = null, Field = kept.Field, DeclaringType = st.Type, Type = ft };
                    if (a.Offset == kept.Offset && (size < 0 || size == fs || !(ft.Definition is { IsValueType: true, IsEnum: false } && ft is not PrimitiveSig)))
                        return new PLocation(field, ft);
                    return FieldPlace(field, ft, (int)(a.Offset - kept.Offset), size);
                }
                return new PUnknown($"no static field at offset 0x{a.Offset:X} of {st.Type.DisplayName}");
            }
            case SUnboxed u:
                return new PUnboxed(u.Object, (int)a.Offset);
            case SFrame f:
                if (a.Index != null) return new PUnknown("indexed stack access");
                return FramePlace(f.Offset + (int)a.Offset, size);
            default:
                return new PUnknown("unsupported base");
        }
    }

    /// <summary>
    /// A struct that is nothing but one object reference (possibly wrapped again): in a register it is that
    /// reference, and code uses it as one.
    /// </summary>
    private bool IsReferenceWrapper(TypeSig type)
    {
        for (int depth = 0; depth < 4; depth++)
        {
            if (type.Definition is not { IsValueType: true, IsEnum: false } definition || type is PrimitiveSig) return false;
            if (_p.Layouts.SizeOf(type).Size != _ptr || definition.Fields.Count(f => !f.IsStatic) != 1) return false;
            if (_p.Layouts.FieldAt(type, 0) is not { Offset: 0 } only || only.Size != _ptr) return false;
            if (IsReference(only.Type)) return true;
            type = only.Type;
        }
        return false;
    }

    private Place ValuePlace(AddressParts a, SVal v, int size)
    {
        HExpr e = v.Expr;
        TypeSig? type = e.Type;
        if (_castTypes.TryGetValue(a.Base!, out List<TypeSig>? casts) && casts.Count == 1 && IsReference(casts[0]))
        {
            // A checked cast guards this use: view the object as the cast type.
            e = new HTypeExpr(HTypeOp.CastClass, casts[0], e) { Type = casts[0] };
            type = casts[0];
        }
        if (type == null) return new PUnknown("base value has no known type");

        // A struct that is nothing but one object reference travels in a register as that reference: used as an
        // address, it is the reference (a builder struct wrapping the object it configures, say).
        for (int depth = 0; depth < 4 && IsReferenceWrapper(type) && _p.Layouts.FieldAt(type, 0) is { } only; depth++)
        {
            e = new HField { Object = e, Field = only.Field, DeclaringType = type, Type = only.Type };
            type = only.Type;
        }

        switch (type)
        {
            case SzArraySig array:
            {
                if (a.Index == null && a.Offset == 0) return new PObjKlass(a.Base!);
                int lengthOffset = _header + _ptr;      // { klass, monitor, bounds, max_length, elements... }
                int dataOffset = lengthOffset + _ptr;
                if (a.Index == null && a.Offset == lengthOffset) return new PArrayLength(e);
                var (elementSize, _, known) = _p.Layouts.SizeOf(array.ElementType);
                if (!known || elementSize <= 0) return new PUnknown("array element size unknown");
                if (a.Index == null && a.Offset < dataOffset) return new PInternal("array header");
                long rel = a.Offset - dataOffset;
                HExpr index;
                long inside;
                if (a.Index != null)
                {
                    HExpr? scaled = null;
                    if (a.Scale != elementSize && (NoScaledIndexes || (scaled = ScaledIndex(a.Index, a.Scale, elementSize)) == null))
                        return new PUnknown($"array index scale {a.Scale} does not match element size {elementSize}");
                    // "array[i - 1]" has a displacement below the first element: round toward the element it is in.
                    long whole = Math.DivRem(rel, elementSize, out inside);
                    if (inside < 0)
                    {
                        inside += elementSize;
                        whole--;
                    }
                    index = scaled == null ? IndexValue(a.Index, whole)
                        : whole == 0 ? scaled
                        : new HBinary(HBinaryOp.Add, scaled, new HConst((int)whole, _int)) { Type = _int };
                }
                else
                {
                    index = new HConst((int)(rel / elementSize), _int);
                    inside = rel % elementSize;
                }
                var element = new HElement { Array = e, Index = index, Type = array.ElementType };
                bool isStruct = array.ElementType.Definition is { IsValueType: true, IsEnum: false } && array.ElementType is not PrimitiveSig;
                if (inside == 0 && (!isStruct || size < 0 || size == elementSize)) return new PLocation(element, array.ElementType);
                if (isStruct) return FieldPlace(element, array.ElementType, (int)inside, size);
                return new PUnknown("partial array element access");
            }
            case PointerSig pointer:
            {
                // The replicated memory of a networked object: what lies at an offset is the property that
                // was given those words.
                if (!NoReplicatedTypes && a.Index == null)
                {
                    // (The address is read once and kept while nothing can change it: what was read then says
                    // whose memory it is.)
                    HExpr? read = e is HField ? e
                        : e is HLocal && a.Base is { Op: Op.Load } held && ResolvePlace(held.In[0], held.Type.Bytes()) is PLocation { Location: HField through } ? through
                        : null;
                    if (read is HField { Object: { } networked } storage && IsReplicatedStorage(storage.Field) &&
                        _p.Replicated.At(networked.Type?.Definition ?? (networked is HArg { Index: < 0 } ? _method.DeclaringType : null), a.Offset) is { } kept &&
                        ReplicatedPlace(e, type, kept, (int)a.Offset, size) is { } typed)
                        return typed;
                }
                HExpr p = e;
                if (a.Index != null)
                {
                    HExpr scaled = IntValue(StripExtension(a.Index));
                    if (a.Scale != 1) scaled = new HBinary(HBinaryOp.Mul, scaled, new HConst((int)a.Scale, _int)) { Type = _int };
                    p = new HBinary(HBinaryOp.Add, p, scaled) { Type = type };
                }
                if (a.Offset != 0) p = new HBinary(HBinaryOp.Add, p, new HConst((int)a.Offset, _int)) { Type = type };
                TypeSig pointee = pointer.ElementType.IsVoid ? TypeForBits(VTExtensions.IntOfBytes(Math.Max(1, Math.Min(8, size < 0 ? 8 : size)))) : pointer.ElementType;
                // As many bytes as are read or written, whatever the pointer says it points at: eight bytes
                // through an "int*" are two of its ints, not one.
                if (!NoReplicatedTypes && size is 1 or 2 or 4 or 8 && pointee is PrimitiveSig && _p.Layouts.SizeOf(pointee) is { Known: true, Size: > 0 } own && own.Size != size &&
                    !IsFloat(pointee))
                    pointee = TypeForBits(VTExtensions.IntOfBytes(size));
                return new PLocation(new HDeref(p) { Type = pointee }, pointee);
            }
            case ByRefSig byRef:
            {
                var target = new HDeref(e) { Type = byRef.ElementType };
                bool isStruct = byRef.ElementType.Definition is { IsValueType: true, IsEnum: false } && byRef.ElementType is not PrimitiveSig;
                if (a.Index == null && a.Offset == 0 && !isStruct) return new PLocation(target, byRef.ElementType);
                if (a.Index == null && isStruct) return FieldPlace(target, byRef.ElementType, (int)a.Offset, size);
                return new PUnknown("indexed access through a ref");
            }
        }

        if (IsReference(type))
        {
            if (a.Index != null && a.Scale > 0 && !NoChosenFields && ChosenField(e, type, a, size) is { } chosen) return chosen;
            if (a.Index != null && !NoStringChars && StringChar(e, type, a, size) is { } character) return character;
            if (a.Index != null) return new PUnknown($"indexed access into {type.DisplayName}");
            if (a.Offset == 0) return new PObjKlass(a.Base!);
            Place direct = FieldPlace(e, type, (int)a.Offset, size);
            // Not a field of the static type: a type test on the way here may have shown the object to be more.
            if (direct is PUnknown && TestedType(a.Base!) is { } tested && !ReferenceEquals(tested, type) && IsReference(tested))
            {
                var cast = new HTypeExpr(HTypeOp.CastClass, tested, e) { Type = tested };
                Place refined = FieldPlace(cast, tested, (int)a.Offset, size);
                if (refined is not PUnknown) return refined;
            }
            return direct;
        }
        return new PUnknown($"memory access through a {type.DisplayName} value");
    }

    // ---- loads and stores --------------------------------------------------------------------------------------

    /// <summary>Reads of the parts of a class description that type tests use.</summary>
    private Sem? ClassDataLoad(Node n)
    {
        AddressParts a = Decompose(n.In[0]);
        if (a.Base == null || a.Scale < 0) return null;
        switch (a.BaseSem)
        {
            case SInterfaceEntry e when a.Index == null && a.Offset is 0 or 8 && (a.Offset == 0 || a.Offset == _ptr):
                return new SVTable(e.Object, e.Slot, a.Offset != 0) { Interface = e.Interface };
            case SKlass k when a.Index == null && a.Offset == _p.Klass.TypeHierarchyDepth:
                return new SDepth(k.Type, null);
            case SObjKlass o when a.Index == null && a.Offset == _p.Klass.TypeHierarchyDepth:
                return new SDepth(null, o.Object);
            case SObjKlass o when a.Index == null && a.Offset == _p.Klass.TypeHierarchy:
                return new SHierarchy(o.Object);
            case SHierarchy h when a.Index != null && a.Scale == _ptr && a.Offset == -_ptr && Eval(StripExtension(a.Index)) is SDepth { Type: { } type }:
                return new SHierarchyEntry(h.Object, type);
        }
        return null;
    }

    private HExpr InstanceTest(Node obj, TypeSig type, bool wanted)
    {
        var test = new HTypeExpr(HTypeOp.IsInst, type, Value(obj)) { Type = type };
        return new HCompare(wanted ? HCompareOp.Ne : HCompareOp.Eq, test, new HConst(null, type)) { Type = _bool };
    }

    /// <summary>
    /// A class that nothing can derive from is tested by comparing class pointers; for any other class the
    /// comparison means "exactly this class", which "is" does not express.
    /// </summary>
    private bool ExactClassIsInstance(TypeSig type)
    {
        if (type is SzArraySig or ArraySig || type.IsValueType) return true;
        if (type.Definition is { } definition && (definition.IsSealed || definition.IsValueType)) return true;
        Problem($"exact class comparison with {type.ShortName}, which can be derived from");
        return true;
    }

    private static readonly bool NoUnboxedWords = Environment.GetEnvironmentVariable("REWIND_NO_UNBOXED_WORDS") != null;

    /// <summary>
    /// The value type an object is known to be a boxed instance of where <paramref name="at"/> runs: an exact
    /// class comparison of the object (class of obj == T) on the way in, its "same" edge the only way to
    /// <paramref name="at"/>. Clang drops the class check of an unbox that such a test already settled.
    /// </summary>
    private TypeSig? ProvenClass(Node obj, Block at)
    {
        if (_cfg == null || !_cfg.IsReachable(at)) return null;
        Block child = at;
        for (int guard = 0; guard < 64 && _cfg.ImmediateDominator(child) is { } p && !ReferenceEquals(p, child); guard++, child = p)
        {
            if (p.Terminator is not { Op: Op.Branch } branch || p.Succs.Count != 2 || ReferenceEquals(p.Succs[0], p.Succs[1])) continue;
            Node c = branch.In[0];
            if (c.Op is not (Op.CmpEq or Op.CmpNe)) continue;
            Block same = p.Succs[c.Op == Op.CmpEq ? 0 : 1];
            if (same.Preds.Count != 1 || !_cfg.Dominates(same, at)) continue;
            Sem a = Eval(c.In[0]), b = Eval(c.In[1]);
            TypeSig? type = (a, b) switch
            {
                (SObjKlass oa, SKlass kb) when ReferenceEquals(oa.Object, obj) => kb.Type,
                (SKlass ka, SObjKlass ob) when ReferenceEquals(ob.Object, obj) => ka.Type,
                _ => null,
            };
            if (type is { IsValueType: true }) return type;
        }
        return null;
    }

    /// <summary>The comparisons generated code uses to ask whether an object is an instance of a type.</summary>
    private Sem? TypeTestCompare(Node n)
    {
        Sem a = Eval(n.In[0]), b = Eval(n.In[1]);
        if (n.Op is Op.CmpEq or Op.CmpNe)
        {
            bool equal = n.Op == Op.CmpEq;
            if (a is SObjKlass oa && b is SKlass kb && ExactClassIsInstance(kb.Type)) return new SVal(InstanceTest(oa.Object, kb.Type, equal));
            if (b is SObjKlass ob && a is SKlass ka && ExactClassIsInstance(ka.Type)) return new SVal(InstanceTest(ob.Object, ka.Type, equal));
            if (a is SHierarchyEntry ea && b is SKlass kc && ReferenceEquals(ea.Type, kc.Type)) return new SVal(InstanceTest(ea.Object, ea.Type, equal));
            if (b is SHierarchyEntry eb && a is SKlass kd && ReferenceEquals(eb.Type, kd.Type)) return new SVal(InstanceTest(eb.Object, eb.Type, equal));
        }
        // "depth(object) < depth(T)" rules an instance out. "depth(T) <= depth(object)" does not settle it, but
        // the test that follows on that path is the base class comparison, which is this same question.
        if (a is SDepth da && b is SDepth db)
        {
            if (n.Op == Op.CmpLtU && da.Object != null && db.Type != null) return new SVal(InstanceTest(da.Object, db.Type, false));
            if (n.Op == Op.CmpLeU && da.Type != null && db.Object != null) return new SVal(InstanceTest(db.Object, da.Type, true));
        }
        return null;
    }

    /// <summary>"(class of obj == T) ? obj : null": the value form of the same test.</summary>
    private Sem? TypeTestSelect(Node n)
    {
        Node condition = n.In[0];
        if (condition.Op is not (Op.CmpEq or Op.CmpNe)) return null;
        var (whenSame, whenOther) = condition.Op == Op.CmpEq ? (n.In[1], n.In[2]) : (n.In[2], n.In[1]);
        if (!whenOther.IsConstValue(0)) return null;
        Sem a = Eval(condition.In[0]), b = Eval(condition.In[1]);
        Node? obj = null;
        TypeSig? type = null;
        if (a is SObjKlass oa && b is SKlass kb) (obj, type) = (oa.Object, kb.Type);
        else if (b is SObjKlass ob && a is SKlass ka) (obj, type) = (ob.Object, ka.Type);
        else if (a is SHierarchyEntry ea && b is SKlass kc && ReferenceEquals(ea.Type, kc.Type)) (obj, type) = (ea.Object, ea.Type);
        else if (b is SHierarchyEntry eb && a is SKlass kd && ReferenceEquals(eb.Type, kd.Type)) (obj, type) = (eb.Object, eb.Type);
        if (obj == null || type == null || !ReferenceEquals(obj, whenSame)) return null;
        if (a is SObjKlass || b is SObjKlass) ExactClassIsInstance(type);
        return new SVal(new HTypeExpr(HTypeOp.IsInst, type, Value(obj)) { Type = type });
    }

    private static readonly bool NoBoxedTests = Environment.GetEnvironmentVariable("REWIND_NO_BOXED_TESTS") != null;
    private static readonly bool NoFlaggedCasts = Environment.GetEnvironmentVariable("REWIND_NO_FLAGGED_CASTS") != null;
    private static readonly bool NoStructPieces = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_PIECES") != null;
    private static readonly bool NoStructTops = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_TOPS") != null;
    private static readonly bool FlaggedTrace = Environment.GetEnvironmentVariable("REWIND_FLAGGED_TRACE") != null;

    /// <summary>
    /// "flag != 0 ? obj : null" where the flag is 1 on the one way out of the test that obj is a T and 0 on the
    /// other ways (the compiler kept the answer as a number and picked afterwards): the same "obj as T".
    /// </summary>
    private Sem? FlaggedTypeTestSelect(Node n)
    {
        if (NoFlaggedCasts || n.In.Length != 3) return null;
        Node condition = n.In[0];
        if (condition.Op is not (Op.CmpEq or Op.CmpNe) || !condition.In[1].IsConstValue(0)) return null;
        Node flag = condition.In[0];
        static Node Plain(Node x)
        {
            while (x.Op is Op.Trunc or Op.ZExt or Op.SExt && x.In.Length == 1) x = x.In[0];
            return x;
        }
        var (whenSet, whenClear) = condition.Op == Op.CmpNe ? (n.In[1], n.In[2]) : (n.In[2], n.In[1]);
        if (!whenClear.IsConstValue(0)) return null;
        if (flag.Op != Op.Select) flag = Plain(flag);
        // The answer kept as the cast itself: "(obj as T) != null ? obj : null".
        if (flag.Op == Op.Select && flag.In.Length == 3 && TypeTestSelect(flag) is SVal { Expr: HTypeExpr { Op: HTypeOp.IsInst } } again &&
            ReferenceEquals(flag.In[0].Op == Op.CmpEq ? flag.In[1] : flag.In[2], whenSet))
            return again;
        Sem? Not(string why)
        {
            if (FlaggedTrace) Console.Error.WriteLine($"[flagged] {n} in {n.Block}: {why}");
            return null;
        }
        // The answer of the test itself, as a number: "sete al" into a cleared register - (0 & ~0xFF) | answer.
        {
            static bool NoBits(Node x) => x.IsConstValue(0) || (x.Op == Op.And && x.In.Length == 2 && (x.In[0].IsConstValue(0) || x.In[1].IsConstValue(0)));
            Node answer = flag;
            for (int depth = 0; depth < 4; depth++)
            {
                answer = Plain(answer);
                if (answer.Op != Op.Or || answer.In.Length != 2) break;
                if (NoBits(answer.In[0])) answer = answer.In[1];
                else if (NoBits(answer.In[1])) answer = answer.In[0];
                else break;
            }
            if (answer.Op is Op.CmpEq or Op.CmpNe && InstanceTestOf(answer) is var (whose, of, isOne) && isOne && ReferenceEquals(whose, whenSet))
                return new SVal(new HTypeExpr(HTypeOp.IsInst, of, Value(whose)) { Type = of });
        }
        if (flag.Op != Op.Phi || flag.Block is not { } join) return Not($"the condition is on {flag} ({flag.Op}), not a merged number");
        if (flag.In.Length != join.Preds.Count || join.Preds.Count is < 2 or > 4) return Not($"{join.Preds.Count} ways into {join}, {flag.In.Length} values");
        // A 0, also one kept in a register around a loop (a merged value that is 0 or itself on every way in).
        static bool Zero(Node x, HashSet<Node> seen)
        {
            x = Plain(x);
            if (x.IsConstValue(0)) return true;
            if (x.Op != Op.Phi || seen.Count > 16) return false;
            if (!seen.Add(x)) return true;
            foreach (Node way in x.In)
                if (!Zero(way, seen))
                    return false;
            return x.In.Length != 0;
        }
        // One way in sets the flag, the others clear it.
        int set = -1;
        for (int i = 0; i < flag.In.Length; i++)
        {
            if (Plain(flag.In[i]).IsConstValue(1))
            {
                if (set >= 0) return Not("two ways set the flag");
                set = i;
            }
            else if (!Zero(flag.In[i], []))
                return Not($"value {flag.In[i]} ({flag.In[i].Op} of {Plain(flag.In[i]).Op} {Plain(flag.In[i]).Imm}: {string.Join(",", Plain(flag.In[i]).In.Select(x => x.Op + " " + x.Imm))}) is neither 1 nor 0");
        }
        if (set < 0) return Not("no way sets the flag");
        Block test = join.Preds[set];
        // (The way that sets the flag may have a block of its own between the test and here.)
        Block reached = join;
        if (test.Terminator is { Op: Op.Jump } && test.Preds.Count == 1 && test.Succs.Count == 1 && !test.Nodes.Any(x => x.IsEffect && !x.IsTerminator))
            (reached, test) = (test, test.Preds[0]);
        if (test.Terminator is not { Op: Op.Branch } asked || test.Succs.Count != 2) return Not($"{test} does not end in a test");
        if (InstanceTestOf(asked.In[0]) is not var (tested, type, whenTrue)) return Not($"the test of {test} ({asked.In[0].Op}) is not a type test");
        if (!ReferenceEquals(tested, whenSet)) return Not($"the test is of {tested}, picked is {whenSet}");
        if (!ReferenceEquals(test.Succs[whenTrue ? 0 : 1], reached)) return Not($"{test} does not set the flag on the way that means it is one");
        // The first half of the test: "too few base classes to be one", which otherwise goes on to the second half.
        bool FirstHalf(Block block) => block.Terminator is { Op: Op.Branch } first && block.Succs.Count == 2 && block.Succs.Contains(test) &&
                                       first.In[0].Op is Op.CmpLtU or Op.CmpLeU && TypeTestCompare(first.In[0]) != null;
        for (int i = 0; i < join.Preds.Count; i++)
        {
            if (i == set) continue;
            Block cleared = join.Preds[i];
            if (ReferenceEquals(cleared, test) || FirstHalf(cleared)) continue;
            if (cleared.Terminator is not { Op: Op.Jump } || cleared.Nodes.Any(x => x.IsEffect && !x.IsTerminator)) return Not($"{cleared} clears the flag and does something else");
            foreach (Block before in cleared.Preds)
                if (!ReferenceEquals(before, test) && !FirstHalf(before))
                    return Not($"{before} also leads to {cleared}, where the flag is cleared");
        }
        return new SVal(new HTypeExpr(HTypeOp.IsInst, type, Value(tested)) { Type = type });
    }

    private Sem LoadSem(Node n)
    {
        if (_spillLoads.TryGetValue(n, out int parked)) return new SFrame(parked);
        if (_refLoads.TryGetValue(n, out Node? reference)) return Eval(reference);
        // The catch object is Il2CppExceptionWrapper&: its first field is the managed exception. (Reading the
        // reference itself out of the catch object slot stands for the same thing: it is only read through.)
        int region = -1;
        if (n.In[0] is { Op: Op.Idiom, Aux: int r } wrapper && (IdiomKind)wrapper.Imm == IdiomKind.CaughtWrapper) region = r;
        else if (_caughtLoads.TryGetValue(n.In[0], out int viaSlot) || _caughtLoads.TryGetValue(n, out viaSlot)) region = viaSlot;
        if (region >= 0 && n.Type == VT.I64)
        {
            HVar exception = RegionFor(region).Exception;
            return new SVal(new HLocal(exception) { Type = exception.Type });
        }
        if (ClassDataLoad(n) is { } classData) return classData;
        Place place = ResolvePlace(n.In[0], n.Type.Bytes());
        switch (place)
        {
            case PLocation { Location: HDeref { Pointer: HSelect { WhenTrue: HAddressOf first, WhenFalse: HAddressOf second } either } } picked:
                // Reading through a selected address is selecting between the two values.
                return new SVal(new HSelect(either.Condition, first.Target, second.Target) { Type = picked.Type });
            case PLocation loc:
                return new SVal(loc.Location is { Type: null } ? WithType(loc.Location, loc.Type) : loc.Location);
            case PPair pair:
                return new SPair(pair.Low, pair.High);
            case PParts parts:
                return new SParts(parts.Leaves, parts.Size);
            case PArrayLength len:
                return new SVal(new HArrayLength(len.Array) { Type = _int });
            case PChosenValue chosen:
                return new SVal(chosen.Value);
            case PObjKlass ok:
                return new SObjKlass(ok.Object);
            case PStatics st:
                return new SStatics(st.Type);
            case PVTable vt:
                return new SVTable(vt.Object, vt.Slot, vt.MethodInfo);
            case PInternal:
                return SJunk.Instance;
            case PKlassOf of:
                return new SKlass(of.Type);
            case PMethodCode code:
                return new SMethodCode(code.Method.Method, code.Method.Inst);
            case PRgctx table:
                return table.Context;
            case PRgctxItem entry:
                return RgctxValue(entry.Context, entry.Index);
            case PUnboxed u:
            {
                TypeSig? type = _castTypes.TryGetValue(u.Object, out List<TypeSig>? casts) && casts.Count != 0 ? casts[0] : null;
                if (type == null && n.Block != null) type = ProvenClass(u.Object, n.Block);
                if (type == null)
                {
                    Problem("unboxed value of unknown type");
                    type = TypeForBits(n.Type);
                }
                var unboxed = new HTypeExpr(HTypeOp.UnboxAny, type, Value(u.Object)) { Type = type };
                var (size, _, _) = _p.Layouts.SizeOf(type);
                bool isStruct = type.Definition is { IsValueType: true, IsEnum: false } && type is not PrimitiveSig;
                if (u.Offset == 0 && (!isStruct || size == n.Type.Bytes())) return new SVal(unboxed);
                if (isStruct && FieldPlace(unboxed, type, u.Offset, n.Type.Bytes()) is PLocation inner) return new SVal(inner.Location);
                if (isStruct && FieldPlace(unboxed, type, u.Offset, n.Type.Bytes()) is PPair innerPair) return new SPair(innerPair.Low, innerPair.High);
                // A word read whole (clang loads a struct's first eight bytes for a register pair): the fields in
                // it, the padding between them nothing.
                if (isStruct && !NoUnboxedWords && StructLeaves(unboxed, type, u.Offset, n.Type.Bytes()) is { } words)
                    return new SParts(words, n.Type.Bytes());
                Problem("partial read of an unboxed value");
                return new SVal(Site(new HOpaque("unbox_part", unboxed) { Type = TypeForBits(n.Type) }, "partial read of an unboxed value"));
            }
            case PBits bits:
            {
                HExpr whole = new HLocal(bits.Variable) { Type = bits.Variable.Type };
                if (bits.Shift != 0)
                    whole = new HBinary(HBinaryOp.ShrUn, whole, new HConst(bits.Shift * 8, _int)) { Type = bits.Variable.Type };
                TypeSig type = TypeForBits(n.Type.IsInt() ? n.Type : VTExtensions.IntOfBytes(bits.Size));
                HConvKind kind = bits.Size switch { 1 => HConvKind.U1, 2 => HConvKind.I2, 4 => HConvKind.I4, _ => HConvKind.I8 };
                return new SVal(new HConv(kind, whole) { Type = type });
            }
            case PChunk chunk:
                return new SChunk(SnapshotOf(chunk.Owner, chunk.OwnerType, n.Addr), chunk.OwnerType, chunk.Offset, chunk.Size);
            case PUnknown unknown:
                Problem("load: " + unknown.Why);
                return new SVal(Site(new HOpaque("load" + n.Type.Bytes(), Value(n.In[0])) { Type = TypeForBits(n.Type) }, "load: " + unknown.Why));
            default:
                return SJunk.Instance;
        }
    }

    private static HExpr WithType(HExpr e, TypeSig type)
    {
        e.Type = type;
        return e;
    }

    private readonly Block _scratch = new();
    private IrBuilder? _scratchBuilder;

    /// <summary>
    /// A register holds 64 bits but a bool, byte or int argument uses only some of them; the rest is whatever
    /// was there before. Cutting the value to the width that is used lets that leftover fall away.
    /// </summary>
    private Node Narrowed(Node n, int bits)
    {
        if (bits is not (8 or 16 or 32) || !n.Type.IsInt() || n.Type.Bits() <= bits || n.IsConst) return n;
        if (n.Op is not (Op.Or or Op.And or Op.Xor or Op.Add or Op.Sub or Op.ZExt or Op.SExt or Op.Trunc or Op.Select or Op.Concat)) return n;
        // A value that was given a name of its own (a temporary) is used through that name. One that was merely
        // looked at before - while choosing between candidate methods, say - can still be cut to size.
        if (_materialize.Contains(n) || (_sem.TryGetValue(n, out Sem? seen) && seen is not SVal { Expr: not HLocal })) return n;
        _scratchBuilder ??= new IrBuilder(_fn) { Current = _scratch };
        _scratchBuilder.Current = _scratch;
        return _scratchBuilder.Trunc(n, bits == 8 ? VT.I8 : bits == 16 ? VT.I16 : VT.I32);
    }

    /// <summary>The value of a node as something assignable to a location of the given type.</summary>
    private HExpr ValueFor(Node n, TypeSig target)
    {
        // Skip widening that only filled a register: the store or call narrows again.
        int bits = BitsOf(target);
        // What takes 32 bits or fewer of a slot made of two halves takes the low half; the high half - what the
        // slot held before, as a rule - is not looked at.
        if (n.Op == Op.Concat && !NoUnreadHalves && (bits is 8 or 16 or 32 || (bits == 0 && FitsHalf(target)))) n = n.In[1];
        Node source = Narrowed(n, bits);
        while (source.Op is Op.ZExt or Op.SExt && bits != 0 && source.In[0].Type.Bits() >= bits && source.In[0].Type != VT.I1)
            source = source.In[0];

        bool isStruct = target.Definition is { IsValueType: true, IsEnum: false } && target is not PrimitiveSig;
        if (isStruct)
        {
            Sem s = Eval(source);
            if (s is SVal v && v.Type != null && ReferenceEquals(v.Type, target)) return v.Expr;
            if (s is SRef r && ReferenceEquals(r.Type, target)) return r.Location;
            return StructFromBits(source, target);
        }
        // A value of 32 bits or fewer in a 64-bit slot that is two halves side by side (an argument passed on
        // the stack, as a rule): the low half. The high half is whatever was there before.
        if (bits is 8 or 16 or 32 && source.Type == VT.I64 && !NoLowHalves && Eval(source) is SPair halves)
            return Coerce(Narrow(halves.Low, target), target);
        HExpr e = Value(source);
        return Coerce(Narrow(e, target), target);
    }

    private static readonly bool NoLowHalves = Environment.GetEnvironmentVariable("REWIND_NO_LOW_HALVES") != null;
    private static readonly bool NoUnreadHalves = Environment.GetEnvironmentVariable("REWIND_NO_UNREAD_HALVES") != null;

    /// <summary>A struct of four bytes or fewer: in a 64-bit slot it is in the low half.</summary>
    private bool FitsHalf(TypeSig type) =>
        type.Definition is { IsValueType: true } && _p.Layouts.Of(type) is { Known: true, Size: 1 or 2 or 4 };
    private static readonly bool NoRetypedWrites = Environment.GetEnvironmentVariable("REWIND_NO_RETYPED_WRITES") != null;
    private static readonly bool NoDeclaredFloats = Environment.GetEnvironmentVariable("REWIND_NO_DECLARED_FLOATS") != null;

    private static readonly bool NoBoxLifetimes = Environment.GetEnvironmentVariable("REWIND_NO_BOX_LIFETIMES") != null;

    private void EmitStore(Node n)
    {
        // The header of a value boxed in place (its class, and the "not a real object" mark) is not a store
        // the program makes.
        if (_fakeBoxes.Count != 0 && IsFrameAddress(n.In[0], out int boxOffset) &&
            (_fakeBoxes.ContainsKey(boxOffset) || _fakeBoxes.ContainsKey(boxOffset - _ptr)))
        {
            // (What is written there for the box: the class, and the mark - or, through the runtime's own
            // constructor, nothing at all here.)
            bool first = _fakeBoxes.ContainsKey(boxOffset);
            Node written = n.In[1];
            bool header = first ? written.Op == Op.SlotValue : written.IsConst && written.Imm == -1;
            if (header || NoBoxLifetimes) return;
            // Anything else stored in those bytes is the program's: the compiler keeps another local there
            // while no box is ("key.message = message", then - later - the class of an enum boxed to be printed).
            // Dropped, that local read as never set.
            FrameConflicts.Add(first ? boxOffset : boxOffset - _ptr);
        }
        if (_spillStores.Contains(n)) return; // a parked stack address (see PlanAddressSpills)
        if (_caughtStores.Contains(n)) return; // the catch object (see PlanCaughtSlots)
        Node valueNode = n.In[1];
        int size = valueNode.Type.Bytes();
        // A class written to stack memory is the header of a value boxed in place. Where that memory is a typed
        // struct, the struct is another lifetime of the same bytes.
        if (valueNode.Op == Op.SlotValue && IsFrameAddress(n.In[0], out int headerAt) && FrameObjectAt(headerAt) is int reused &&
            Eval(valueNode) is SKlass { Type.IsValueType: true })
            FrameConflicts.Add(reused);
        Place place = ResolvePlace(n.In[0], size);
        // Bytes of untyped stack memory copied into bytes of a struct: the stack memory is a copy of that struct
        // (a struct built on the stack field by field, then copied out eight bytes at a time).
        // (Only from the struct's first bytes: where just a later part of it was put together on the stack, the
        // stack memory before that part is something else.)
        if (!NoCopyTypes && valueNode.Op == Op.Load && IsFrameAddress(valueNode.In[0], out int copiedFrom) && !IsFrameAddress(n.In[0], out _))
        {
            if (place is PChunk { Offset: 0 } destination) VoteCopyType(copiedFrom, destination.OwnerType);
            else if (place is PParts { OwnerType: { } owner, Leaves.Count: > 1, Offset: 0 }) VoteCopyType(copiedFrom, owner);
        }
        // A caught exception put into a typed stack struct that has no place for one: the slot it waits in until
        // the clean-up code has run and it is thrown again, in bytes that held another local before.
        if (size == 8 && IsFrameAddress(n.In[0], out int keptAt) && FrameObjectAt(keptAt) is not null &&
            Eval(valueNode) is SVal { Expr: HLocal { Variable: var caught } } && _h.TryRegions.Values.Any(r => ReferenceEquals(r.Exception, caught)) &&
            !(place is PLocation { Type: { } keptIn } && IsReference(keptIn) && IsAssignable(caught.Type, keptIn)))
            FrameConflicts.Add(keptAt);
        switch (place)
        {
            case PLocation loc:
                // (Bytes read at other widths as well are loose bits - unless a struct of all eight is stored whole:
                // its fields are what the narrower reads take.)
                if (size == 8 && ReferenceEquals(loc.Type, _long) && IsFrameAddress(n.In[0], out int slotAt) && !_frameTypes.ContainsKey(slotAt) &&
                    (!_rawCells.ContainsKey(slotAt) || (!NoStructVotes && Eval(valueNode) is SVal { Type: { } whole } && IsStructType(whole) && _p.Layouts.SizeOf(whole) is { Known: true, Size: 8 })))
                    VoteFrameType(slotAt, valueNode);
                // A struct written through a pointer to something else of its size: for this write the pointer
                // is a pointer to that struct ("*(NetworkBool*)(Ptr + 4) = value").
                if (loc.Location is HDeref through && !NoRetypedWrites && loc.Type is PrimitiveSig && !IsFloat(loc.Type) &&
                    Eval(valueNode) is SVal { Type: { } written } && IsStructType(written) && _p.Layouts.SizeOf(written).Size == size)
                {
                    Emit(new HAssign(new HDeref(through.Pointer) { Type = written }, ValueFor(valueNode, written)), n.Addr);
                    return;
                }
                Emit(new HAssign(loc.Location, ValueFor(valueNode, loc.Type)), n.Addr);
                return;
            case PPair pair:
            {
                // A whole number where two floats are - a sum, a count widened to 64 bits, a constant that read
                // as floats is no number anyone writes: other data in a reused slot (a loop's spilled offset
                // where a vector was). Each lifetime gets its own memory (see StackSplitting).
                if (!NoPairConflicts && (IsFloat(pair.Low.Type) || IsFloat(pair.High.Type)) && IsFrameAddress(n.In[0], out int pairAt) &&
                    IsWholeNumber(valueNode, IsFloat(pair.Low.Type), IsFloat(pair.High.Type)))
                    FrameConflicts.Add(pairAt);
                MarkReferenceInPieces(n, valueNode);
                Sem s = Eval(valueNode);
                HExpr low, high;
                if (s is SPair p) (low, high) = (p.Low, p.High);
                else if (valueNode.IsConst)
                {
                    low = Coerce(new HConst((int)(valueNode.UImm & 0xFFFFFFFF), _int), pair.Low.Type!);
                    high = Coerce(new HConst((int)(valueNode.UImm >> 32), _int), pair.High.Type!);
                    if (IsFloat(pair.Low.Type)) low = new HConst(BitConverter.Int32BitsToSingle((int)(valueNode.UImm & 0xFFFFFFFF)), _float);
                    if (IsFloat(pair.High.Type)) high = new HConst(BitConverter.Int32BitsToSingle((int)(valueNode.UImm >> 32)), _float);
                }
                else
                {
                    StoreParts([new Part(0, 4, pair.Low), new Part(4, 4, pair.High)], valueNode, n.Addr);
                    return;
                }
                Emit(new HAssign(pair.Low, low), n.Addr);
                Emit(new HAssign(pair.High, high), n.Addr);
                return;
            }
            case PParts parts:
                MarkReferenceInPieces(n, valueNode);
                StoreParts(parts.Leaves, valueNode, n.Addr);
                return;
            case PInternal:
                return; // writes to runtime bookkeeping have no managed meaning
            case PBits bits:
            {
                // var = (var & ~(mask << shift)) | ((value & mask) << shift), in the variable's width.
                TypeSig wide = bits.Variable.Type;
                bool is64 = BitsOf(wide) == 64;
                ulong mask = bits.Size >= 8 ? ulong.MaxValue : (1UL << (bits.Size * 8)) - 1;
                ulong keep = ~(mask << (bits.Shift * 8));
                if (!is64) keep &= 0xFFFFFFFF;
                HExpr Const(ulong v) => is64 ? new HConst((long)v, wide) : new HConst((int)(uint)v, wide);
                HExpr value = BitsOfValue(ValueFor(valueNode, TypeForBits(valueNode.Type)), bits.Size);
                if (!is64) value = new HConv(HConvKind.I4, value) { Type = wide };
                HExpr part;
                if (value is HConst { Value: int or long } known)
                    part = Const(((ulong)Convert.ToInt64(known.Value) & mask) << (bits.Shift * 8));
                else
                {
                    part = new HBinary(HBinaryOp.And, value, Const(mask)) { Type = wide };
                    if (bits.Shift != 0) part = new HBinary(HBinaryOp.Shl, part, new HConst(bits.Shift * 8, _int)) { Type = wide };
                }
                var target = new HLocal(bits.Variable) { Type = wide };
                HExpr kept = new HBinary(HBinaryOp.And, new HLocal(bits.Variable) { Type = wide }, Const(keep)) { Type = wide };
                bool nothing = part is HConst { Value: int or long } zero && Convert.ToInt64(zero.Value) == 0;
                Emit(new HAssign(target, nothing ? kept : new HBinary(HBinaryOp.Or, kept, part) { Type = wide }), n.Addr);
                return;
            }
            case PChunk chunk when Eval(valueNode) is SChunk piece && piece.Type.Key == chunk.OwnerType.Key &&
                                   piece.Offset == chunk.Offset && piece.Size == chunk.Size:
                CopyChunk(chunk, piece, n.Addr);
                return;
            case PUnknown unknown:
                // Bytes of a typed stack struct written as something that is no field of it: often other data
                // in a reused slot.
                if (unknown is PChunk && IsFrameAddress(n.In[0], out int misfit)) FrameConflicts.Add(misfit);
                Problem("store: " + unknown.Why);
                Emit(new HEval(new HOpaque("store" + size, Value(n.In[0]), Value(valueNode))), n.Addr);
                return;
            default:
                Problem("store to " + place.GetType().Name[1..]);
                Emit(new HEval(new HOpaque("store" + size, Value(n.In[0]), Value(valueNode))), n.Addr);
                return;
        }
    }

    /// <summary>
    /// A struct of at most 8 bytes travels in an integer register. Rebuilds the struct value from those bits.
    /// </summary>
    private HExpr StructFromBits(Node n, TypeSig structType)
    {
        if (n.Op == Op.Concat && !NoUnreadHalves && FitsHalf(structType)) n = n.In[1];
        Sem s = Eval(n);
        if (s is SVal v && v.Type != null && ReferenceEquals(v.Type, structType)) return v.Expr;
        if (s is SRef r && ReferenceEquals(r.Type, structType)) return r.Location;

        TypeLayout layout = _p.Layouts.Of(structType);
        // A struct smaller than the register it travels in: the widening that filled the register is not part
        // of it ("s.id = (ulong)id" for a struct that is one int).
        if (layout.Known && layout.Size is 1 or 2 or 4 && !NoLowHalves)
        {
            Node inner = n;
            while (inner.Op is Op.ZExt or Op.SExt && inner.In[0].Type.IsInt() && inner.In[0].Type.Bytes() >= layout.Size && inner.In[0].Type != VT.I1)
                inner = inner.In[0];
            if (!ReferenceEquals(inner, n))
            {
                n = inner;
                s = Eval(n);
                if (s is SVal narrow && narrow.Type != null && ReferenceEquals(narrow.Type, structType)) return narrow.Expr;
                if (s is SRef narrowRef && ReferenceEquals(narrowRef.Type, structType)) return narrowRef.Location;
            }
        }
        // A struct without fields has one value, whatever the bytes standing in for it happen to hold.
        if (layout.Known && layout.Fields.Length == 0 && IsStructType(structType))
            return new HTypeExpr(HTypeOp.Default, structType, null) { Type = structType };
        // All bits zero: the default value, whatever the fields are.
        if (!NoStructZero && IsStructType(structType) && s is SVal { Expr: HConst { Value: int or long } nothing } && Convert.ToInt64(nothing.Value) == 0)
            return new HTypeExpr(HTypeOp.Default, structType, null) { Type = structType };
        var parts = new List<(FieldSlot Slot, HExpr Value)>();
        bool ok = true;
        bool Direct(HExpr given, TypeSig field) => NoLowHalves || !IsStructType(field) || ReferenceEquals(given.Type, field);
        if (s is SPair pair && layout.Fields.Length == 2 && layout.Fields[0].Size == 4 && layout.Fields[1].Size == 4 &&
            Direct(pair.Low, layout.Fields[0].Type) && Direct(pair.High, layout.Fields[1].Type))
        {
            parts.Add((layout.Fields[0], Coerce(pair.Low, layout.Fields[0].Type)));
            parts.Add((layout.Fields[1], Coerce(pair.High, layout.Fields[1].Type)));
        }
        else if (layout.Fields.Length == 1 && s is SVal single && Direct(single.Expr, layout.Fields[0].Type))
        {
            parts.Add((layout.Fields[0], Coerce(single.Expr, layout.Fields[0].Type)));
        }
        else if (s is SVal { Expr: HConst { Value: int or long } zero } && Convert.ToInt64(zero.Value) == 0)
        {
            return new HTypeExpr(HTypeOp.Default, structType, null) { Type = structType };
        }
        else if (HandleFromToken(s, structType) is { } handle)
        {
            return handle;
        }
        else
        {
            // Any other arrangement of scalar fields: each field takes its own bytes of the register.
            var leaves = new List<Part>();
            HVar whole = _h.NewLocal(structType, "s");
            whole.AddressTaken = true;
            var target = new HLocal(whole) { Type = structType };
            if (layout.Size is > 0 and <= 8 &&
                ((Leaves(target, structType, 0, layout.Size, 0, leaves) && leaves.Count != 0) || UnionLeaves(target, structType, layout.Size, leaves)))
            {
                StoreParts(leaves, n, n.Addr);
                return new HLocal(whole) { Type = structType };
            }
            _h.Locals.Remove(whole);
            ok = false;
        }

        if (!ok)
        {
            string fromBits = $"could not rebuild {structType.DisplayName} from register bits";
            Problem(fromBits);
            return Site(new HOpaque("struct_from_bits", Value(n)) { Type = structType }, fromBits);
        }
        HVar temp = _h.NewLocal(structType, "s");
        temp.AddressTaken = true;
        foreach (var (slot, value) in parts)
            Emit(new HAssign(new HField { Object = new HLocal(temp) { Type = structType }, Field = slot.Field, DeclaringType = structType, Type = slot.Type }, value), n.Addr);
        return new HLocal(temp) { Type = structType };
    }

    // ---- additions that are addresses --------------------------------------------------------------------------

    private Sem AddSem(Node n)
    {
        AddressParts a = Decompose(n);
        if (a.Base != null && a.Scale >= 0)
        {
            // An interior address used as a value: the address of a field, element or local.
            if (a.BaseSem is SFrame f && a.Index == null) return new SFrame(f.Offset + (int)a.Offset);
            // &klass->byval_arg: the class's own type record, which is what a type handle holds (typeof(T)).
            if (a.BaseSem is SKlass ofClass && a.Index == null && a.Offset == _p.Klass.ByvalArg) return new SType(ofClass.Type);
            if (a.BaseSem is SObjKlass or SKlass or SStatics)
            {
                Place inner = ResolvePlace(n, -1);
                if (inner is PLocation located) return new SRef(located.Location, located.Type);
                return SJunk.Instance;
            }
            Place place = ResolvePlace(n, -1);
            switch (place)
            {
                case PLocation loc:
                    if (loc.Location is HDeref { Pointer: var pointer } && pointer.Type is PointerSig) return new SVal(pointer);
                    return new SRef(loc.Location, loc.Type);
                case PUnboxed u when u.Offset == 0:
                    return new SUnboxed(u.Object);
                case PArrayLength or PObjKlass or PInternal or PVTable or PStatics or PKlassOf or PMethodCode or PRgctx or PRgctxItem:
                    return SJunk.Instance;
            }
            if (a.BaseSem is SVal { Type: PrimitiveSig { Element: Il2CppTypeEnum.I or Il2CppTypeEnum.U } }) return BinarySem(n);
            // An address into something no managed location was found in: the arithmetic stays, as the operand
            // of a marker (a number added to a reference is no value IL has).
            string what = "address computation: " + (place is PUnknown unknown ? unknown.Why : place.GetType().Name[1..]);
            Problem(what);
            Sem arithmetic = BinarySem(n);
            return arithmetic is SVal { Expr: var computed } ? new SVal(Site(new HOpaque("address", computed) { Type = TypeForBits(n.Type) }, what)) : arithmetic;
        }
        return BinarySem(n);
    }

    // ---- stack locals ------------------------------------------------------------------------------------------

    private static readonly bool FrameDebug = Environment.GetEnvironmentVariable("REWIND_FRAME_DEBUG") != null;

    private HVar FrameVar(int offset, TypeSig type)
    {
        var key = (offset, type.Key);
        if (!_frameVars.TryGetValue(key, out HVar? variable))
        {
            variable = _h.NewLocal(type, FrameDebug ? $"local_{-offset:X}_" : "local");
            variable.AddressTaken = true;
            _frameVars[key] = variable;
        }
        return variable;
    }

    /// <summary>
    /// An untyped 8-byte slot written with object references of one type (and nothing else but null) holds that
    /// type: the compiler keeps a reference local in memory (around a try region, for instance).
    /// </summary>
    private static readonly bool NoStructVotes = Environment.GetEnvironmentVariable("REWIND_NO_STRUCT_SLOT_VOTES") != null;

    private void VoteFrameType(int offset, Node value)
    {
        if (value.IsConst && value.Imm == 0) return; // null fits any reference type
        TypeSig? type = Eval(value) switch
        {
            SVal { Expr: not HConst } v => v.Expr.Type,
            SNewObject o => o.Type,
            _ => null,
        };
        // (A struct of just those eight bytes stored whole - a call's Nullable<float>, say - holds the slot as well.)
        bool wholeStruct = !NoStructVotes && type != null && IsStructType(type) && _p.Layouts.SizeOf(type) is { Known: true, Size: 8 };
        TypeSig vote = type != null && (IsReference(type) || wholeStruct) && !Open(type) && Nameable(type) ? type : _long;
        if (!_frameVotes.TryGetValue(offset, out HashSet<TypeSig>? votes)) _frameVotes[offset] = votes = [];
        votes.Add(vote);
    }

    private static readonly bool NoCopyTypes = Environment.GetEnvironmentVariable("REWIND_NO_COPY_TYPES") != null;
    private static readonly bool NoPaddedParts = Environment.GetEnvironmentVariable("REWIND_NO_PADDED_PARTS") != null;

    /// <summary>Stack offset to the struct types the memory there was copied out as (see EmitStore).</summary>
    private readonly Dictionary<int, HashSet<TypeSig>> _copyVotes = [];

    private void VoteCopyType(int start, TypeSig type)
    {
        if (!IsStructType(type) || Open(type) || !Nameable(type) || _frameTypes.ContainsKey(start)) return;
        if (!_copyVotes.TryGetValue(start, out HashSet<TypeSig>? votes)) _copyVotes[start] = votes = [];
        votes.Add(type);
    }

    private static readonly bool NoWidePairs = Environment.GetEnvironmentVariable("REWIND_NO_WIDE_PAIRS") != null;
    private static readonly bool NoPairConflicts = Environment.GetEnvironmentVariable("REWIND_NO_PAIR_CONFLICTS") != null;

    /// <summary>
    /// True when eight bytes are a whole number and not two floats side by side: the result of integer
    /// arithmetic, or a constant one of whose float halves would be a denormal or an odd "not a number".
    /// </summary>
    private static bool IsWholeNumber(Node value, bool lowIsFloat, bool highIsFloat)
    {
        if (value.Type != VT.I64) return false;
        if (value.Op is Op.Add or Op.Sub or Op.Mul or Op.SExt) return true;
        if (!value.IsConst) return false;
        static bool Unlikely(uint bits)
        {
            uint exponent = (bits >> 23) & 0xFF, fraction = bits & 0x7FFFFF;
            // (Infinity and the one "not a number" a program names are numbers people do write.)
            return (exponent == 0 && fraction != 0) || (exponent == 0xFF && fraction != 0 && fraction != 0x400000);
        }
        return (lowIsFloat && Unlikely((uint)(value.UImm & 0xFFFFFFFF))) || (highIsFloat && Unlikely((uint)(value.UImm >> 32)));
    }

    private Place FramePlace(int offset, int size)
    {
        // Prefer a typed object that covers this offset.
        foreach (var (start, type) in _frameTypes.OrderByDescending(kv => kv.Key))
        {
            if (offset < start) continue;
            var (typeSize, _, _) = _p.Layouts.SizeOf(type);
            if (offset >= start + Math.Max(1, typeSize)) continue;
            var local = new HLocal(FrameVar(start, type)) { Type = type };
            bool isStruct = type.Definition is { IsValueType: true, IsEnum: false } && type is not PrimitiveSig;
            // Eight bytes moved where a variable of four is, with another of four right behind it: the two
            // together (the x and y of a vector kept as separate numbers, copied in one go). Taken as the first
            // alone, the second was never set.
            if (!NoWidePairs && offset == start && !isStruct && size == 8 && typeSize == 4 &&
                _frameTypes.TryGetValue(start + 4, out TypeSig? behind) && !IsStructType(behind) && _p.Layouts.SizeOf(behind) is { Known: true, Size: 4 })
                return new PPair(local, new HLocal(FrameVar(start + 4, behind)) { Type = behind });
            if (offset == start && (!isStruct || size < 0 || size == typeSize)) return new PLocation(local, type);
            if (isStruct)
            {
                Place inside = FieldPlace(local, type, offset - start, size);
                // Bytes of a typed stack struct that are no field of it: often other data in a reused slot.
                if (inside is PUnknown and not PChunk) FrameConflicts.Add(start);
                return inside;
            }
            if (size > 0 && offset + size <= start + typeSize && type is PrimitiveSig && !IsFloat(type) && BitsOf(type) is 16 or 32 or 64)
                return new PBits(FrameVar(start, type), offset - start, size);
            return new PUnknown("partial access to a scalar local");
        }
        // An untyped slot accessed at several widths is one variable (see PlanRawCells).
        foreach (var (start, width) in _rawCells)
        {
            if (offset < start || offset >= start + width) continue;
            TypeSig cellType = width switch { 1 => _byte, 2 => _short, 4 => _int, _ => _long };
            if (offset == start && (size <= 0 || size == width)) return new PLocation(new HLocal(FrameVar(start, cellType)) { Type = cellType }, cellType);
            if (size > 0 && offset + size <= start + width) return new PBits(FrameVar(start, cellType), offset - start, size);
            break;
        }
        if (size <= 0) size = 8;
        TypeSig raw = size switch { 1 => _byte, 2 => _short, 4 => _int, _ => _long };
        return new PLocation(new HLocal(FrameVar(offset, raw)) { Type = raw }, raw);
    }
}
