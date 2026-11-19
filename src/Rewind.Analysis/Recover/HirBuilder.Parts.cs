// Modified by xob0t (2026): wide stores over inherited fields, gaps always marked, bits read as float/double. See FORK.md.
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Model;
using Rewind.Runtime;

namespace Rewind.Analysis.Recover;

/// <summary>One scalar field inside a run of bytes: where it sits, how wide it is, and how to name it.</summary>
internal readonly record struct Part(int Offset, int Size, HExpr Value);

/// <summary>
/// Several independent values travelling together as one run of bytes: what a compiler produces when it moves
/// a struct, or a few adjacent fields, through a register or with one wide load.
/// </summary>
internal sealed class SParts(List<Part> parts, int size) : Sem
{
    public List<Part> Parts = parts;
    public int Size = size;
}

/// <summary>
/// Compilers move structs as raw bytes: eight at a time through a register, sixteen through a vector register,
/// whatever the fields inside are. This part of the builder keeps such moves exact: a wide access is resolved
/// into the fields it covers, and where bytes really are treated as one number the bit arithmetic is written
/// out, so nothing has to be left unexplained.
/// </summary>
public sealed partial class HirBuilder
{
    private sealed record PParts(List<Part> Leaves, int Size) : Place
    {
        /// <summary>The struct the bytes lie in, and where in it they start.</summary>
        public HExpr? Owner { get; init; }
        public TypeSig? OwnerType { get; init; }
        public int Offset { get; init; }
    }

    private static bool IsStructType(TypeSig? t) => t?.Definition is { IsValueType: true, IsEnum: false } && t is not PrimitiveSig;

    /// <summary>
    /// The scalar fields of <paramref name="type"/> that lie in [offset, offset + size), as locations under
    /// <paramref name="owner"/>. Fails when a scalar is only partly inside the range or fields overlap.
    /// </summary>
    private bool Leaves(HExpr owner, TypeSig type, int offset, int size, int baseOffset, List<Part> output, int depth = 0)
    {
        if (depth > 8) return false;
        foreach (FieldSlot slot in InstanceFields(type))
        {
            int start = Math.Max(offset, slot.Offset), end = Math.Min(offset + size, slot.Offset + slot.Size);
            if (start >= end) continue;
            var field = new HField { Object = owner, Field = slot.Field, DeclaringType = type, Type = slot.Type };
            bool whole = start == slot.Offset && end == slot.Offset + slot.Size;
            if (IsStructType(slot.Type))
            {
                if (!Leaves(field, slot.Type, start - slot.Offset, end - start, baseOffset + start - offset, output, depth + 1)) return false;
            }
            else if (whole) output.Add(new Part(baseOffset + slot.Offset - offset, slot.Size, field));
            else return false;
        }
        // Overlapping fields (a union) cannot be told apart by position.
        for (int i = 1; i < output.Count; i++)
            if (output[i].Offset < output[i - 1].Offset + output[i - 1].Size && output[i].Offset >= output[i - 1].Offset)
                return false;
        return true;
    }

    private static readonly bool NoInheritedParts = Environment.GetEnvironmentVariable("REWIND_NO_INHERITED_PARTS") != null;

    /// <summary>
    /// The instance fields an object of <paramref name="type"/> has, by offset: a struct's own, a class's own and
    /// those of each class it derives from (one wide write can set the last field a base class declares and the
    /// first of the class below, or two flags side by side in a base class).
    /// </summary>
    private IEnumerable<FieldSlot> InstanceFields(TypeSig type)
    {
        TypeLayout layout = _p.Layouts.Of(type);
        if (NoInheritedParts || type.Definition is not { IsValueType: false } definition || definition.BaseType == null) return layout.Fields;
        var chain = new List<FieldSlot>();
        for (TypeSig? current = type; current?.Definition is { } def;)
        {
            chain.AddRange(_p.Layouts.Of(current).Fields);
            if (def.BaseType == null) break;
            current = _m.Sigs.Substitute(def.BaseType, current is GenericInstSig g ? g.Arguments : [], []);
        }
        return chain.OrderBy(f => f.Offset);
    }

    private static readonly bool NoUnions =Environment.GetEnvironmentVariable("REWIND_NO_UNION_PARTS") != null;

    /// <summary>
    /// The fields that fill a struct whose fields lie over each other (a union, as Color32's "rgba" over "r",
    /// "g", "b", "a"), each byte once: for writing the whole struct, where it does not matter which of the fields
    /// over a byte carries it. The public fields first - the ones code outside the struct can name - each where
    /// nothing taken before covers any of its bytes. Scalars only.
    /// </summary>
    private bool UnionLeaves(HExpr owner, TypeSig type, int size, List<Part> output)
    {
        output.Clear();
        if (NoUnions) return false;
        TypeLayout layout = _p.Layouts.Of(type);
        if (!layout.Known) return false;
        var covered = new bool[size];
        foreach (bool open in new[] { true, false })
            foreach (FieldSlot slot in layout.Fields.OrderBy(f => f.Offset).ThenByDescending(f => f.Size))
            {
                if (((slot.Field.Attrs & FieldDef.AccessMask) == 6) != open) continue;
                if (IsStructType(slot.Type) || slot.Size <= 0 || slot.Offset < 0 || slot.Offset + slot.Size > size)
                {
                    output.Clear();
                    return false;
                }
                bool free = true;
                for (int b = slot.Offset; b < slot.Offset + slot.Size; b++) free &= !covered[b];
                if (!free) continue;
                for (int b = slot.Offset; b < slot.Offset + slot.Size; b++) covered[b] = true;
                output.Add(new Part(slot.Offset, slot.Size, new HField { Object = owner, Field = slot.Field, DeclaringType = type, Type = slot.Type }));
            }
        output.Sort((a, b) => a.Offset.CompareTo(b.Offset));
        return output.Count != 0;
    }

    private MethodDef? BitConverterMethod(string name, TypeSig parameter) =>
        _m.FindType("System.BitConverter")?.Methods.FirstOrDefault(m => m.IsStatic && m.Name == name && m.Parameters.Length == 1 && ReferenceEquals(m.Parameters[0].Type, parameter));

    private MethodDef? BitConverterReader(string name) =>
        _m.FindType("System.BitConverter")?.Methods.FirstOrDefault(m => m.IsStatic && m.Name == name && m.Parameters.Length == 2 &&
            m.Parameters[0].Type is SzArraySig bytes && ReferenceEquals(bytes.ElementType, _byte) && ReferenceEquals(m.Parameters[1].Type, _int));

    /// <summary>
    /// The bits of a float as an int: BitConverter.SingleToInt32Bits where the game's class library has it.
    /// The one Unity 2020 ships does not; there the same is said through the float's bytes, which every class
    /// library can: BitConverter.ToInt32(BitConverter.GetBytes(value), 0). Null when it has neither.
    /// </summary>
    private HExpr? SingleBits(HExpr value)
    {
        if (BitConverterMethod("SingleToInt32Bits", _float) is { } toBits) return new HCall { Method = toBits, Arguments = [value], Type = _int };
        if (BitConverterMethod("GetBytes", _float) is { } bytes && BitConverterReader("ToInt32") is { } read)
            return new HCall { Method = read, Arguments = [new HCall { Method = bytes, Arguments = [value], Type = bytes.ReturnType }, new HConst(0, _int)], Type = _int };
        return null;
    }

    /// <summary>The float whose bits are the given int, the same two ways.</summary>
    private HExpr? SingleFromBits(HExpr bits)
    {
        if (BitConverterMethod("Int32BitsToSingle", _int) is { } fromBits) return new HCall { Method = fromBits, Arguments = [bits], Type = _float };
        if (BitConverterMethod("GetBytes", _int) is { } bytes && BitConverterReader("ToSingle") is { } read)
            return new HCall { Method = read, Arguments = [new HCall { Method = bytes, Arguments = [bits], Type = bytes.ReturnType }, new HConst(0, _int)], Type = _float };
        return null;
    }

    private static readonly bool NoBitCasts = Environment.GetEnvironmentVariable("REWIND_NO_BIT_CASTS") != null;

    /// <summary>
    /// The value whose bits are those of <paramref name="value"/>, read as <paramref name="type"/> (a number of
    /// the same size), where the class library has no call for it: the value's own memory read as the other
    /// type, "*(double*)&amp;bits" (emitted as ldloca and ldobj). Null when that is off or the sizes differ.
    /// </summary>
    private HExpr? BitCast(HExpr value, TypeSig type)
    {
        if (NoBitCasts || value.Type is not PrimitiveSig || BitsOf(value.Type) is not (32 or 64) || BitsOf(value.Type) != BitsOf(type)) return null;
        return new HDeref(new HAddressOf(value) { Type = _m.Sigs.Pointer(value.Type) }) { Type = type };
    }

    /// <summary>Matches what SingleBits and SingleFromBits build (whichever way): the value whose bits are read as the other type.</summary>
    private static bool IsReinterpreted(HExpr e, string direct, string reader, out HExpr original)
    {
        if (e is HDeref read && read.IsBitCast(out original)) return true;
        original = e;
        if (e is not HCall { This: null, Method: { DeclaringType: { Name: "BitConverter", Namespace: "System" } } method } call) return false;
        if (method.Name == direct && call.Arguments.Length == 1)
        {
            original = call.Arguments[0];
            return true;
        }
        if (method.Name != reader || call.Arguments.Length != 2 || call.Arguments[1] is not HConst { Value: 0 }) return false;
        if (call.Arguments[0] is not HCall { This: null, Method: { Name: "GetBytes", DeclaringType: { Name: "BitConverter", Namespace: "System" } }, Arguments: [{ } inner] }) return false;
        original = inner;
        return true;
    }

    /// <summary>The bit pattern of a scalar as an unsigned integer of 64 bits (its own width, zero-extended).</summary>
    private HExpr BitsOfValue(HExpr e, int size)
    {
        TypeSig? t = e.Type;
        if (ReferenceEquals(t, _float))
        {
            if (e is HConst { Value: float f }) return new HConst((long)(uint)BitConverter.SingleToInt32Bits(f), _long);
            if ((SingleBits(e) ?? BitCast(e, _int)) is { } asInt)
                return new HConv(HConvKind.U8, new HConv(HConvKind.U4, asInt) { Type = _uint }) { Type = _ulong };
            Problem("float reinterpreted as bits (no BitConverter in this build)");
            return Site(new HOpaque("float_bits", e) { Type = _long }, "float reinterpreted as bits (no BitConverter in this build)");
        }
        if (ReferenceEquals(t, _double))
        {
            if (e is HConst { Value: double d }) return new HConst(BitConverter.DoubleToInt64Bits(d), _long);
            if (BitConverterMethod("DoubleToInt64Bits", _double) is { } toBits) return new HCall { Method = toBits, Arguments = [e], Type = _long };
            if (BitCast(e, _long) is { } asLong) return asLong;
            Problem("double reinterpreted as bits (no BitConverter in this build)");
            return Site(new HOpaque("double_bits", e) { Type = _long }, "double reinterpreted as bits (no BitConverter in this build)");
        }
        if (e is HConst { Value: int or long or bool } c)
        {
            long v = c.Value is bool b ? (b ? 1 : 0) : Convert.ToInt64(c.Value);
            return new HConst(size >= 8 ? v : v & ((1L << (size * 8)) - 1), _long);
        }
        if (size >= 8) return e;
        HConvKind narrow = size switch { 1 => HConvKind.U1, 2 => HConvKind.U2, _ => HConvKind.U4 };
        TypeSig narrowType = size switch { 1 => _byte, 2 => _ushort, _ => _uint };
        return new HConv(HConvKind.U8, new HConv(narrow, e) { Type = narrowType }) { Type = _ulong };
    }

    /// <summary>The value a field of the given type has when its bytes are <paramref name="bits"/> (an integer of the field's width).</summary>
    private HExpr ValueFromBits(HExpr bits, TypeSig type, int size)
    {
        if (ReferenceEquals(type, _float))
        {
            if (bits is HConst { Value: int or long } c) return new HConst(BitConverter.Int32BitsToSingle((int)Convert.ToInt64(c.Value)), _float);
            {
                // The bits of a float, read as a float again, are that float.
                HExpr narrow = Shortened(HConvKind.I4, _int, bits, 32);
                if (IsReinterpreted(narrow, "SingleToInt32Bits", "ToInt32", out HExpr original) && ReferenceEquals(original.Type, _float)) return original;
                if ((SingleFromBits(narrow) ?? BitCast(narrow, _float)) is { } asFloat) return asFloat;
            }
            Problem("bits reinterpreted as float (no BitConverter in this build)");
            return Site(new HOpaque("bits_to_float", bits) { Type = _float }, "bits reinterpreted as float (no BitConverter in this build)");
        }
        if (ReferenceEquals(type, _double))
        {
            if (bits is HConst { Value: int or long } c) return new HConst(BitConverter.Int64BitsToDouble(Convert.ToInt64(c.Value)), _double);
            if (BitConverterMethod("Int64BitsToDouble", _long) is { } fromBits) return new HCall { Method = fromBits, Arguments = [bits], Type = _double };
            // The bits of a double, read as a double again, are that double.
            if (!NoBitCasts && IsReinterpreted(bits, "DoubleToInt64Bits", "", out HExpr original) && ReferenceEquals(original.Type, _double)) return original;
            if (BitCast(BitsOf(bits.Type) == 64 ? bits : new HConv(HConvKind.U8, bits) { Type = _ulong }, _double) is { } asDouble) return asDouble;
            Problem("bits reinterpreted as double (no BitConverter in this build)");
            return Site(new HOpaque("bits_to_double", bits) { Type = _double }, "bits reinterpreted as double (no BitConverter in this build)");
        }
        if (bits is HConst { Value: int or long } k)
        {
            long v = Convert.ToInt64(k.Value);
            if (ReferenceEquals(type, _bool)) return new HConst((v & 0xFF) != 0, _bool);
            if (IsReference(type)) return v == 0 ? new HConst(null, type) : bits;
            return size switch
            {
                1 => new HConst(IsSignedSmall(type) ? (int)(sbyte)v : (int)(byte)v, type),
                2 => new HConst(IsSignedSmall(type) ? (int)(short)v : (int)(ushort)v, type),
                4 => new HConst((int)v, type),
                _ => new HConst(v, type),
            };
        }
        if (ReferenceEquals(type, _bool))
        {
            // The byte a truth value was made into is that truth value.
            HExpr low = Shortened(HConvKind.U1, _byte, bits, 8);
            if (low is HConv { Kind: HConvKind.U1, Operand: { } truth } && ReferenceEquals(truth.Type, _bool)) return truth;
            return new HCompare(HCompareOp.Ne, low, new HConst(0, _int)) { Type = _bool };
        }
        if (size >= 8) return bits;
        bool signed = IsSignedSmall(type);
        HConvKind kind = (size, signed) switch
        {
            (1, true) => HConvKind.I1, (1, false) => HConvKind.U1, (2, true) => HConvKind.I2, (2, false) => HConvKind.U2,
            (_, true) => HConvKind.I4, _ => HConvKind.U4,
        };
        return Shortened(kind, type, bits, size * 8);
    }

    /// <summary>
    /// A conversion to an integer of 32 bits or fewer, of something that was only just made wider: the widening
    /// changes none of the bits that are kept, so it is left out.
    /// </summary>
    private HExpr Shortened(HConvKind kind, TypeSig type, HExpr e, int bits)
    {
        if (bits <= 32)
        {
            for (int guard = 0; guard < 4; guard++)
            {
                if (e is HConv { Kind: HConvKind.U8 or HConvKind.I8, Operand: { } narrower } && BitsOf(narrower.Type) is > 0 and <= 32 && !IsFloat(narrower.Type)) e = narrower;
                else if (e is HConv { Kind: HConvKind.U4 or HConvKind.I4, Operand: { } same } && BitsOf(same.Type) == 32 && !IsFloat(same.Type)) e = same;
                else break;
            }
        }
        if (ReferenceEquals(e.Type, type) && BitsOf(type) == bits) return e;
        return new HConv(kind, e) { Type = type };
    }

    /// <summary>How many of the low bits of a value made wider without its sign can be set; 0 when that is not known.</summary>
    private int UnsignedWidth(HExpr e)
    {
        if (e is not HConv { Kind: HConvKind.U8, Operand: { } inner }) return 0;
        if (inner is HConv { Kind: HConvKind.U1 }) return 8;
        if (inner is HConv { Kind: HConvKind.U2 }) return 16;
        if (inner is HConv { Kind: HConvKind.U4 }) return 32;
        if (IsFloat(inner.Type)) return 0;
        if (ReferenceEquals(inner.Type, _bool) || ReferenceEquals(inner.Type, _byte)) return 8;
        if (ReferenceEquals(inner.Type, _ushort) || inner.Type is PrimitiveSig { Element: Il2CppTypeEnum.Char }) return 16;
        return BitsOf(inner.Type) is > 0 and <= 32 ? 32 : 0;
    }

    /// <summary>
    /// A number put together from parts ("a | (b &lt;&lt; 32)"), taken apart: each part's bits and the bit they
    /// start at. False when the number is not written that way.
    /// </summary>
    private bool TermsOf(HExpr e, int shift, List<(HExpr Bits, int At, int Width)> terms)
    {
        switch (e)
        {
            case HBinary { Op: HBinaryOp.Or } both when BitsOf(both.Type) == 64:
                return TermsOf(both.Left, shift, terms) && TermsOf(both.Right, shift, terms);
            case HBinary { Op: HBinaryOp.Shl, Right: HConst { Value: int by } } moved when BitsOf(moved.Type) == 64 && by is > 0 and < 64 && shift + by < 64:
                return TermsOf(moved.Left, shift + by, terms);
            case HConst { Value: long or int } c:
            {
                ulong v = (ulong)Convert.ToInt64(c.Value);
                if (v == 0) return true;
                int high = 64 - System.Numerics.BitOperations.LeadingZeroCount(v);
                // (What would be moved out at the top is not there afterwards: such a part is not one.)
                if (shift + high > 64) return false;
                terms.Add((e, shift, high));
                return true;
            }
            default:
                if (UnsignedWidth(e) is > 0 and var width && shift + width <= 64)
                {
                    terms.Add((e, shift, width));
                    return true;
                }
                return false;
        }
    }

    /// <summary>
    /// Bits [from, from + width) of a number put together from parts, moved down to bit 0: the parts that lie
    /// elsewhere are left out. Null when the number is not of that shape, a part lies across the lower end, or
    /// nothing would be left out.
    /// </summary>
    private HExpr? PartOfCombined(HExpr wide, int from, int width)
    {
        if (wide is HConst) return null;
        var terms = new List<(HExpr Bits, int At, int Width)>();
        if (!TermsOf(wide, 0, terms)) return null;
        HExpr? result = null;
        bool less = from != 0;
        foreach (var (bits, at, size) in terms)
        {
            if (at + size <= from || at >= from + width)
            {
                if (!IsPure(bits)) return null;
                less = true;
                continue;
            }
            if (at < from) return null;
            HExpr moved = at == from ? bits
                : bits is HConst { Value: long or int } c ? new HConst(Convert.ToInt64(c.Value) << (at - from), _long)
                : new HBinary(HBinaryOp.Shl, bits, new HConst(at - from, _int)) { Type = _long };
            result = result == null ? moved : new HBinary(HBinaryOp.Or, result, moved) { Type = _long };
        }
        if (!less) return null;
        return result ?? new HConst(0L, _long);
    }

    /// <summary>
    /// Values that travel together, moved down by a number of bytes: the ones that lay above, where they then
    /// are. Null when one of them lies across the cut.
    /// </summary>
    private Sem? MovedDown(List<Part> parts, int bytes)
    {
        var left = new List<Part>();
        foreach (Part p in parts)
        {
            if (p.Offset + p.Size <= bytes)
            {
                if (!IsPure(p.Value)) return null;
                continue;
            }
            if (p.Offset < bytes) return null;
            left.Add(new Part(p.Offset - bytes, p.Size, p.Value));
        }
        if (left.Count == 0) return new SVal(new HConst(0L, _long));
        return new SParts(left, 8);
    }

    /// <summary>The integer that a run of parts forms when read as one number.</summary>
    private HExpr CombineParts(IReadOnlyList<Part> parts, int totalSize)
    {
        HExpr? result = null;
        // Constants side by side are one constant.
        if (parts.Count != 0 && parts.All(p => p.Value is HConst { Value: int or long or bool or float } && p.Size is >= 1 and <= 8 && p.Offset is >= 0 and < 8))
        {
            ulong folded = 0;
            bool constant = true;
            foreach (Part p in parts)
            {
                if (BitsOfValue(p.Value, p.Size) is not HConst { Value: long piece }) { constant = false; break; }
                ulong masked = p.Size >= 8 ? (ulong)piece : (ulong)piece & ((1UL << (p.Size * 8)) - 1);
                folded |= masked << (p.Offset * 8);
            }
            if (constant) return new HConst((long)folded, _long);
        }
        foreach (Part p in parts)
        {
            if (IsReference(p.Value.Type) && totalSize > p.Size)
                Problem("a reference used as part of a wider number");
            HExpr bits = BitsOfValue(p.Value, p.Size);
            if (p.Offset != 0) bits = new HBinary(HBinaryOp.Shl, bits, new HConst(p.Offset * 8, _int)) { Type = _long };
            result = result == null ? bits : new HBinary(HBinaryOp.Or, result, bits) { Type = _long };
        }
        return result ?? new HConst(0L, _long);
    }

    /// <summary>The bits of a wide integer expression that belong to one part.</summary>
    private HExpr ExtractPart(HExpr wide, int offset, int size, TypeSig type)
    {
        if (wide is HConst { Value: int or long } c)
        {
            long v = Convert.ToInt64(c.Value);
            long bits = offset >= 8 ? 0 : (long)((ulong)v >> (offset * 8));
            if (size < 8) bits &= (1L << (size * 8)) - 1;
            return ValueFromBits(new HConst(bits, _long), type, size);
        }
        // Of a number put together from parts, only the parts that lie there.
        if (size < 8 && PartOfCombined(wide, offset * 8, size * 8) is { } only) return ValueFromBits(only, type, size);
        HExpr shifted = offset == 0 ? wide : new HBinary(HBinaryOp.ShrUn, wide, new HConst(offset * 8, _int)) { Type = _ulong };
        return ValueFromBits(shifted, type, size);
    }

    /// <summary>The 32 bits one lane of a vector register holds, as an integer expression.</summary>
    private HExpr HalfBits(Node lane)
    {
        Sem s = Eval(lane);
        if (s is SJunk) return new HConst(0, _int);
        if (s is SHalf { Part: null } half) return ExtractPart(BitsOfValue(half.Whole, 8), half.High ? 4 : 0, 4, _int);
        HExpr e = Value(lane);
        return IsFloat(e.Type) ? ExtractPart(BitsOfValue(e, 4), 0, 4, _int) : e;
    }

    /// <summary>
    /// The handle structs of reflection (what "ldtoken" pushes) are a single pointer to the runtime's own
    /// description of a type, method or field; code holds them as that pointer.
    /// </summary>
    private HExpr? HandleFromToken(Sem s, TypeSig structType)
    {
        string name = structType.Definition?.ReflectionName ?? "";
        switch (s)
        {
            case SType t when name == "System.RuntimeTypeHandle":
                return new HTypeExpr(HTypeOp.TypeToken, t.Type, null) { Type = structType };
            case SMethod m when name == "System.RuntimeMethodHandle":
                return new HMemberToken
                {
                    Method = m.Method,
                    DeclaringType = m.Inst is { ClassArguments.Length: > 0 } inst ? _m.Sigs.GenericInst(m.Method.DeclaringType, inst.ClassArguments) : null,
                    MethodArguments = m.Inst?.MethodArguments ?? [],
                    Type = structType,
                };
            case SFieldInfo f when name == "System.RuntimeFieldHandle":
                return new HMemberToken { Field = f.Field, Type = structType };
        }
        return null;
    }

    private static List<Part>? PartsOf(Sem s) => s switch
    {
        SPair p => [new Part(0, 4, p.Low), new Part(4, 4, p.High)],
        SParts ps => ps.Parts,
        _ => null,
    };

    private static readonly bool NoReferencePieces = Environment.GetEnvironmentVariable("REWIND_NO_REFERENCE_PIECES") != null;

    /// <summary>
    /// A reference written over the fields of a struct (two floats of a Vector3): no field of a struct holds a
    /// piece of a reference, so the memory is the struct's slot used again for another variable - on the stack,
    /// each lifetime gets its own memory (see StackSplitting). Until then, or anywhere else, it is a gap: cut into
    /// the fields, the reference came out as two numbers, and C# refuses them.
    /// </summary>
    private void MarkReferenceInPieces(Node store, Node valueNode)
    {
        // (A value typed only "object" says little: the bytes of a struct copied whose source was not known.)
        TypeSig? type = Eval(valueNode) switch { SVal v => v.Type, SNewObject o => o.Type, _ => null };
        if (NoReferencePieces || type == null || !IsReference(type) || type.Key == _object.Key) return;
        if (IsFrameAddress(store.In[0], out int at)) FrameConflicts.Add(FrameObjectAt(at) ?? at);
        Problem("a reference stored over the fields of a struct");
    }

    /// <summary>Assigns the bytes of a value to the fields a wide store covers.</summary>
    private void StoreParts(List<Part> leaves, Node valueNode, ulong address)
    {
        Sem s = Eval(valueNode);
        List<Part>? source = PartsOf(s);
        // Read every source before writing any destination: they may be the same struct.
        var assignments = new List<(HExpr Target, HExpr Value)>();
        HExpr? wide = null;
        foreach (Part leaf in leaves)
        {
            HExpr? value = null;
            if (source != null)
            {
                foreach (Part p in source)
                    if (p.Offset == leaf.Offset && p.Size == leaf.Size)
                    {
                        value = TypesAgree(p.Value.Type, leaf.Value.Type) ? Coerce(p.Value, leaf.Value.Type!) : ValueFromBits(BitsOfValue(p.Value, p.Size), leaf.Value.Type!, leaf.Size);
                        break;
                    }
            }
            if (value == null && source != null)
            {
                // The field is a piece of one of the values: only that one has a say in it.
                foreach (Part p in source)
                    if (p.Offset <= leaf.Offset && leaf.Offset + leaf.Size <= p.Offset + p.Size && !IsReference(p.Value.Type) && !IsStructType(p.Value.Type))
                    {
                        value = ExtractPart(BitsOfValue(p.Value, p.Size), leaf.Offset - p.Offset, leaf.Size, leaf.Value.Type!);
                        break;
                    }
            }
            if (value == null)
            {
                wide ??= source != null ? CombineParts(source, 8) : valueNode.IsConst ? new HConst((long)valueNode.UImm, _long) : IntValue(valueNode);
                value = ExtractPart(wide, leaf.Offset, leaf.Size, leaf.Value.Type!);
            }
            assignments.Add((leaf.Value, value));
        }
        foreach (var (target, value) in assignments) Emit(new HAssign(target, value), address);
    }

    private bool TypesAgree(TypeSig? a, TypeSig? b)
    {
        if (a == null || b == null) return a == null;
        if (ReferenceEquals(a, b)) return true;
        if (IsFloat(a) != IsFloat(b)) return false;
        if (IsReference(a) || IsReference(b)) return IsReference(a) && IsReference(b);
        return BitsOf(a) == BitsOf(b) && !IsStructType(a) && !IsStructType(b);
    }
}
