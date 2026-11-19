// Modified by xob0t (2026): gaps always marked, floating-point negation. See FORK.md.
using Rewind.Analysis.Abi;
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>
/// What the AArch64 calling convention adds: a struct of 9 to 16 bytes travels in two integer registers, and a
/// struct of one to four floats (or doubles) - a Vector3, a Quaternion, a Color - in one floating-point register
/// per member. Such a struct is rebuilt from its registers where it is passed or returned, and the registers a
/// method receives one in are its fields.
/// </summary>
public sealed partial class HirBuilder
{
    /// <summary>How the bytes of a struct are spread over the values carrying it.</summary>
    private enum Carried
    {
        /// <summary>Eight bytes per value: integer registers or stack slots.</summary>
        Words,
        /// <summary>One float member per value (lane 0 of a floating-point register).</summary>
        Floats,
        /// <summary>One double member per two values (lanes 0 and 1).</summary>
        Doubles,
    }

    /// <summary>
    /// The position an argument of a method has when the method is called through a function that is handed
    /// <paramref name="shift"/> more integer arguments first (an invoker: the slot, the object). Floating-point
    /// positions are counted apart from integer ones where the convention does so, and do not move.
    /// </summary>
    private int Shifted(AbiParam p, int shift)
    {
        RegisterModel regs = _fn.Regs;
        if (shift == 0 || regs.SharedPositions) return p.Position + shift;
        if (p.Role == ParamRole.ReturnBuffer) return p.Position; // x8 is no argument position
        if (p.Pass is PassKind.Float or PassKind.FloatAggregate && !regs.IsStackPosition(p.Position)) return p.Position;
        int r = regs.IntRegisterOf(p.Position);
        if (r >= 0)
        {
            int moved = r + shift;
            return moved < 8 ? moved : regs.FirstStackPosition + (moved - 8);
        }
        return p.Position + shift;
    }

    /// <summary>Position of the i-th of a C function's leading floating-point arguments.</summary>
    private int FloatArgPosition(int i) => _fn.Regs.SharedPositions ? i : _fn.Regs.FirstFloatPosition + i;

    /// <summary>Position of an integer argument of a C function that comes after <paramref name="ints"/> integer and <paramref name="floats"/> floating-point ones.</summary>
    private int IntArgPosition(int ints, int floats) => _fn.Regs.SharedPositions ? ints + floats : ints;

    /// <summary>The values a pair or aggregate argument of a call arrives in, in byte order (lane 1 of a double after lane 0).</summary>
    private List<Node?> ArgumentRegisters(Node call, AbiParam p, int position, out Carried how)
    {
        RegisterModel regs = _fn.Regs;
        var nodes = new List<Node?>();
        if (regs.IsStackPosition(position))
        {
            how = Carried.Words;
            int first = regs.StackSlotOf(position);
            for (int k = 0; k < (p.Size + 7) / 8; k++) nodes.Add(Input(call, ArgSlotKind.Stack, first + k));
            return nodes;
        }
        if (p.Pass == PassKind.IntegerPair)
        {
            how = Carried.Words;
            int r = regs.IntRegisterOf(position);
            nodes.Add(Input(call, ArgSlotKind.IntReg, r));
            nodes.Add(Input(call, ArgSlotKind.IntReg, r + 1));
            return nodes;
        }
        how = p.IsDouble ? Carried.Doubles : Carried.Floats;
        int v = regs.FloatRegisterOf(position);
        for (int k = 0; k < p.Count; k++)
        {
            nodes.Add(Input(call, ArgSlotKind.FloatReg, (v + k) * 4));
            if (p.IsDouble) nodes.Add(Input(call, ArgSlotKind.FloatReg, (v + k) * 4 + 1));
        }
        return nodes;
    }

    /// <summary>A float or double from the lanes of a floating-point register (lane 1 only for a double).</summary>
    private HExpr FloatFromLanes(Node? lo, Node? hi, bool isDouble)
    {
        TypeSig type = isDouble ? _double : _float;
        if (lo == null) return Missing(type);
        if (!isDouble) return AsFloat(FloatValue(lo), type);
        if (Eval(lo) is SHalf { High: false } l && hi != null && Eval(hi) is SHalf { High: true } h && SameValue(l.Whole, h.Whole))
            return l.Whole;
        if (hi != null && SignedLanes(lo, hi) is { } signed) return signed;
        if (Eval(lo) is SVal { Expr: HConst { Value: int low } } && hi != null && Eval(hi) is SVal { Expr: HConst { Value: int high } })
            return new HConst(BitConverter.Int64BitsToDouble((long)(uint)high << 32 | (uint)low), _double);
        HExpr bits = CombineParts([new Part(0, 4, HalfBits(lo)), new Part(4, 4, hi != null ? HalfBits(hi) : new HConst(0, _int))], 8);
        return ValueFromBits(bits, _double, 8);
    }

    private static bool SameValue(HExpr a, HExpr b) =>
        ReferenceEquals(a, b) ||
        (a is HLocal la && b is HLocal lb && ReferenceEquals(la.Variable, lb.Variable)) ||
        (a is HArg aa && b is HArg ab && aa.Index == ab.Index) ||
        (a is HField fa && b is HField fb && ReferenceEquals(fa.Field, fb.Field) && (fa.Object == null ? fb.Object == null : fb.Object != null && SameValue(fa.Object, fb.Object)));

    /// <summary>The scalar fields of a struct, as locations under <paramref name="owner"/>; null when they cannot be told apart.</summary>
    private List<Part>? StructLeaves(HExpr owner, TypeSig structType, int offset, int size)
    {
        var leaves = new List<Part>();
        return Leaves(owner, structType, offset, size, 0, leaves) && leaves.Count != 0 ? leaves : null;
    }

    /// <summary>Whether the leaves fit the way the struct is carried (no field split between two values).</summary>
    private static bool Fits(List<Part> leaves, Carried how, int values)
    {
        foreach (Part leaf in leaves)
        {
            if (how == Carried.Words)
            {
                if (leaf.Offset / 8 != (leaf.Offset + leaf.Size - 1) / 8 || leaf.Offset / 8 >= values) return false;
                continue;
            }
            int member = how == Carried.Doubles ? 8 : 4;
            if (leaf.Size != member || leaf.Offset % member != 0) return false;
            if ((how == Carried.Doubles ? 2 * (leaf.Offset / 8) + 1 : leaf.Offset / 4) >= values) return false;
        }
        return true;
    }

    /// <summary>
    /// A struct rebuilt from the registers (or stack slots) it is handed over in. Where every field comes from
    /// the same struct at the same place, that struct is the value; otherwise a temporary is filled field by field.
    /// </summary>
    private HExpr StructFromRegisters(IReadOnlyList<Node?> nodes, TypeSig structType, Carried how, ulong address)
    {
        TypeLayout layout = _p.Layouts.Of(structType);
        HVar whole = _h.NewLocal(structType, "s");
        whole.AddressTaken = true;
        var target = new HLocal(whole) { Type = structType };
        List<Part>? leaves = layout.Known && layout.Size > 0 ? StructLeaves(target, structType, 0, layout.Size) : null;
        if (leaves == null || !Fits(leaves, how, nodes.Count))
        {
            _h.Locals.Remove(whole);
            string fromRegisters = $"could not rebuild {structType.DisplayName} from its registers";
            Problem(fromRegisters);
            return Site(new HOpaque("struct_from_registers") { Type = structType }, fromRegisters);
        }

        // The sources of the fields, where each one is known on its own.
        HExpr? SourceOf(Part leaf)
        {
            if (how == Carried.Words)
            {
                Node? word = nodes[leaf.Offset / 8];
                if (word == null || PartsOf(Eval(word)) is not { } parts) return null;
                int at = leaf.Offset % 8;
                foreach (Part p in parts)
                    if (p.Offset == at && p.Size == leaf.Size)
                        return p.Value;
                return null;
            }
            if (how == Carried.Floats)
                return nodes[leaf.Offset / 4] is { } lane && Eval(lane) is SVal { Expr: var e } ? e : null;
            int member = leaf.Offset / 8;
            return nodes[2 * member] is { } lo && Eval(lo) is SHalf { High: false } half ? half.Whole : null;
        }

        // Handed on as it came: the struct itself.
        HExpr? root = null;
        bool same = true;
        foreach (Part leaf in leaves)
        {
            HExpr? source = SourceOf(leaf);
            if (source == null) { same = false; break; }
            HExpr t = leaf.Value, s = source;
            while (t is HField ft && s is HField fs && ReferenceEquals(ft.Field, fs.Field) && ft.Object != null && fs.Object != null)
            {
                t = ft.Object;
                s = fs.Object;
            }
            if (!ReferenceEquals(t, target) && !(t is HLocal tl && ReferenceEquals(tl.Variable, whole))) { same = false; break; }
            if (root == null) root = s;
            else if (!SameValue(root, s)) { same = false; break; }
        }
        if (same && root?.Type is { } rootType && rootType.Key == structType.Key)
        {
            _h.Locals.Remove(whole);
            return root;
        }

        if (how == Carried.Words)
        {
            for (int word = 0; word < nodes.Count; word++)
            {
                var mine = leaves.Where(l => l.Offset / 8 == word).Select(l => l with { Offset = l.Offset - 8 * word }).ToList();
                if (mine.Count == 0) continue;
                if (nodes[word] is not { } n)
                {
                    foreach (Part l in mine) Emit(new HAssign(l.Value, Missing(l.Value.Type!)), address);
                    continue;
                }
                StoreParts(mine, n, address);
            }
        }
        else
        {
            foreach (Part leaf in leaves)
            {
                HExpr value = how == Carried.Doubles
                    ? FloatFromLanes(nodes[2 * (leaf.Offset / 8)], nodes[2 * (leaf.Offset / 8) + 1], true)
                    : FloatFromLanes(nodes[leaf.Offset / 4], null, false);
                Emit(new HAssign(leaf.Value, Coerce(value, leaf.Value.Type!)), address);
            }
        }
        return new HLocal(whole) { Type = structType };
    }

    /// <summary>
    /// The registers a pair or aggregate parameter arrives in hold its fields: the first eight bytes and the rest
    /// (a pair), or one member each (an aggregate).
    /// </summary>
    private void BindRegisterStruct(AbiParam p, HExpr arg)
    {
        RegisterModel regs = _fn.Regs;
        TypeSig type = p.Type!;
        int size = _p.Layouts.SizeOf(type).Size;
        if (p.Pass == PassKind.IntegerPair)
        {
            int r = regs.IntRegisterOf(p.Position);
            for (int word = 0; word < 2; word++)
            {
                if (r + word >= regs.IntArgs.Length || !_fn.Params.TryGetValue(regs.IntArgs[r + word], out Node? reg)) continue;
                List<Part>? leaves = StructLeaves(arg, type, 8 * word, Math.Min(8, size - 8 * word));
                _sem[reg] = leaves != null ? new SParts(leaves, 8) : SJunk.Instance;
            }
            return;
        }
        int v = regs.FloatRegisterOf(p.Position);
        List<Part>? members = StructLeaves(arg, type, 0, size);
        if (members == null || !Fits(members, p.IsDouble ? Carried.Doubles : Carried.Floats, p.Count * (p.IsDouble ? 2 : 1))) return;
        foreach (Part member in members)
        {
            int k = member.Offset / (p.IsDouble ? 8 : 4);
            int lane0 = regs.FloatLane(v + k, 0);
            if (p.IsDouble)
            {
                if (_fn.Params.TryGetValue(lane0, out Node? lo)) _sem[lo] = new SHalf(member.Value, false, null);
                if (_fn.Params.TryGetValue(lane0 + 1, out Node? hi)) _sem[hi] = new SHalf(member.Value, true, null);
            }
            else if (_fn.Params.TryGetValue(lane0, out Node? lane)) _sem[lane] = new SVal(member.Value);
        }
    }

    private static readonly int[] FloatResultLane0 = [CallResult.FloatLane0, CallResult.Float1Lane0, CallResult.Float2Lane0, CallResult.Float3Lane0];
    private static readonly int[] FloatResultLane1 = [CallResult.FloatLane1, CallResult.Float1Lane1, CallResult.Float2Lane1, CallResult.Float3Lane1];

    /// <summary>A call's result that comes back in x0 and x1, or one member per floating-point register: the registers are its fields.</summary>
    private void FinishRegisterStruct(Node call, HExpr expr, ReturnKind kind, TypeSig returnType)
    {
        Dictionary<int, Node> projs = Projections(call);
        int[] wanted = kind == ReturnKind.StructInRegisterPair ? [CallResult.IntReturn, CallResult.IntReturn2] : [.. FloatResultLane0, .. FloatResultLane1];
        if (!wanted.Any(w => projs.TryGetValue(w, out Node? p) && IsUsed(p)))
        {
            Emit(new HEval(expr), call.Addr);
            return;
        }
        HVar t = _h.NewLocal(returnType, "t");
        t.AddressTaken = true;
        Emit(new HAssign(new HLocal(t) { Type = returnType }, expr), call.Addr);
        int size = _p.Layouts.SizeOf(returnType).Size;
        if (kind == ReturnKind.StructInRegisterPair)
        {
            for (int word = 0; word < 2; word++)
            {
                if (!projs.TryGetValue(word == 0 ? CallResult.IntReturn : CallResult.IntReturn2, out Node? reg)) continue;
                List<Part>? leaves = StructLeaves(new HLocal(t) { Type = returnType }, returnType, 8 * word, Math.Min(8, size - 8 * word));
                _sem[reg] = leaves != null ? new SParts(leaves, 8) : SJunk.Instance;
            }
            return;
        }
        List<Part>? members = StructLeaves(new HLocal(t) { Type = returnType }, returnType, 0, size);
        if (members == null) return;
        bool isDouble = members[0].Size == 8;
        foreach (Part member in members)
        {
            int k = member.Offset / (isDouble ? 8 : 4);
            if (k >= 4 || member.Size != (isDouble ? 8 : 4)) continue;
            if (isDouble)
            {
                if (projs.TryGetValue(FloatResultLane0[k], out Node? lo)) _sem[lo] = new SHalf(member.Value, false, null);
                if (projs.TryGetValue(FloatResultLane1[k], out Node? hi)) _sem[hi] = new SHalf(member.Value, true, null);
            }
            else if (projs.TryGetValue(FloatResultLane0[k], out Node? lane)) _sem[lane] = new SVal(member.Value);
        }
    }
}
