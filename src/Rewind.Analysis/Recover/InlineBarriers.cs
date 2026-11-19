// Modified by xob0t (2026): static-field write barriers; card tables indexed from the image base, re-read flags, copied endings. See FORK.md.
using Rewind.Analysis.Ir;
using Rewind.Analysis.Passes;

namespace Rewind.Analysis.Recover;

public sealed partial class Normalizer
{
    private static readonly bool NoInlineBarriers = Environment.GetEnvironmentVariable("REWIND_NO_INLINE_BARRIERS") != null;

    /// <summary>
    /// A collector that keeps a card table has every store of a reference mark the card of the field it went into.
    /// Newer IL2CPP versions paste that marking in after the store instead of calling a write barrier: when a word
    /// of the runtime's own data says the collector is running incrementally, a short loop sets the field's bit in
    /// the table with "lock cmpxchg" ("table[(address >> 18) &amp; 0x7FFF] |= 1 &lt;&lt; ((address >> 12) &amp; 0x3F)").
    /// That is the runtime's bookkeeping, as the write barrier call is, and goes with its test: a region guarded by
    /// a test of a word at a fixed address of the image's data, that reads and changes memory only at fixed
    /// addresses of that data (changing it at least once at a place found by shifting a value right, a card), and
    /// that gives nothing to the code after it. After a store to a static field the card is that of the class's
    /// static data, read from the class.
    /// </summary>
    private bool RemoveInlineBarriers()
    {
        if (NoInlineBarriers) return false;
        bool changed = false, swept = false;
        var flags = new HashSet<Node>();
        foreach (Block guard in _fn.Blocks.ToList())
        {
            if (!_fn.Blocks.Contains(guard) || guard.Terminator is not { Op: Op.Branch } term || guard.Succs.Count != 2 ||
                ReferenceEquals(guard.Succs[0], guard.Succs[1]) || Function.IsTryEntry(term.In[0]) || !IsRuntimeFlagTest(Resolve(term.In[0])))
                continue;
            // (Registers the marking used are merged at the join until nothing reads them.)
            if (!swept)
            {
                DeadCode.Run(_fn);
                swept = true;
            }
            for (int side = 0; side < 2; side++)
            {
                Block entry = guard.Succs[side], join = guard.Succs[1 - side];
                HashSet<Block>? region = BarrierRegion(guard, entry, join);
                if (region == null) continue;
                if (FlagRead(Resolve(term.In[0])) is { } flag) flags.Add(flag);
                foreach (Block b in region)
                {
                    foreach (Node n in b.Phis) n.Dead = true;
                    foreach (Node n in b.Nodes) n.Dead = true;
                }
                foreach (Block b in region)
                    while (join.Preds.Contains(b)) RemoveEdge(b, join);
                foreach (Block b in region)
                {
                    b.Preds.Clear();
                    b.Succs.Clear();
                    _fn.Blocks.Remove(b);
                }
                MakeJump(guard, join);
                for (int i = 0; i < _fn.Blocks.Count; i++) _fn.Blocks[i].Id = i;
                DeadCode.Run(_fn);
                _result.RegionsRemoved++;
                changed = true;
                break;
            }
        }
        if (flags.Count != 0) DropFlagArguments(flags);
        return changed;
    }

    /// <summary>
    /// The runtime's word, read once for several markings, stays in its register after the last one and goes on
    /// to the next call in an argument register the callee does not take (a callee that took it would be handed
    /// it on purpose, and no managed code knows the word). There it is nothing: an undefined value, not a read.
    /// </summary>
    private void DropFlagArguments(HashSet<Node> flags)
    {
        bool any = false;
        foreach (Block b in _fn.Blocks)
            foreach (Node n in b.Nodes)
            {
                if (n.Dead || n.Op is not (Op.Call or Op.TailCall) || n.Aux is not CallInfo { Intrinsic: null } info) continue;
                for (int i = 0; i < n.In.Length && i < info.Slots.Count; i++)
                {
                    if (info.Slots[i].Kind != ArgSlotKind.IntReg) continue;
                    Node value = Resolve(n.In[i]);
                    while (value.Op is Op.ZExt or Op.SExt or Op.Trunc) value = Resolve(value.In[0]);
                    if (!flags.Contains(value)) continue;
                    n.In[i] = _fn.NewNode(Op.Undef, n.In[i].Type, null);
                    any = true;
                }
            }
        if (any) DeadCode.Run(_fn);
    }

    private static readonly bool BarrierDebug = Environment.GetEnvironmentVariable("REWIND_BARRIER_DEBUG") != null;

    /// <summary>The blocks from <paramref name="entry"/> to <paramref name="join"/> when they are a card marking.</summary>
    private HashSet<Block>? BarrierRegion(Block guard, Block entry, Block join)
    {
        HashSet<Block>? found = BarrierRegionCore(guard, entry, join, out string why);
        if (BarrierDebug) Console.Error.WriteLine($"barrier {guard} -> {entry} / {join}: {why}");
        return found;
    }

    private HashSet<Block>? BarrierRegionCore(Block guard, Block entry, Block join, out string why)
    {
        why = "shape";
        int guardIndex = join.Preds.IndexOf(guard);
        if (ReferenceEquals(entry, join) || entry.Preds.Count != 1 || guardIndex < 0) { why = $"shape: entry preds {entry.Preds.Count}, guard index {guardIndex}"; return null; }
        var region = new HashSet<Block>();
        var exits = new List<Node>();
        var work = new Stack<Block>();
        work.Push(entry);
        while (work.Count > 0)
        {
            Block b = work.Pop();
            if (ReferenceEquals(b, guard) || region.Count > 8) { why = "shape: back to the guard or too large"; return null; }
            if (!region.Add(b)) continue;
            if (b.Scope != guard.Scope) { why = "shape: another scope"; return null; }
            if (b.Succs.Count == 0)
            {
                // The marking neither returns nor throws, but the compiler may have copied the method's ending into
                // it: the last marking of a path then returns by itself (checked below against the join's ending).
                if (b.Terminator is not { Op: Op.Return } ret) { why = "shape: an exit"; return null; }
                exits.Add(ret);
            }
            foreach (Block next in b.Succs)
                if (!ReferenceEquals(next, join)) work.Push(next);
        }
        foreach (Block b in region)
            foreach (Block p in b.Preds)
                if (!region.Contains(p) && !(ReferenceEquals(b, entry) && ReferenceEquals(p, guard))) { why = $"shape: {b} entered from {p}"; return null; }

        bool marks = false;
        var defined = new HashSet<Node>();
        foreach (Block b in region)
        {
            defined.UnionWith(b.Phis.Where(n => !n.Dead));
            foreach (Node n in b.Nodes)
            {
                if (n.Dead) continue;
                defined.Add(n);
                switch (n.Op)
                {
                    case Op.Load:
                        // (Reads may also be of a class's own record: a static field's card is found from the
                        // class's static data, klass->static_fields.)
                        if (!AtRuntimeData(Resolve(n.In[0]), out _, classData: true)) return null;
                        break;
                    case Op.Store:
                    {
                        if (!AtRuntimeData(Resolve(n.In[0]), out bool card)) return null;
                        marks |= card;
                        break;
                    }
                    case Op.Call:
                    {
                        if (n.Aux is not CallInfo { Intrinsic: { } name } || !name.StartsWith("atomic_", StringComparison.Ordinal) ||
                            n.In.Length == 0 || !AtRuntimeData(Resolve(n.In[0]), out bool card))
                            return null;
                        marks |= card;
                        break;
                    }
                    case Op.Return when exits.Contains(n):
                        break;
                    case Op.Proj or Op.Jump or Op.Branch or Op.Const or Op.Add or Op.Sub or Op.Mul or Op.And or Op.Or or Op.Xor or
                        Op.Not or Op.Shl or Op.ShrU or Op.ShrS or Op.Rol or Op.Ror or Op.Trunc or Op.ZExt or Op.SExt or Op.Select or
                        Op.CmpEq or Op.CmpNe or Op.CmpLtU or Op.CmpLeU or Op.CmpLtS or Op.CmpLeS or Op.Flags:
                        break;
                    default:
                        why = "op " + n.Op;
                        return null;
                }
            }
        }
        why = "no card";
        if (!marks) return null;

        // Nothing after the region sees what it computed. A merge at the join may take a value the region computed for
        // itself: a register it left behind, handed on as a call's unused argument register (the code after the join
        // also runs without the region, so it cannot depend on that value). Anything else it takes from the region
        // must be what it takes from the guard.
        var uses = DeadCode.Uses(_fn);
        foreach (Node n in defined)
            if (uses.TryGetValue(n, out List<Node>? users))
                foreach (Node user in users)
                    if (!defined.Contains(user) && !(user.Op == Op.Phi && join.Phis.Contains(user))) { why = "used after: " + user.Op; return null; }
        foreach (Node phi in join.Phis)
        {
            if (phi.Dead || guardIndex >= phi.In.Length) continue;
            Node fromGuard = Resolve(phi.In[guardIndex]);
            for (int i = 0; i < join.Preds.Count && i < phi.In.Length; i++)
                if (region.Contains(join.Preds[i]) && !LeftBehind(Resolve(phi.In[i]), defined) && !SameValue(Resolve(phi.In[i]), fromGuard)) { why = $"join merge {phi.Type} {phi.Id}: {Resolve(phi.In[i]).Op} {Resolve(phi.In[i]).Id} vs {fromGuard.Op} {fromGuard.Id}, users " + string.Join(",", uses.GetValueOrDefault(phi, []).Select(u => u.Op + "@" + u.Block)); return null; }
        }
        // A copied ending returns what the way around the marking returns: the join must lead straight to a return,
        // and each value returned from the region is the same as the one returned that way, or one the region
        // computed for itself (a register it left behind, which the code without the region does not give either).
        if (exits.Count != 0)
        {
            if (TailReturn(join, guardIndex) is not { } around) { why = "copied ending: the join does not lead to a return"; return null; }
            foreach (Node ret in exits)
            {
                if (ret.In.Length != around.Count) { why = "copied ending: other values"; return null; }
                for (int i = 0; i < ret.In.Length; i++)
                {
                    Node value = Resolve(ret.In[i]);
                    if (!LeftBehind(value, defined) && !SameValue(value, around[i])) { why = $"copied ending: value {i} differs"; return null; }
                }
            }
        }
        why = "removed";
        return region;
    }

    /// <summary>
    /// A value the marking computed for itself: one of its own nodes, or an address in the image's data (the card
    /// table, whose address the compiler may keep in a register through the loop). No managed value is either.
    /// </summary>
    private bool LeftBehind(Node value, HashSet<Node> defined) =>
        defined.Contains(value) || value.IsConst && value.Imm != 0 && InRuntimeData((ulong)value.Imm);

    /// <summary>
    /// What a way into <paramref name="join"/> (as its pred number <paramref name="predIndex"/>) returns, when the
    /// join leads to a return through blocks that only merge and jump; null otherwise.
    /// </summary>
    private List<Node>? TailReturn(Block join, int predIndex)
    {
        var chain = new List<(Block Block, int Index)>();
        Block current = join;
        int index = predIndex;
        for (int steps = 0; steps < 6; steps++)
        {
            chain.Add((current, index));
            foreach (Node n in current.Nodes)
                if (!n.Dead && n.Op is not (Op.Jump or Op.Return)) return null;
            Node? term = current.Terminator;
            if (term is { Op: Op.Return })
            {
                var values = new List<Node>();
                foreach (Node input in term.In)
                {
                    Node v = Resolve(input);
                    for (int i = chain.Count - 1; i >= 0; i--)
                        if (v.Op == Op.Phi && chain[i].Block.Phis.Contains(v) && chain[i].Index < v.In.Length) v = Resolve(v.In[chain[i].Index]);
                    values.Add(v);
                }
                return values;
            }
            if (term is not { Op: Op.Jump } || current.Succs.Count != 1) return null;
            Block next = current.Succs[0];
            index = next.Preds.IndexOf(current);
            if (index < 0) return null;
            current = next;
        }
        return null;
    }

    /// <summary>"word == 0" or "word != 0" for a word at a fixed address of the image's data.</summary>
    private bool IsRuntimeFlagTest(Node condition) => FlagRead(condition) != null;

    /// <summary>The read of the runtime's word a flag test tests.</summary>
    private Node? FlagRead(Node condition)
    {
        if (condition.Op is not (Op.CmpEq or Op.CmpNe)) return null;
        Node a = Resolve(condition.In[0]), b = Resolve(condition.In[1]);
        if (a.IsConst) (a, b) = (b, a);
        if (!b.IsConst || b.Imm != 0) return null;
        for (int depth = 0; depth < 4 && a.Op is Op.Trunc or Op.ZExt or Op.SExt or Op.And; depth++)
        {
            if (a.Op == Op.And && !Resolve(a.In[1]).IsConst) return null;
            a = Resolve(a.In[0]);
        }
        if (a.Op == Op.Phi) return MergedFlagRead(a);
        return a.Op == Op.Load && Resolve(a.In[0]) is { IsConst: true } address && InRuntimeData((ulong)address.Imm) ? a : null;
    }

    /// <summary>
    /// After a marking the compiler reads the runtime's word again for the next store, and the next test takes the
    /// word merged from the way around the marking and the way through it: a merge of reads of one fixed address
    /// (through merges and widenings). The read standing for them is the first one.
    /// </summary>
    private Node? MergedFlagRead(Node phi)
    {
        Node? first = null;
        long address = 0;
        var seen = new HashSet<Node>();
        var work = new Stack<Node>();
        work.Push(phi);
        while (work.Count > 0)
        {
            Node v = Resolve(work.Pop());
            for (int depth = 0; depth < 4 && v.Op is Op.Trunc or Op.ZExt or Op.SExt; depth++) v = Resolve(v.In[0]);
            if (!seen.Add(v)) continue;
            if (seen.Count > 64) return null;
            if (v.Op == Op.Phi)
            {
                foreach (Node input in v.In) work.Push(input);
                continue;
            }
            if (v.Op != Op.Load || Resolve(v.In[0]) is not { IsConst: true } at || !InRuntimeData((ulong)at.Imm)) return null;
            if (first == null) (first, address) = (v, at.Imm);
            else if (at.Imm != address) return null;
        }
        return first;
    }

    /// <summary>
    /// An address made of a fixed address of the image's data and offsets (or a pointer read from such an address);
    /// <paramref name="card"/> when an offset is a value shifted right. With <paramref name="classData"/>, a class
    /// read from its metadata slot is such a base too.
    /// </summary>
    private bool AtRuntimeData(Node address, out bool card, int depth = 0, bool classData = false)
    {
        card = false;
        var terms = new List<Node>();
        var work = new Stack<Node>();
        work.Push(address);
        while (work.Count > 0)
        {
            Node t = Resolve(work.Pop());
            if (t.Op == Op.Add && terms.Count < 8)
            {
                work.Push(t.In[0]);
                work.Push(t.In[1]);
            }
            else terms.Add(t);
        }
        bool based = false;
        // (The constant parts count together: MSVC indexes a table of the image's data from the image base,
        // "[base + index*8 + offset]" with base = __ImageBase, so neither constant alone is in the data.)
        ulong constants = 0;
        bool anyConstant = false;
        foreach (Node t in terms)
            if (t.IsConst)
            {
                constants += (ulong)t.Imm;
                anyConstant = true;
            }
        if (anyConstant && InRuntimeData(constants)) based = true;
        foreach (Node t in terms)
        {
            if (t.IsConst)
            {
                if (InRuntimeData((ulong)t.Imm)) based = true;
            }
            else if (classData && t.Op == Op.SlotValue) based = true;
            else if (t.Op == Op.Load && depth < 2 && AtRuntimeData(Resolve(t.In[0]), out _, depth + 1, classData)) based = true;
            else if (ShiftsRight(t, 0)) card = true;
        }
        return based;
    }

    private bool ShiftsRight(Node n, int depth)
    {
        n = Resolve(n);
        if (n.Op is Op.ShrU or Op.ShrS && Resolve(n.In[1]) is { IsConst: true } shift && shift.Imm >= 6) return true;
        if (depth >= 6 || n.Op is not (Op.Mul or Op.Shl or Op.And or Op.Trunc or Op.ZExt or Op.SExt or Op.Add)) return false;
        return n.In.Any(input => ShiftsRight(input, depth + 1));
    }

    private bool InRuntimeData(ulong address) =>
        program.Model.Image.SectionAt(address) is { IsExecutable: false };
}
