// Modified by xob0t (2026): byte-indexed two-level jump tables. See FORK.md.
using Iced.Intel;
using Rewind.Binary;

namespace Rewind.Analysis.X64;

/// <summary>InlinedCall: the block ends with a call whose target's code is lifted in place (see X64Lifter).</summary>
public enum BlockEnd { FallThrough, Jump, Branch, Switch, Return, TailCall, IndirectTailCall, NoReturnCall, Trap, InlinedCall }

public sealed class RawBlock
{
    public ulong Start;
    public List<Instruction> Instructions = [];
    public BlockEnd End;
    /// <summary>Successor addresses. For Branch: [taken, fall-through]. For Switch: one per table entry.</summary>
    public List<ulong> Successors = [];
    /// <summary>For Switch through a byte-indexed table: the address of the byte table (0 for a one-level table).</summary>
    public ulong SwitchByteTable;
    /// <summary>For Switch through a byte-indexed table: the address of the table of targets it indexes.</summary>
    public ulong SwitchTable;
    public ulong EndAddress => Instructions.Count == 0 ? Start : Instructions[^1].NextIP;
}

/// <summary>Facts about the surrounding program that function discovery needs.</summary>
public interface ICodeContext
{
    NativeImage Image { get; }
    /// <summary>True when <paramref name="address"/> starts some function (a jump to it leaves the current one).</summary>
    bool IsFunctionStart(ulong address);
    /// <summary>Smallest known function start greater than <paramref name="address"/>, or 0 when unknown.</summary>
    ulong NextFunctionStart(ulong address);
    /// <summary>True when a call to <paramref name="target"/> never returns.</summary>
    bool IsNoReturn(ulong target);
}

/// <summary>Decodes one x64 function by following control flow and splits it into basic blocks.</summary>
public sealed class X64Cfg
{
    public ulong Start;
    public ulong Limit;
    public List<RawBlock> Blocks = [];
    public List<string> Problems = [];

    private const int MaxInstructions = 200_000;

    public static X64Cfg Build(ICodeContext context, ulong start) => Build(context, start, null, null);

    /// <param name="extraLeaders">Addresses where a block must start even without a jump there (try state changes).</param>
    /// <param name="extraRoots">Addresses reached other than by the code's own control flow (catch continuations).</param>
    public static X64Cfg Build(ICodeContext context, ulong start, IEnumerable<ulong>? extraLeaders, IEnumerable<ulong>? extraRoots)
    {
        NativeImage image = context.Image;
        var cfg = new X64Cfg { Start = start };
        ImageSection? section = image.SectionAt(start);
        if (section == null || !section.IsExecutable)
        {
            cfg.Problems.Add($"0x{start:X} is not in an executable section");
            return cfg;
        }

        ulong limit = context.NextFunctionStart(start);
        if (limit == 0 || limit > section.End) limit = section.End;
        cfg.Limit = limit;

        ReadOnlySpan<byte> all = image.SpanToSectionEnd(start);
        int available = (int)Math.Min((ulong)all.Length, limit - start);
        byte[] code = all[..available].ToArray();

        var instructions = new SortedDictionary<ulong, Instruction>();
        var leaders = new HashSet<ulong> { start };
        var ends = new Dictionary<ulong, (BlockEnd End, List<ulong> Successors)>();
        var byteTables = new Dictionary<ulong, (ulong Bytes, ulong Table)>();
        var work = new Stack<ulong>();
        if (extraLeaders != null)
            foreach (ulong leader in extraLeaders)
                if (leader > start && leader < limit)
                    leaders.Add(leader);
        if (extraRoots != null)
            foreach (ulong root in extraRoots)
                if (root > start && root < limit)
                {
                    leaders.Add(root);
                    work.Push(root);
                }
        work.Push(start);

        bool InFunction(ulong a) => a >= start && a < limit && (a == start || !context.IsFunctionStart(a));

        var reader = new ByteArrayCodeReader(code);
        var decoder = Decoder.Create(64, reader, start);

        while (work.Count > 0)
        {
            ulong ip = work.Pop();
            while (true)
            {
                if (instructions.ContainsKey(ip)) break;
                if (ip < start || ip >= limit)
                {
                    cfg.Problems.Add($"control flow runs outside the function at 0x{ip:X}");
                    break;
                }
                if (instructions.Count > MaxInstructions)
                {
                    cfg.Problems.Add("function too large");
                    work.Clear();
                    break;
                }

                reader.Position = (int)(ip - start);
                decoder.IP = ip;
                decoder.Decode(out Instruction ins);
                if (ins.IsInvalid)
                {
                    cfg.Problems.Add($"invalid instruction at 0x{ip:X}");
                    ends[ip] = (BlockEnd.Trap, []);
                    instructions[ip] = ins;
                    break;
                }
                instructions[ip] = ins;
                ulong next = ins.NextIP;

                switch (ins.FlowControl)
                {
                    case FlowControl.ConditionalBranch:
                    {
                        ulong target = ins.NearBranchTarget;
                        if (!InFunction(target))
                        {
                            // A conditional jump out of the function: a conditional tail call. Rare; keep the
                            // fall-through path and note it.
                            cfg.Problems.Add($"conditional branch leaves the function at 0x{ip:X}");
                            ends[ip] = (BlockEnd.Branch, [target, next]);
                            leaders.Add(next);
                            work.Push(next);
                            goto nextBlock;
                        }
                        ends[ip] = (BlockEnd.Branch, [target, next]);
                        leaders.Add(target);
                        leaders.Add(next);
                        work.Push(next);
                        work.Push(target);
                        goto nextBlock;
                    }
                    case FlowControl.UnconditionalBranch:
                    {
                        ulong target = ins.NearBranchTarget;
                        if (ins.Op0Kind != OpKind.NearBranch64 || !InFunction(target))
                        {
                            ends[ip] = (BlockEnd.TailCall, []);
                            goto nextBlock;
                        }
                        ends[ip] = (BlockEnd.Jump, [target]);
                        leaders.Add(target);
                        work.Push(target);
                        goto nextBlock;
                    }
                    case FlowControl.IndirectBranch:
                    {
                        List<ulong>? table = TryReadJumpTable(image, instructions, ip, start, limit, out ulong bytesAt, out ulong tableAt);
                        if (table != null && bytesAt != 0) byteTables[ip] = (bytesAt, tableAt);
                        if (table == null)
                        {
                            ends[ip] = (BlockEnd.IndirectTailCall, []);
                        }
                        else
                        {
                            ends[ip] = (BlockEnd.Switch, table);
                            foreach (ulong t in table)
                            {
                                leaders.Add(t);
                                work.Push(t);
                            }
                        }
                        goto nextBlock;
                    }
                    case FlowControl.Return:
                        ends[ip] = (BlockEnd.Return, []);
                        goto nextBlock;
                    case FlowControl.Interrupt:
                    case FlowControl.Exception:
                        ends[ip] = (BlockEnd.Trap, []);
                        goto nextBlock;
                    case FlowControl.Call:
                    {
                        // Compilers put a trap after a call that cannot return; execution never reaches it.
                        bool trapFollows = next < limit && code[(int)(next - start)] == 0xCC;
                        if (context.IsNoReturn(ins.NearBranchTarget) || trapFollows)
                        {
                            ends[ip] = (BlockEnd.NoReturnCall, []);
                            goto nextBlock;
                        }
                        break;
                    }
                    case FlowControl.IndirectCall:
                    {
                        bool trapFollows = next < limit && code[(int)(next - start)] == 0xCC;
                        if (trapFollows)
                        {
                            ends[ip] = (BlockEnd.NoReturnCall, []);
                            goto nextBlock;
                        }
                        break;
                    }
                }
                ip = next;
                continue;

            nextBlock:
                break;
            }
        }

        // Split the decoded instructions into blocks at leaders and after terminators.
        RawBlock? current = null;
        ulong expected = 0;
        foreach (var (address, ins) in instructions)
        {
            if (current != null && (leaders.Contains(address) || address != expected))
            {
                if (address == expected)
                {
                    current.End = BlockEnd.FallThrough;
                    current.Successors = [address];
                }
                cfg.Blocks.Add(current);
                current = null;
            }
            current ??= new RawBlock { Start = address };
            current.Instructions.Add(ins);
            expected = ins.NextIP;
            if (ends.TryGetValue(address, out var end))
            {
                current.End = end.End;
                current.Successors = end.Successors;
                if (byteTables.TryGetValue(address, out var two)) (current.SwitchByteTable, current.SwitchTable) = two;
                cfg.Blocks.Add(current);
                current = null;
            }
        }
        if (current != null)
        {
            // Ran off the decoded region without a terminator (only after an error).
            current.End = BlockEnd.Trap;
            cfg.Blocks.Add(current);
        }

        // The entry block must be first.
        int entryIndex = cfg.Blocks.FindIndex(b => b.Start == start);
        if (entryIndex > 0)
        {
            RawBlock entry = cfg.Blocks[entryIndex];
            cfg.Blocks.RemoveAt(entryIndex);
            cfg.Blocks.Insert(0, entry);
        }
        return cfg;
    }

    /// <summary>Off (REWIND_NO_BYTE_JUMP_TABLES): a switch through a byte table of case indexes stays an indirect jump.</summary>
    private static readonly bool NoByteTables = Environment.GetEnvironmentVariable("REWIND_NO_BYTE_JUMP_TABLES") != null;

    /// <summary>
    /// Recognizes the MSVC jump table idiom ending in "jmp reg":
    ///   lea base, [image base] ... mov r32, [base + index*4 + tableRva] ; add r, base ; jmp r
    /// and returns the table's targets. Returns null when the indirect jump is not such a table.
    /// A switch whose cases share few bodies has two tables: a byte per case value giving the index into the table
    /// of targets, "movzx index, byte [base + value + bytesRva]" before the load. Its targets are returned per case
    /// value, and <paramref name="bytesAt"/> and <paramref name="tableAt"/> give the two tables' addresses (0 for a
    /// one-level table).
    /// </summary>
    private static List<ulong>? TryReadJumpTable(NativeImage image, SortedDictionary<ulong, Instruction> decoded,
        ulong jumpAddress, ulong start, ulong limit, out ulong bytesAt, out ulong tableAt)
    {
        bytesAt = 0;
        tableAt = 0;
        Instruction jump = decoded[jumpAddress];
        if (jump.Op0Kind != OpKind.Register) return null;
        Register target = jump.Op0Register;

        // Walk back over the instructions that were decoded just before the jump.
        var previous = new List<Instruction>();
        foreach (var (address, ins) in decoded.Reverse())
        {
            if (address >= jumpAddress) continue;
            previous.Add(ins);
            if (previous.Count == 24) break;
        }

        ulong tableRva = 0;
        bool found = false;
        int entrySize = 4;
        ulong imageBase = image.ImageBase;
        int loadAt = -1;
        for (int i = 0; i < previous.Count; i++)
        {
            Instruction ins = previous[i];
            if (ins.Mnemonic is Mnemonic.Mov or Mnemonic.Movsxd && ins.Op0Kind == OpKind.Register &&
                ins.Op0Register.GetFullRegister() == target.GetFullRegister() && ins.Op1Kind == OpKind.Memory &&
                ins.MemoryIndex != Register.None && ins.MemoryIndexScale == 4 && ins.MemoryBase != Register.None)
            {
                tableRva = ins.MemoryDisplacement64;
                found = true;
                loadAt = i;
                break;
            }
            // Any other write to the target register before we find the table load defeats the pattern,
            // except the "add target, base" that rebases the entry.
            if (ins.Op0Kind == OpKind.Register && ins.Op0Register.GetFullRegister() == target.GetFullRegister() &&
                ins.Mnemonic != Mnemonic.Add)
                return null;
        }
        if (!found) return null;

        ulong table = imageBase + tableRva;
        if (!image.IsMapped(table, entrySize)) return null;

        // The table load's index comes from a byte table: the last write of the index register before the load is
        // "movzx index32, byte [base + value + bytesRva]" (base and value in either order, unscaled).
        ulong bytes = 0;
        if (!NoByteTables)
        {
            Register slot = previous[loadAt].MemoryIndex.GetFullRegister();
            for (int i = loadAt + 1; i < previous.Count; i++)
            {
                Instruction ins = previous[i];
                if (ins.Op0Kind != OpKind.Register || ins.Op0Register.GetFullRegister() != slot ||
                    ins.Mnemonic is Mnemonic.Cmp or Mnemonic.Test) continue;
                if (ins.Mnemonic == Mnemonic.Movzx && ins.Op1Kind == OpKind.Memory && ins.MemorySize == MemorySize.UInt8 &&
                    ins.MemoryBase != Register.None && ins.MemoryIndex != Register.None && ins.MemoryIndexScale == 1 &&
                    ins.MemorySegment == Register.DS)
                    bytes = imageBase + ins.MemoryDisplacement64;
                break;
            }
        }

        // The bound comes from a preceding "cmp index, n ; ja default"; when it cannot be found, read entries
        // while they keep pointing into this function.
        int bound = -1;
        foreach (Instruction ins in previous)
        {
            if (ins.Mnemonic == Mnemonic.Cmp && ins.Op1Kind is OpKind.Immediate8 or OpKind.Immediate8to32 or OpKind.Immediate32
                    or OpKind.Immediate8to64 or OpKind.Immediate32to64)
            {
                bound = (int)ins.GetImmediate(1) + 1;
                break;
            }
        }

        if (bytes != 0)
        {
            // The bound is the number of case values: one byte each, every byte an index of a target in the function.
            if (bound <= 0 || bound > 4096 || !image.IsMapped(bytes, bound)) return null;
            var cases = new List<ulong>(bound);
            for (int i = 0; i < bound; i++)
            {
                ulong slotAt = table + (ulong)(image.U8(bytes + (ulong)i) * entrySize);
                if (!image.IsMapped(slotAt, entrySize)) return null;
                ulong entry = imageBase + image.U32(slotAt);
                if (entry < start || entry >= limit) return null;
                cases.Add(entry);
            }
            bytesAt = bytes;
            tableAt = table;
            return cases;
        }

        var targets = new List<ulong>();
        int max = bound > 0 && bound <= 4096 ? bound : 4096;
        for (int i = 0; i < max; i++)
        {
            ulong slot = table + (ulong)(i * entrySize);
            if (!image.IsMapped(slot, entrySize)) break;
            ulong entry = imageBase + image.U32(slot);
            if (entry < start || entry >= limit) break;
            targets.Add(entry);
        }
        if (targets.Count == 0) return null;
        if (bound > 0 && targets.Count != bound) return null;
        return targets;
    }
}
