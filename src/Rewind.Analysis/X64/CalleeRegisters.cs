// Added by xob0t (2026): the volatile registers a direct callee can change, read from its code. See FORK.md.
using System.Collections.Concurrent;
using System.Runtime.CompilerServices;
using Iced.Intel;
using Rewind.Binary;

namespace Rewind.Analysis.X64;

/// <summary>
/// Which of the Win64 volatile registers (rax, rcx, rdx, r8-r11, xmm0-xmm5) a direct call can change, read from
/// the callee's code. A compiler that sees the whole program (MSVC with LTCG) knows a callee of the same image
/// leaves some of them alone, IL2CPP's write barrier say, and keeps a value in one of them across the call; taking
/// every volatile register as lost there turns that value into an undefined one.
///
/// Every instruction reachable from the callee's entry is visited, following jumps out of the function and the
/// code of the functions it calls (a call comes back to the instruction after it): the registers any of them
/// write are the ones that can change. A pop counts as a write, so a register saved and restored counts as
/// changed. An indirect jump or call, code that cannot be decoded, or more code than the budget allows, and the
/// callee can change every one of them.
/// </summary>
public static class CalleeRegisters
{
    /// <summary>Bit i: general register i (rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8-r15); bit 16 + i: xmm i.</summary>
    public const uint Volatile = 0b1111_0000_0111u | 0b11_1111u << 16;
    public const int XmmBit = 16;

    private const int Budget = 4000;

    private static readonly ConditionalWeakTable<NativeImage, ConcurrentDictionary<ulong, uint>> Cache = new();

    /// <summary>The volatile registers a call to <paramref name="target"/> can change (<see cref="Volatile"/> when not known).</summary>
    public static uint Clobbered(NativeImage image, ulong target) =>
        Cache.GetOrCreateValue(image).GetOrAdd(target, t => Compute(image, t));

    private sealed class ImageReader(NativeImage image) : CodeReader
    {
        public ulong Position;
        public override int ReadByte() => image.IsMapped(Position) ? image.U8(Position++) : -1;
    }

    private static uint Compute(NativeImage image, ulong entry)
    {
        var reader = new ImageReader(image);
        var decoder = Decoder.Create(64, reader, entry);
        var info = new InstructionInfoFactory();
        var seen = new HashSet<ulong>();
        var work = new Stack<ulong>();
        work.Push(entry);
        uint written = 0;
        while (work.Count > 0)
        {
            ulong ip = work.Pop();
            while (seen.Add(ip))
            {
                if (seen.Count > Budget || image.SectionAt(ip) is not { IsExecutable: true }) return Volatile;
                reader.Position = ip;
                decoder.IP = ip;
                decoder.Decode(out Instruction ins);
                if (ins.IsInvalid) return Volatile;
                written |= Writes(ins, info);
                if ((written & Volatile) == Volatile) return Volatile;
                switch (ins.FlowControl)
                {
                    case FlowControl.Next:
                        break;
                    case FlowControl.ConditionalBranch:
                        work.Push(ins.NearBranchTarget);
                        break;
                    case FlowControl.UnconditionalBranch:
                        if (!IsNear(ins)) return Volatile;
                        ip = ins.NearBranchTarget;
                        continue;
                    case FlowControl.Call:
                        if (!IsNear(ins)) return Volatile;
                        work.Push(ins.NearBranchTarget);
                        break;
                    case FlowControl.Return:
                    case FlowControl.Interrupt:
                    case FlowControl.Exception:
                        goto nextPath;
                    default:
                        // Indirect jumps and calls, transactions: where they go is not known here.
                        return Volatile;
                }
                ip = ins.NextIP;
            }
            nextPath: ;
        }
        return written & Volatile;
    }

    private static bool IsNear(in Instruction ins) => ins.Op0Kind is OpKind.NearBranch64 or OpKind.NearBranch32 or OpKind.NearBranch16;

    private static uint Writes(in Instruction ins, InstructionInfoFactory factory)
    {
        switch (ins.Mnemonic)
        {
            // Clears only the upper halves of the ymm registers; their low 128 bits are what is tracked here.
            case Mnemonic.Vzeroupper:
                return 0;
            // Load the vector registers from memory without naming them.
            case Mnemonic.Vzeroall or Mnemonic.Fxrstor or Mnemonic.Fxrstor64 or Mnemonic.Xrstor or Mnemonic.Xrstor64 or
                Mnemonic.Xrstors or Mnemonic.Xrstors64:
                return Volatile;
        }
        uint mask = 0;
        foreach (UsedRegister used in factory.GetInfo(ins).GetUsedRegisters())
        {
            if (used.Access is not (OpAccess.Write or OpAccess.CondWrite or OpAccess.ReadWrite or OpAccess.ReadCondWrite)) continue;
            Register full = used.Register.GetFullRegister();
            if (full.IsGPR64()) mask |= 1u << (full - Register.RAX);
            else if (full.IsZMM() && full - Register.ZMM0 < 16) mask |= 1u << (XmmBit + (full - Register.ZMM0));
        }
        return mask;
    }
}
