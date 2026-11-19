using Iced.Intel;
using Rewind.Model;
using Decoder = Iced.Intel.Decoder;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// Finds runtime support functions whose own few instructions say what they are, where no signature library
/// recognized them.
/// </summary>
public static class HelperShapes
{
    private static readonly bool NoWidened = Environment.GetEnvironmentVariable("REWIND_NO_WIDENED_HELPERS") != null;

    /// <summary>Adds what the code shows to <paramref name="helpers"/>; returns a line for the log, or null.</summary>
    public static string? Identify(Il2CppModel model, ModelCodeContext context, CodeIndex code, RuntimeHelpers helpers)
    {
        if (model.Image.Arch != Rewind.Binary.CpuArch.X64) return null;
        var found = new List<string>();
        if (!NoWidened && AddWidenedTargets(model, context, code, helpers) is > 0 and var widened)
            found.Add($"{widened} called through a function that only widens arguments");
        return found.Count == 0 ? null : "shapes:   found by their code: " + string.Join("; ", found);
    }

    /// <summary>
    /// A support function can be a wrapper that does nothing but widen its 32-bit arguments to 64 bits and jump to
    /// the function that does the work: SZArrayNew(klass, uint32 length) is "mov edx, edx; jmp Array::NewSpecific".
    /// The library recognizes the wrapper, but code built with whole-program optimization mostly calls the function
    /// behind it, passing the length already widened. That function does what the wrapper does, for every argument
    /// the wrapper can pass on, and is the same helper. (Not where something else is known to be there, nor a
    /// compiled method, nor where the wrapper does anything but widen a register into itself.)
    /// </summary>
    private static int AddWidenedTargets(Il2CppModel model, ModelCodeContext context, CodeIndex code, RuntimeHelpers helpers)
    {
        int added = 0;
        foreach (var (address, info) in helpers.ByAddress.ToList())
        {
            if (info.Kind == HelperKind.None || WidenedJumpTarget(model, address) is not { } next) continue;
            ulong target = code.ThunkTarget(next);
            foreach (ulong at in new[] { next, target }.Distinct())
            {
                if (at == address || context.IsManaged(at) || helpers.At(at) != null) continue;
                helpers.Add(at, info with { Name = info.Name + " (the function it widens its arguments for)" });
                added++;
            }
        }
        return added;
    }

    /// <summary>Where the function jumps when all it does before is "mov r32, r32" of an argument register into itself.</summary>
    private static ulong? WidenedJumpTarget(Il2CppModel model, ulong start)
    {
        ReadOnlySpan<byte> bytes = model.Image.SpanToSectionEnd(start);
        if (bytes.Length == 0) return null;
        var decoder = Decoder.Create(64, new ByteArrayCodeReader(bytes[..Math.Min(bytes.Length, 64)].ToArray()), start);
        bool widens = false;
        for (int i = 0; i < 5; i++)
        {
            decoder.Decode(out Instruction ins);
            if (ins.IsInvalid) return null;
            if (ins.Mnemonic == Mnemonic.Jmp && ins.Op0Kind == OpKind.NearBranch64)
                return widens ? ins.NearBranchTarget : null;
            if (ins.Mnemonic != Mnemonic.Mov || ins.Op0Kind != OpKind.Register || ins.Op1Kind != OpKind.Register ||
                ins.Op0Register != ins.Op1Register || ins.Op0Register is not (Register.ECX or Register.EDX or Register.R8D or Register.R9D))
                return null;
            widens = true;
        }
        return null;
    }
}
