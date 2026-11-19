using Iced.Intel;
using Rewind.Model;
using Decoder = Iced.Intel.Decoder;

namespace Rewind.Analysis.Runtime;

/// <summary>
/// Finds runtime support functions by the part they play in the compiled methods that call them, where no
/// signature library recognizes their code: a Unity version, or a build of one, that no library was made from.
///
/// The code of a support function changes from one Unity version to the next; what the compiled methods do with
/// it does not. The object allocator is the clearest case: it is handed the class of the object, read from that
/// class's metadata slot, and what it returns is handed straight on, as "this", to a constructor of that same
/// class. No other support function is used that way - the class initializer returns nothing, the array and box
/// makers' results are never constructed. Where one unrecognized function is used that way from many places and
/// no other comes near, it is the allocator. Likewise the metadata initializer is the function handed the address
/// of a metadata slot (all others are handed the slot's content), and nearly only that.
/// </summary>
public static class HelperRoles
{
    private static readonly bool NoRoles = Environment.GetEnvironmentVariable("REWIND_NO_HELPER_ROLES") != null;
    private static readonly bool NoInit = Environment.GetEnvironmentVariable("REWIND_NO_INIT_ROLE") != null;

    private const int MinimumEvidence = 10;
    private const int Margin = 3;
    private const int MaximumFunctionBytes = 0x8000;

    /// <summary>Adds what the calls show to <paramref name="helpers"/>; returns a line for the log, or null.</summary>
    public static string? Identify(Il2CppModel model, ModelCodeContext context, CodeIndex code, RuntimeHelpers helpers)
    {
        if (NoRoles || model.Image.Arch != Rewind.Binary.CpuArch.X64) return null;
        bool wantAllocator = !helpers.ByAddress.Values.Any(i => i.Kind == HelperKind.ObjectNew);
        bool wantResolver = !helpers.ByAddress.Values.Any(i => i.Kind == HelperKind.ResolveICall);
        bool wantInit = !NoInit && !helpers.ByAddress.Values.Any(i => i.Kind is HelperKind.MetadataInit or HelperKind.MetadataInitInline);
        if (!wantAllocator && !wantResolver && !wantInit) return null;

        var allocations = new Dictionary<ulong, int>();
        var resolutions = new Dictionary<ulong, int>();
        var initializations = new Dictionary<ulong, int>();
        var calls = new Dictionary<ulong, int>();
        var names = new Dictionary<ulong, bool>();
        foreach (ulong start in context.FunctionStarts)
        {
            if (!context.IsManaged(start)) continue;
            List<Instruction> body = Decode(model, context, start);
            TypeDef? klass = null;
            bool named = false, slot = false;
            int age = 0;
            for (int i = 0; i < body.Count; i++)
            {
                Instruction ins = body[i];
                // "mov rcx, [slot]": the class kept in a metadata slot, as the first argument.
                if (ins.Mnemonic == Mnemonic.Mov && ins.Op0Kind == OpKind.Register && ins.Op0Register == Register.RCX &&
                    ins.Op1Kind == OpKind.Memory && ins.IsIPRelativeMemoryOperand &&
                    model.ResolveUsageSlot(ins.IPRelativeMemoryAddress) is { Kind: UsageKind.TypeInfo, Type.Definition: { } definition })
                {
                    (klass, named, slot, age) = (definition, false, false, 0);
                    continue;
                }
                // "lea rcx, [text]": the name of an internal call ("UnityEngine.Transform::get_position_Injected(...)").
                if (ins.Mnemonic == Mnemonic.Lea && ins.Op0Kind == OpKind.Register && ins.Op0Register == Register.RCX && ins.IsIPRelativeMemoryOperand)
                {
                    ulong text = ins.IPRelativeMemoryAddress;
                    // (Or the address of a metadata slot, which only the metadata initializer is handed.)
                    bool isSlot = wantInit && model.ResolveUsageSlot(text) != null;
                    bool isName = false;
                    if (!isSlot && !names.TryGetValue(text, out isName)) names[text] = isName = NamesInternalCall(model, text);
                    (klass, named, slot, age) = (null, isName, isSlot, 0);
                    continue;
                }
                if (ins.Mnemonic == Mnemonic.Call && ins.Op0Kind == OpKind.NearBranch64)
                {
                    ulong target = ins.NearBranchTarget;
                    if (wantInit) calls[target] = calls.GetValueOrDefault(target) + 1;
                    bool unknown = age <= 4 && !context.IsManaged(target) && helpers.At(target) == null && helpers.At(code.ThunkTarget(target)) == null;
                    if (unknown && wantAllocator && klass != null && ConstructedAfter(model, body, i + 1, klass))
                        allocations[target] = allocations.GetValueOrDefault(target) + 1;
                    // (The name is also handed to what reports the method missing when that fails; only the resolver
                    // returns something, tested at once.)
                    if (unknown && wantResolver && named && i + 1 < body.Count && body[i + 1] is { Mnemonic: Mnemonic.Test, Op0Kind: OpKind.Register } check &&
                        check.Op0Register == Register.RAX)
                        resolutions[target] = resolutions.GetValueOrDefault(target) + 1;
                    if (unknown && wantInit && slot)
                        initializations[target] = initializations.GetValueOrDefault(target) + 1;
                    (klass, named, slot) = (null, false, false);
                    continue;
                }
                if (Writes(ins, Register.RCX)) (klass, named, slot) = (null, false, false);
                age++;
            }
        }

        if (Environment.GetEnvironmentVariable("REWIND_ROLES_DEBUG") != null)
        {
            foreach (var (what, map) in new[] { ("allocations", allocations), ("resolutions", resolutions), ("initializations", initializations) })
                Console.Error.WriteLine($"[roles] {what}: " + string.Join(", ", map.OrderByDescending(kv => kv.Value).Take(5).Select(kv => $"0x{kv.Key:X}={kv.Value}")));
            Console.Error.WriteLine($"[roles] names looked at {names.Count}, of them internal calls {names.Count(kv => kv.Value)}");
        }
        var found = new List<string>();
        if (wantAllocator && Clear(allocations) is { } allocator)
        {
            Add(helpers, code, allocator.Address, new HelperInfo(HelperKind.ObjectNew, 1, false, true, "il2cpp_codegen_object_new (by its use)"));
            found.Add($"the object allocator at 0x{allocator.Address:X} ({allocator.Count} allocations followed by a constructor of the same class)");
        }
        if (wantResolver && Clear(resolutions) is { } resolver)
        {
            Add(helpers, code, resolver.Address, new HelperInfo(HelperKind.ResolveICall, 1, false, true, "il2cpp_codegen_resolve_icall (by its use)"));
            found.Add($"the internal-call resolver at 0x{resolver.Address:X} (handed {resolver.Count} internal-call names)");
        }
        if (wantInit)
        {
            // Unity 6 has two (with and without the memory barrier after it, the one that returns the slot's
            // content and one that doesn't) and a function they both call; every one of them is the initializer.
            // Taken as the one that returns the content: where nothing reads the result that changes nothing.
            var initializers = initializations
                .Where(kv => kv.Value >= MinimumEvidence && kv.Value * 10 >= calls.GetValueOrDefault(kv.Key) * 9)
                .OrderBy(kv => kv.Key).ToList();
            foreach (var (address, _) in initializers)
                Add(helpers, code, address, new HelperInfo(HelperKind.MetadataInitInline, 1, false, true, "il2cpp_codegen_initialize_runtime_metadata (by its use)"));
            if (initializers.Count != 0)
                found.Add("the metadata initializer at " + string.Join(", ", initializers.Select(kv => $"0x{kv.Key:X}")) +
                          $" (handed metadata slot addresses {initializers.Sum(kv => kv.Value)} times)");
        }
        return found.Count == 0 ? null : "roles:    found by their use: " + string.Join("; ", found);
    }

    /// <summary>The one function with clearly the most evidence, when it has enough.</summary>
    private static (ulong Address, int Count)? Clear(Dictionary<ulong, int> evidence)
    {
        var ranked = evidence.OrderByDescending(kv => kv.Value).Take(2).ToList();
        if (ranked.Count == 0 || ranked[0].Value < MinimumEvidence) return null;
        if (ranked.Count > 1 && ranked[0].Value < Margin * ranked[1].Value) return null;
        return (ranked[0].Key, ranked[0].Value);
    }

    private static void Add(RuntimeHelpers helpers, CodeIndex code, ulong address, HelperInfo info)
    {
        helpers.Add(address, info);
        ulong onward = code.ThunkTarget(address);
        if (onward != address && onward != 0 && helpers.At(onward) == null) helpers.Add(onward, info);
    }

    /// <summary>Whether the text at the address is "Type::Method..." naming an internal-call method of the game.</summary>
    private static bool NamesInternalCall(Il2CppModel model, ulong address)
    {
        if (model.Image.SectionAt(address) is not { IsExecutable: false }) return false;
        if (model.Image.TryCString(address, 400) is not { Length: > 4 } text) return false;
        int split = text.IndexOf("::", StringComparison.Ordinal);
        if (split <= 0) return false;
        string rest = text[(split + 2)..];
        int open = rest.IndexOf('(');
        string method = open < 0 ? rest : rest[..open];
        const ushort InternalCall = 0x1000;
        return model.FindType(text[..split]) is { } type && type.Methods.Any(m => m.Name == method && (m.ImplFlags & InternalCall) != 0);
    }

    /// <summary>
    /// Whether, within a few instructions, what the call returned is handed as "this" to a constructor of the
    /// class: rax, or a register it was copied to, in rcx at a call to such a constructor.
    /// </summary>
    private static bool ConstructedAfter(Il2CppModel model, List<Instruction> body, int from, TypeDef klass)
    {
        var holding = new HashSet<Register> { Register.RAX };
        for (int i = from; i < body.Count && i < from + 12; i++)
        {
            Instruction ins = body[i];
            if (ins.Mnemonic == Mnemonic.Call)
            {
                if (ins.Op0Kind != OpKind.NearBranch64 || !holding.Contains(Register.RCX)) return false;
                ulong target = ins.NearBranchTarget;
                if (model.MethodsByAddress.TryGetValue(target, out List<MethodDef>? methods) &&
                    methods.Any(m => m.Name == ".ctor" && ReferenceEquals(m.DeclaringType, klass)))
                    return true;
                if (model.InstsByAddress.TryGetValue(target, out List<MethodInst>? insts) &&
                    insts.Any(m => m.Method.Name == ".ctor" && ReferenceEquals(m.Method.DeclaringType, klass)))
                    return true;
                return false;
            }
            if (ins.Mnemonic == Mnemonic.Mov && ins.Op0Kind == OpKind.Register && ins.Op1Kind == OpKind.Register)
            {
                Register to = ins.Op0Register.GetFullRegister(), source = ins.Op1Register.GetFullRegister();
                if (holding.Contains(source)) holding.Add(to);
                else holding.Remove(to);
                continue;
            }
            foreach (Register r in holding.ToList())
                if (Writes(ins, r))
                    holding.Remove(r);
            if (holding.Count == 0) return false;
        }
        return false;
    }

    /// <summary>Whether the instruction writes the register (as its first operand, the way nearly all do).</summary>
    private static bool Writes(in Instruction ins, Register full) =>
        ins.Op0Kind == OpKind.Register && ins.Op0Register.GetFullRegister() == full &&
        ins.Mnemonic is not (Mnemonic.Cmp or Mnemonic.Test or Mnemonic.Push);

    private static List<Instruction> Decode(Il2CppModel model, ModelCodeContext context, ulong start)
    {
        var list = new List<Instruction>();
        ulong end = context.NextFunctionStart(start);
        ulong length = end > start ? Math.Min(end - start, MaximumFunctionBytes) : 0x400;
        ReadOnlySpan<byte> bytes = model.Image.SpanToSectionEnd(start);
        if (bytes.Length == 0) return list;
        int take = (int)Math.Min((ulong)bytes.Length, length);
        var decoder = Decoder.Create(64, new ByteArrayCodeReader(bytes[..take].ToArray()), start);
        ulong stop = start + (ulong)take;
        while (decoder.IP < stop)
        {
            decoder.Decode(out Instruction ins);
            if (ins.IsInvalid) break;
            list.Add(ins);
        }
        return list;
    }
}
