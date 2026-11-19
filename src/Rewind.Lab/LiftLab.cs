// Modified by xob0t (2026): helpers behind widening wrappers. See FORK.md.
using System.Diagnostics;
using Iced.Intel;
using Rewind.Analysis;
using Rewind.Analysis.Ir;
using Rewind.Analysis.X64;
using Rewind.Model;

namespace Rewind.Lab;

/// <summary>Research commands for the machine-code lifter.</summary>
internal static class LiftLab
{
    /// <summary>lift &lt;input&gt; &lt;name filter&gt; [symbols.tsv]: prints the IR of matching methods.</summary>
    public static int Dump(Il2CppModel model, string filter, string? symbolsPath)
    {
        Dictionary<ulong, List<string>>? symbols = symbolsPath != null ? CallStats.LoadSymbols(model.Image, symbolsPath) : null;
        var context = new ModelCodeContext(model);
        IMachineLifter lifter = model.Image.Arch == Rewind.Binary.CpuArch.Arm64 ? new Rewind.Analysis.Arm64.A64Lifter(context) : new X64Lifter(context);
        int shown = 0;
        foreach (MethodDef method in model.Methods)
        {
            if (method.Address == 0 || !method.FullName.Contains(filter, StringComparison.Ordinal)) continue;
            Function fn = lifter.Lift(method.Address);
            Console.WriteLine($"=== {method.FullName}");
            Console.WriteLine(fn.Dump(n => Annotate(n, model, symbols)));
            if (++shown >= 12) break;
        }
        return 0;
    }

    public static ProgramAnalysis MakeProgram(Il2CppModel model, string symbolsPath)
    {
        // A ".sig" file is a signature library: the path every symbol-less game takes.
        if (symbolsPath.EndsWith(".sig", StringComparison.OrdinalIgnoreCase))
        {
            var context = new ModelCodeContext(model);
            context.DiscoverCallTargets();
            var index = new Rewind.Analysis.Runtime.CodeIndex(context);
            var library = Rewind.Analysis.Runtime.HelperLibrary.Load(symbolsPath);
            var matched = library.Match(index, model.Image, context.FunctionStarts.Where(a => !context.IsManaged(a)), out var report,
                context.FunctionStarts.Where(context.IsManaged));
            Console.WriteLine($"helpers from {Path.GetFileName(symbolsPath)}: {report}");
            // (As the decompiler does: functions named by the stubs they are called through.)
            int stubs = Rewind.Analysis.Runtime.HelperDiscovery.AddImportStubs(model.Image, matched);
            if (stubs != 0) Console.WriteLine($"helpers from import stubs: {stubs}");
            foreach (string line in Rewind.Analysis.Runtime.HelperDiscovery.Complete(model, context, index, matched)) Console.WriteLine(line);
            var watch = Stopwatch.StartNew();
            var analysis = new ProgramAnalysis(model, matched, context);
            Console.WriteLine($"exact copies: {analysis.ExactCopies.Copies.Count} of {analysis.ExactCopies.Examined} unlisted functions equal a listed method ({analysis.ExactCopies.Rounds} rounds); witnessed copies: {analysis.InlineCopies.Count}; near copies: {analysis.NearCopies.Count}; program analysis {watch.ElapsedMilliseconds} ms");
            return analysis;
        }
        Dictionary<ulong, List<string>> symbols = CallStats.LoadSymbols(model.Image, symbolsPath);
        var helpers = Rewind.Analysis.Runtime.RuntimeHelpers.FromSymbols(symbols,
            a => model.MethodsByAddress.ContainsKey(a) || model.InstsByAddress.ContainsKey(a));
        return new ProgramAnalysis(model, helpers);
    }

    /// <summary>hir &lt;input&gt; &lt;name filter&gt; &lt;symbols.tsv&gt;: the recovered high-level form of matching methods.</summary>
    /// <summary>
    /// frame-dump &lt;input&gt; &lt;symbols|sig&gt; &lt;out.tsv&gt;: for every method, the types recovery gave its stack memory
    /// (rva, offset from the entry stack pointer, size, type, clean) - to compare with the compiler's own records.
    /// </summary>
    public static int FrameDump(Il2CppModel model, string symbolsPath, string outPath)
    {
        ProgramAnalysis program = MakeProgram(model, symbolsPath);
        var pipeline = new Rewind.Analysis.Recover.MethodPipeline(program);
        ulong imageBase = model.Image.ImageBase;
        int methods = 0;
        using var writer = new StreamWriter(outPath);
        writer.WriteLine("rva	offset	size	type	clean	method");
        foreach (MethodDef method in model.Methods)
        {
            if (method.Address == 0) continue;
            Rewind.Analysis.Hir.HMethod h;
            try { h = pipeline.Recover(method); }
            catch { continue; }
            methods++;
            bool clean = h.Problems.Count == 0;
            if (h.FrameTypes.Count == 0) writer.WriteLine($"{method.Address - imageBase:X}				{(clean ? 1 : 0)}	{method.FullName}");
            foreach (var (offset, type) in h.FrameTypes.OrderBy(kv => kv.Key))
                writer.WriteLine($"{method.Address - imageBase:X}	{offset}	{program.Layouts.SizeOf(type).Size}	{type.DisplayName}	{(clean ? 1 : 0)}	{method.FullName}");
        }
        Console.WriteLine($"{methods} methods written to {outPath}");
        return 0;
    }

    /// <summary>
    /// marker-patterns &lt;input&gt; &lt;symbols|sig&gt; &lt;text&gt; [assembly]: the statements containing a marker (such as
    /// "__undefined"), with names and numbers blanked, by how many methods have them - to see the shapes behind a gap.
    /// </summary>
    public static int MarkerPatterns(Il2CppModel model, string symbolsPath, string marker, string? assembly)
    {
        ProgramAnalysis program = MakeProgram(model, symbolsPath);
        var pipeline = new Rewind.Analysis.Recover.MethodPipeline(program);
        var counts = new Dictionary<string, int>();
        var example = new Dictionary<string, string>();
        var name = new System.Text.RegularExpressions.Regex(@"(m|t|s|o|e|local|result)\d+");
        var number = new System.Text.RegularExpressions.Regex(@"-?\d+(\.\d+)?[LfF]?");
        int methods = 0;
        foreach (MethodDef method in model.Methods)
        {
            if (method.Address == 0 || (assembly != null && method.DeclaringType.Assembly.Name != assembly)) continue;
            // The same methods the decompiler gives bodies to.
            if (method.DeclaringType.GenericParameters.Length != 0 || method.GenericParameters.Length != 0 || !Rewind.Output.AssemblyEmitter.HasIlBody(method)) continue;
            Rewind.Analysis.Hir.HMethod h;
            try { h = pipeline.Recover(method); }
            catch { continue; }
            var seen = new HashSet<string>();
            foreach (var block in h.Blocks)
                foreach (var statement in block.Statements)
                {
                    string text = Rewind.Analysis.Hir.HirPrinter.Print(statement, h);
                    if (!text.Contains(marker, StringComparison.Ordinal)) continue;
                    string key = number.Replace(name.Replace(text, "v"), "N");
                    if (key.Length > 150) key = key[..150];
                    if (!seen.Add(key)) continue;
                    counts[key] = counts.GetValueOrDefault(key) + 1;
                    example.TryAdd(key, method.FullName);
                }
            if (seen.Count != 0) methods++;
        }
        Console.WriteLine($"{methods} methods have statements containing {marker}; {counts.Count} shapes");
        foreach (var (key, count) in counts.OrderByDescending(kv => kv.Value).Take(30))
            Console.WriteLine($"  {count,6}  {key}    e.g. {example[key]}");
        return 0;
    }

    /// <summary>copy-check &lt;input&gt; &lt;symbols|sig&gt; &lt;hex address&gt; &lt;hex original&gt;: the function at an address read as the listed method at another, next to that method's own code.</summary>
    public static int CopyCheck(Il2CppModel model, string symbolsPath, ulong address, ulong original)
    {
        ProgramAnalysis program = MakeProgram(model, symbolsPath);
        var pipeline = new Rewind.Analysis.Recover.MethodPipeline(program);
        var (method, own, copy, error) = pipeline.RecoverBoth(address, original);
        Console.WriteLine($"=== 0x{original:X} {method?.FullName}");
        if (error != null || own == null || copy == null) { Console.WriteLine("    " + error); return 1; }
        Console.WriteLine($"    own: {own.Problems.Count} problem(s) {string.Join(" | ", own.Problems.Distinct().Take(3))}");
        Console.WriteLine($"    as copy: {copy.Problems.Count} problem(s) {string.Join(" | ", copy.Problems.Distinct().Take(3))}");
        string[] a = Rewind.Analysis.Hir.HirPrinter.Canonical(own).Split('\n'), b = Rewind.Analysis.Hir.HirPrinter.Canonical(copy).Split('\n');
        int same = 0;
        while (same < a.Length && same < b.Length && a[same] == b[same]) same++;
        Console.WriteLine(same == a.Length && same == b.Length ? "    SAME CODE" : $"    first difference at line {same} of {a.Length}/{b.Length}:");
        for (int i = Math.Max(0, same - 4); i < Math.Min(Math.Max(a.Length, b.Length), same + 14); i++)
            Console.WriteLine($"      {(i < a.Length ? a[i].TrimEnd() : "-"),-90} | {(i < b.Length ? b[i].TrimEnd() : "-")}");
        return 0;
    }

    /// <summary>inline-why &lt;input&gt; &lt;symbols|sig&gt; &lt;hex address&gt;: each condition for lifting calls to a function in place.</summary>
    public static int InlineWhy(Il2CppModel model, string symbolsPath, ulong target)
    {
        ProgramAnalysis program = MakeProgram(model, symbolsPath);
        Console.WriteLine($"section {model.Image.SectionAt(target)?.Name}; noreturn {program.Context.NoReturn.Contains(target)}; helper {program.Helpers.At(target)?.Kind}");
        Console.WriteLine($"range {program.RangeOf(target)}; exception info {program.ExceptionInfo(target) != null}");
        var t = program.Resolve(target);
        Console.WriteLine($"resolve: managed {t.IsManaged} ({string.Join(", ", t.Methods.Select(m => m.FullName).Concat(t.Insts.Select(i => i.ToString())).Take(3))}) helper {t.Helper?.Kind}");
        Console.WriteLine($"should inline: {program.ShouldInline(target)}");
        return 0;
    }

    /// <summary>pinvoke &lt;input&gt; &lt;symbols|sig&gt;: what each P/Invoke declaration imports, read from its wrapper.</summary>
    public static int PInvoke(Il2CppModel model, string symbolsPath)
    {
        ProgramAnalysis program = MakeProgram(model, symbolsPath);
        int declarations = model.Methods.Count(m => (m.Flags & MethodDef.PInvokeImpl) != 0 && m.Address != 0);
        var imports = program.PInvokeDeclarations.ToList();
        Console.WriteLine($"{imports.Count} of {declarations} P/Invoke declarations with code read; {imports.Count(i => program.PInvokeAtSlot(i.CacheSlot) != null)} with a unique cache slot");
        foreach (var i in imports.Take(25))
            Console.WriteLine($"  {i.Method.FullName}: [DllImport(\"{i.Module}\", EntryPoint = \"{i.EntryPoint}\")] charset {i.CharSet} conv {i.CallingConvention} nomangle {i.NoMangle} lasterror {i.SetLastError} slot 0x{i.CacheSlot:X}");
        foreach (var m in model.Methods.Where(m => (m.Flags & MethodDef.PInvokeImpl) != 0 && m.Address != 0 && program.PInvokeOf(m) == null).Take(10))
            Console.WriteLine($"  NOT READ {m.FullName} @0x{m.Address:X}");
        return 0;
    }

    public static int Hir(Il2CppModel model, string filter, string symbolsPath, int max)
    {
        ProgramAnalysis program = MakeProgram(model, symbolsPath);
        var pipeline = new Rewind.Analysis.Recover.MethodPipeline(program);
        int shown = 0;
        if (Environment.GetEnvironmentVariable("REWIND_SPLIT_DEBUG") != null)
        {
            Rewind.Analysis.Passes.StackSplitting.Trace = text => Console.WriteLine("  [split] " + text);
            Rewind.Analysis.Passes.ExceptionStacks.Trace = text => Console.WriteLine("  [stack] " + text);
            Rewind.Analysis.Passes.LeaveTargets.Trace = text => Console.WriteLine("  [leave] " + text);
        }
        // Several methods at once: filters separated by '|'.
        string[] filters = filter.Split('|', StringSplitOptions.RemoveEmptyEntries);
        foreach (MethodDef method in model.Methods)
        {
            if (!filters.Any(f => method.FullName.Contains(f, StringComparison.Ordinal))) continue;
            if (method.Address == 0)
            {
                // A method of a generic class (or a generic method): only its instantiations have code.
                int instances = 0;
                foreach (MethodInst inst in program.InstsOf(method))
                {
                    if (inst.Address == 0) continue;
                    Console.WriteLine($"-- instantiation {inst} at 0x{inst.Address:X}");
                    try
                    {
                        Rewind.Analysis.Hir.HMethod recovered = pipeline.Recover(inst);
                        Console.WriteLine(Rewind.Analysis.Hir.HirPrinter.Print(recovered));
                        foreach (string note in recovered.Notes.Distinct()) Console.WriteLine("  # " + note);
                        foreach (string problem in recovered.Problems.Distinct()) Console.WriteLine("  ! " + problem);
                    }
                    catch (Exception e)
                    {
                        Console.WriteLine($"{inst}: CRASH {e.GetType().Name}: {e.Message}");
                    }
                    if (++instances >= 3) break;
                }
                if (instances != 0 && ++shown >= max) break;
                continue;
            }
            try
            {
                Rewind.Analysis.Hir.HMethod recovered = pipeline.Recover(method);
                Console.WriteLine(Rewind.Analysis.Hir.HirPrinter.Print(recovered));
                foreach (string note in recovered.Notes.Distinct()) Console.WriteLine("  # " + note);
            }
            catch (Exception e)
            {
                Console.WriteLine($"{method.FullName}: CRASH {e.GetType().Name}: {e.Message}\n{e.StackTrace?.Split('\n').Take(4).Aggregate("", (a, b) => a + b.TrimEnd() + "\n")}");
            }
            if (++shown >= max) break;
        }
        return 0;
    }

    /// <summary>hir-stats &lt;input&gt; &lt;symbols.tsv&gt; [assembly]: recovers every method and tallies what is still missing.</summary>
    public static int HirStats(Il2CppModel model, string symbolsPath, string? assemblyFilter, bool showExamples = false)
    {
        ProgramAnalysis program = MakeProgram(model, symbolsPath);
        var pipeline = new Rewind.Analysis.Recover.MethodPipeline(program);
        var sw = Stopwatch.StartNew();
        int total = 0, clean = 0, crashed = 0;
        var kinds = new Dictionary<string, int>();
        var crashes = new Dictionary<string, int>();
        var examples = new Dictionary<string, List<string>>();
        var unidentified = new Dictionary<ulong, int>();
        var callers = new Dictionary<ulong, string>();
        string? focus = Environment.GetEnvironmentVariable("REWIND_PROBLEM");
        var focused = new Dictionary<string, int>();
        var focusedExample = new Dictionary<string, string>();
        var perAssembly = new Dictionary<string, (int Total, int Clean)>();
        foreach (MethodDef method in model.Methods)
        {
            if (method.Address == 0) continue;
            string asm = method.DeclaringType.Assembly.Name;
            if (assemblyFilter != null && asm != assemblyFilter) continue;
            if (method.DeclaringType.GenericParameters.Length != 0 || method.GenericParameters.Length != 0) continue;
            if (!Rewind.Output.AssemblyEmitter.HasIlBody(method)) continue;
            total++;
            var tally = perAssembly.GetValueOrDefault(asm);
            try
            {
                Rewind.Analysis.Hir.HMethod h = pipeline.Recover(method);
                if (h.Problems.Count == 0)
                {
                    clean++;
                    tally.Clean++;
                }
                foreach (string p in h.Problems.Distinct())
                {
                    if (focus != null && p.Contains(focus, StringComparison.Ordinal))
                    {
                        focused[p] = focused.GetValueOrDefault(p) + 1;
                        focusedExample.TryAdd(p, method.FullName);
                        // Split by what the method itself is: a P/Invoke declaration (0x2000) or ordinary code.
                        string shape = (method.Flags & 0x2000) != 0 ? " [pinvoke declaration]" : " [ordinary method]";
                        focused[p + shape] = focused.GetValueOrDefault(p + shape) + 1;
                        focusedExample.TryAdd(p + shape, method.FullName);
                    }
                    if (p.StartsWith("call to unidentified native function 0x", StringComparison.Ordinal))
                    {
                        ulong target = Convert.ToUInt64(p[(p.LastIndexOf("0x", StringComparison.Ordinal) + 2)..], 16);
                        unidentified[target] = unidentified.GetValueOrDefault(target) + 1;
                        callers.TryAdd(target, method.FullName);
                    }
                    string key = System.Text.RegularExpressions.Regex.Replace(p, "0x[0-9A-Fa-f]+", "N");
                    key = System.Text.RegularExpressions.Regex.Replace(key, "%[0-9]+", "%");
                    key = System.Text.RegularExpressions.Regex.Replace(key, " of [^ ]+$| into a .*$|on [^ ]+$", "");
                    kinds[key] = kinds.GetValueOrDefault(key) + 1;
                    if (!examples.TryGetValue(key, out List<string>? list)) examples[key] = list = [];
                    if (list.Count < 3 && h.Blocks.Sum(b => b.Statements.Count) < 30) list.Add(method.FullName);
                }
            }
            catch (Exception e)
            {
                crashed++;
                string key = e.GetType().Name + " @ " + (e.StackTrace?.Split('\n').FirstOrDefault()?.Trim() ?? "");
                if (!crashes.ContainsKey(key)) Console.WriteLine($"  first crash of its kind: {method.FullName} @0x{method.Address:X}: {e.Message}");
                crashes[key] = crashes.GetValueOrDefault(key) + 1;
            }
            tally.Total++;
            perAssembly[asm] = tally;
        }
        Console.WriteLine($"recovered {total} methods in {sw.ElapsedMilliseconds} ms: {clean} clean ({100.0 * clean / Math.Max(1, total):F1}%), {crashed} crashed");
        foreach (var (asm, t) in perAssembly.OrderByDescending(kv => kv.Value.Total).Take(12))
            Console.WriteLine($"  {asm,-40} {t.Clean,6}/{t.Total,-6} {100.0 * t.Clean / Math.Max(1, t.Total):F1}%");
        Console.WriteLine("most common gaps:");
        foreach (var (kind, count) in kinds.OrderByDescending(kv => kv.Value).Take(45))
        {
            Console.WriteLine($"  {count,7}  {kind}");
            if (showExamples && examples.TryGetValue(kind, out List<string>? list))
                foreach (string name in list) Console.WriteLine($"             e.g. {name}");
        }
        if (focus != null)
        {
            Console.WriteLine($"problems mentioning '{focus}': {focused.Count} distinct, {focused.Values.Sum()} methods");
            foreach (var (text, count) in focused.OrderByDescending(kv => kv.Value).Take(60))
                Console.WriteLine($"  {count,6}  {text}   e.g. {focusedExample[text]}");
        }
        if (crashes.Count != 0)
        {
            Console.WriteLine("crashes:");
            foreach (var (kind, count) in crashes.OrderByDescending(kv => kv.Value).Take(15))
                Console.WriteLine($"  {count,7}  {kind}");
        }
        if (unidentified.Count != 0)
        {
            Console.WriteLine($"unidentified native call targets: {unidentified.Count} distinct; most called:");
            var index = new Rewind.Analysis.Runtime.CodeIndex(program.Context);
            foreach (var (target, count) in unidentified.OrderByDescending(kv => kv.Value).Take(int.TryParse(Environment.GetEnvironmentVariable("REWIND_TARGETS"), out int shown) ? shown : 25))
            {
                var code = index.Get(target);
                string section = model.Image.SectionAt(target)?.Name ?? "?";
                string names = code == null ? "" : string.Join(" | ", code.Names.Take(3));
                Console.WriteLine($"  {count,7}  0x{target:X} [{section}] {code?.Instructions ?? 0} instructions, {code?.Callees.Count ?? 0} callees  {names}  e.g. from {callers.GetValueOrDefault(target)}");
            }
        }
        return 0;
    }

    /// <summary>ir &lt;input&gt; &lt;name filter&gt; &lt;signatures&gt;: the code of a method as the recovery is given it, after every pass of the pipeline.</summary>
    public static int PipelineIr(Il2CppModel model, string filter, string symbolsPath)
    {
        ProgramAnalysis program = MakeProgram(model, symbolsPath);
        Dictionary<ulong, List<string>> symbols = [];
        foreach (var (address, info) in program.Helpers.ByAddress) symbols[address] = [info.Kind.ToString()];
        var pipeline = new Rewind.Analysis.Recover.MethodPipeline(program);
        int shown = 0;
        foreach (MethodDef method in model.Methods)
        {
            if (!method.FullName.Contains(filter, StringComparison.Ordinal)) continue;
            Rewind.Analysis.Recover.LiftedMethod lifted;
            if (method.Address == 0)
            {
                // A generic definition: the body its instantiations over reference types share, with its own type parameters.
                static bool IsObject(TypeSig t) => t is PrimitiveSig { Element: Rewind.Runtime.Il2CppTypeEnum.Object };
                MethodInst? shared = program.InstsOf(method).FirstOrDefault(i => i.Address != 0 && i.ClassArguments.All(IsObject) && i.MethodArguments.All(IsObject));
                if (shared == null) continue;
                lifted = pipeline.Lift(method, method.DeclaringType.GenericParameters.Select(p => (TypeSig)model.Sigs.GenericParam(p)).ToArray(),
                    method.GenericParameters.Select(p => (TypeSig)model.Sigs.GenericParam(p)).ToArray(), shared.Address);
            }
            else lifted = pipeline.Lift(method);
            Console.WriteLine($"=== {method.FullName}  (frame objects {lifted.Frame.Count}: {string.Join(", ", lifted.Frame)})");
            Console.WriteLine(lifted.Function.Dump(n => Annotate(n, model, symbols)));
            if (++shown >= 12) break;
        }
        return 0;
    }

    /// <summary>norm &lt;input&gt; &lt;name filter&gt; &lt;symbols.tsv&gt;: IR after normalization and stack promotion.</summary>
    public static int Normalized(Il2CppModel model, string filter, string symbolsPath)
    {
        Dictionary<ulong, List<string>>? symbols = symbolsPath.EndsWith(".sig", StringComparison.OrdinalIgnoreCase) ? null : CallStats.LoadSymbols(model.Image, symbolsPath);
        ProgramAnalysis program = MakeProgram(model, symbolsPath);
        if (symbols == null)
        {
            symbols = [];
            foreach (var (address, info) in program.Helpers.ByAddress) symbols[address] = [info.Kind.ToString()];
        }
        Console.WriteLine($"helpers: {program.Helpers.ByAddress.Count}, default class slots: {program.Defaults.Slots.Count}");
        IMachineLifter lifter = program.NewLifter();
        var normalizer = new Rewind.Analysis.Recover.Normalizer(program);
        int shown = 0;
        foreach (MethodDef method in model.Methods)
        {
            if (method.Address == 0 || !method.FullName.Contains(filter, StringComparison.Ordinal)) continue;
            Function fn = lifter.Lift(method.Address);
            var result = normalizer.Run(fn);
            var frame = Rewind.Analysis.Passes.StackPromotion.Run(fn);
            Rewind.Analysis.Passes.DeadCode.Run(fn);
            Console.WriteLine($"=== {method.FullName}  (guards {result.GuardsRemoved}, helpers {result.HelpersRemoved}, regions {result.RegionsRemoved}, casts {result.Casts.Count}, frame objects {frame.Count})");
            Console.WriteLine(fn.Dump(n => Annotate(n, model, symbols)));
            if (++shown >= 12) break;
        }
        return 0;
    }

    private static string? Annotate(Node n, Il2CppModel model, Dictionary<ulong, List<string>>? symbols)
    {
        if (n.Op is Op.Call or Op.TailCall && n.Aux is CallInfo { Indirect: false, Intrinsic: null } ci)
        {
            if (model.MethodsByAddress.TryGetValue(ci.Target, out List<MethodDef>? methods))
                return methods[0].FullName + (methods.Count > 1 ? $" (+{methods.Count - 1})" : "");
            if (model.InstsByAddress.TryGetValue(ci.Target, out List<MethodInst>? insts))
                return insts[0] + (insts.Count > 1 ? $" (+{insts.Count - 1})" : "");
            if (symbols != null && symbols.TryGetValue(ci.Target, out List<string>? names)) return names[0];
        }
        if (n.Op is Op.Load or Op.Store && n.In[0].IsConst)
        {
            ulong va = (ulong)n.In[0].Imm;
            if (model.ResolveUsageSlot(va) is { } usage) return usage.ToString();
            if (symbols != null && symbols.TryGetValue(va, out List<string>? names)) return names[0];
        }
        return null;
    }

    /// <summary>eh-dump &lt;input&gt; &lt;filter&gt;: the Itanium exception tables (call sites, landing pads, filters) of matching methods.</summary>
    public static int ExceptionTables(Il2CppModel model, string filter)
    {
        if (model.Image is not Rewind.Binary.ElfImage elf) return 1;
        foreach (MethodDef method in model.Methods)
        {
            if (method.Address == 0 || !method.FullName.Contains(filter, StringComparison.Ordinal)) continue;
            Console.WriteLine($"=== {method.FullName} 0x{method.Address:X}");
            if (elf.ExceptionTableOf(method.Address) is not { } table) { Console.WriteLine("  no exception table"); continue; }
            foreach (var site in table.CallSites)
                Console.WriteLine($"  [0x{site.Start:X}, 0x{site.End:X}) pad 0x{site.LandingPad:X} action {site.Action} filter {site.Filter}{(site.Catches ? " catches" : "")}");
        }
        return 0;
    }

    /// <summary>lift-stats &lt;input&gt;: lifts every managed function and reports what the lifter cannot handle yet.</summary>
    public static int Stats(Il2CppModel model)
    {
        var context = new ModelCodeContext(model);
        IMachineLifter lifter = model.Image.Arch == Rewind.Binary.CpuArch.Arm64 ? new Rewind.Analysis.Arm64.A64Lifter(context) : new X64Lifter(context);
        var addresses = new HashSet<ulong>(model.MethodsByAddress.Keys);
        addresses.UnionWith(model.InstsByAddress.Keys);

        var sw = Stopwatch.StartNew();
        int total = 0, clean = 0, crashed = 0;
        long nodes = 0, blocks = 0;
        var problemKinds = new Dictionary<string, int>();
        var crashes = new Dictionary<string, int>();
        foreach (ulong address in addresses)
        {
            total++;
            Function fn;
            try
            {
                fn = lifter.Lift(address);
            }
            catch (Exception e)
            {
                crashed++;
                string key = e.GetType().Name + ": " + e.Message.Split('\n')[0] + " @ " + (e.StackTrace?.Split('\n').FirstOrDefault()?.Trim() ?? "");
                crashes[key] = crashes.GetValueOrDefault(key) + 1;
                continue;
            }
            blocks += fn.Blocks.Count;
            foreach (Block b in fn.Blocks) nodes += b.Nodes.Count + b.Phis.Count;
            if (fn.Problems.Count == 0) clean++;
            foreach (string p in fn.Problems)
            {
                // Group by message shape: drop addresses.
                string key = System.Text.RegularExpressions.Regex.Replace(p, "0x[0-9A-Fa-f]+", "ADDR");
                problemKinds[key] = problemKinds.GetValueOrDefault(key) + 1;
            }
        }
        Console.WriteLine($"lifted {total} functions in {sw.ElapsedMilliseconds} ms: {clean} without problems ({100.0 * clean / Math.Max(1, total):F2}%), {crashed} crashed");
        Console.WriteLine($"{blocks:N0} blocks, {nodes:N0} nodes");
        Console.WriteLine("unsupported instructions:");
        foreach (var (mnemonic, count) in lifter.UnsupportedCounts.OrderByDescending(kv => kv.Value).Take(60))
            Console.WriteLine($"  {count,8}  {mnemonic}");
        Console.WriteLine("problem kinds:");
        foreach (var (kind, count) in problemKinds.OrderByDescending(kv => kv.Value).Take(40))
            Console.WriteLine($"  {count,8}  {kind}");
        if (crashes.Count != 0)
        {
            Console.WriteLine("crashes:");
            foreach (var (kind, count) in crashes.OrderByDescending(kv => kv.Value).Take(20))
                Console.WriteLine($"  {count,8}  {kind}");
        }
        _ = typeof(Mnemonic);
        return 0;
    }
}
