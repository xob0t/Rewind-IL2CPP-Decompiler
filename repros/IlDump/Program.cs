// Prints the IL of the methods of an assembly in Rewind's assemblies/ output, for check_repros.py.
//
//   il <assemblies dir> <assembly> <filter>   methods whose "Type::Name" contains <filter> (a substring match)

using Mono.Cecil;

static class Program
{
    static int Main(string[] args)
    {
        if (args.Length != 4 || args[0] != "il")
        {
            Console.Error.WriteLine("usage: IlDump il <assemblies dir> <assembly> <filter>");
            return 2;
        }
        var resolver = new DefaultAssemblyResolver();
        resolver.AddSearchDirectory(args[1]);
        using var m = ModuleDefinition.ReadModule(Path.Combine(args[1], args[2] + ".dll"), new ReaderParameters { AssemblyResolver = resolver });
        foreach (var t in AllTypes(m))
            foreach (var md in t.Methods.Where(x => x.HasBody && $"{t.FullName}::{x.Name}".Contains(args[3], StringComparison.Ordinal)))
            {
                Console.WriteLine($"{md.FullName}  maxstack {md.Body.MaxStackSize}, locals {string.Join(", ", md.Body.Variables.Select(v => $"V{v.Index}:{v.VariableType}"))}");
                foreach (var h in md.Body.ExceptionHandlers)
                    Console.WriteLine($"  .{h.HandlerType} try {h.TryStart?.Offset:X4}-{h.TryEnd?.Offset:X4} handler {h.HandlerStart?.Offset:X4}-{h.HandlerEnd?.Offset:X4} {h.CatchType}");
                foreach (var i in md.Body.Instructions) Console.WriteLine("  " + i);
            }
        return 0;
    }

    static IEnumerable<TypeDefinition> AllTypes(ModuleDefinition m)
    {
        foreach (var t in m.Types)
            foreach (var n in Walk(t)) yield return n;
        static IEnumerable<TypeDefinition> Walk(TypeDefinition t)
        {
            yield return t;
            foreach (var n in t.NestedTypes)
                foreach (var x in Walk(n)) yield return x;
        }
    }
}
