// Prints the IL of the methods of an assembly in Rewind's assemblies/ output, for check_repros.py, or runs one.
//
//   il <assemblies dir> <assembly> <filter>   methods whose "Type::Name" contains <filter> (a substring match)
//   run <assemblies dir> <assembly> <type> <method>
//       calls the static method <type>::<method>(object owner, object[] pool) of Rewind's recovered assembly with
//       pool = { 1, 2, 3, 4, null, 5 } and describes the objects of the array it returns: each one's instance fields
//       by name, a reference to an object of the array as #<index>, the owner as "owner", an array by its length.
//       What a recovered method computes, not how its C# reads (issue 34: which variable got which object).

using System.Globalization;
using System.Reflection;
using System.Runtime.Loader;
using Mono.Cecil;

static class Program
{
    static int Main(string[] args)
    {
        if (args.Length == 5 && args[0] == "run") return Run(args[1], args[2], args[3], args[4]);
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

    static int Run(string dir, string assembly, string typeName, string methodName)
    {
        // The recovered assembly references the game's class libraries; the runtime's own stand in for mscorlib and
        // the rest, and anything else comes from the assemblies folder.
        AssemblyLoadContext.Default.Resolving += (context, name) =>
        {
            string path = Path.Combine(dir, name.Name + ".dll");
            return File.Exists(path) ? context.LoadFromAssemblyPath(path) : null;
        };
        Assembly recovered = AssemblyLoadContext.Default.LoadFromAssemblyPath(Path.GetFullPath(Path.Combine(dir, assembly + ".dll")));
        Type type = recovered.GetType(typeName) ?? throw new InvalidOperationException($"no type {typeName}");
        MethodInfo method = type.GetMethod(methodName, BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static)
                            ?? throw new InvalidOperationException($"no method {typeName}::{methodName}");
        object owner = new();
        object?[] pool = [1, 2, 3, 4, null, 5];
        Array result;
        try
        {
            result = (Array)method.Invoke(null, [owner, pool])!;
        }
        catch (TargetInvocationException e)
        {
            Console.WriteLine($"threw {e.InnerException?.GetType().Name}: {e.InnerException?.Message}");
            return 0;
        }
        var items = result.Cast<object?>().ToList();
        var parts = new List<string>();
        for (int i = 0; i < items.Count; i++)
        {
            object? item = items[i];
            if (item == null)
            {
                parts.Add($"#{i} null");
                continue;
            }
            var fields = item.GetType().GetFields(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance)
                .OrderBy(f => f.Name, StringComparer.Ordinal)
                .Select(f => $"{f.Name}={Describe(f.GetValue(item), items, owner)}");
            parts.Add($"#{i} " + string.Join(" ", fields));
        }
        Console.WriteLine(string.Join(" | ", parts));
        return 0;
    }

    static string Describe(object? value, List<object?> items, object owner)
    {
        if (value == null) return "null";
        if (ReferenceEquals(value, owner)) return "owner";
        int at = items.FindIndex(x => ReferenceEquals(x, value));
        if (at >= 0) return $"#{at}";
        if (value is Array array) return $"{array.GetType().GetElementType()?.Name}[{array.Length}]";
        return value is IFormattable formattable ? formattable.ToString(null, CultureInfo.InvariantCulture) : value.GetType().Name;
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
