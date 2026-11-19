// Modified by xob0t (2026): NewSpecific/NewAllocSpecific helper rules. See FORK.md.
namespace Rewind.Analysis.Runtime;

/// <summary>The libil2cpp support functions that generated code calls, by what they mean in managed terms.</summary>
public enum HelperKind
{
    None,

    // metadata and type initialization: no managed meaning, removed
    MetadataInit,            // il2cpp_codegen_initialize_runtime_metadata(&slot)
    MetadataInitInline,      // same, returns the initialized pointer
    ClassInit,               // il2cpp_codegen_runtime_class_init(klass): run the static constructor if needed
    ClassInitSlow,           // ClassInlines::InitFromCodegenSlow(klass) -> klass
    RgctxInitSlow,           // ClassInlines::InitRgctxFromCodegenSlow(method)
    WriteBarrier,            // Il2CppCodeGenWriteBarrier(&slot, value)
    WriteBarrierForClass,    // (klass, &slot, value)
    WriteBarrierForType,     // (type, &slot, value)
    NullCheck,               // out-of-line NullCheck(ptr)
    ArrayElementTypeCheck,   // covariance check before storing a reference into an array

    // allocation and conversion
    ObjectNew,               // il2cpp_codegen_object_new(klass)
    SzArrayNew,              // SZArrayNew(arrayKlass, length)
    GenArrayNew,             // GenArrayNew(arrayKlass, dimensions*)
    Box,                     // Box(klass, void* data)
    Unbox,                   // Unbox_internal(obj) -> pointer to the payload
    UnboxAny,                // UnBox_Any(obj, klass, storage)
    UnboxNullable,           // UnBoxNullable_internal(obj, klass, storage)
    IsInst,                  // IsInst(obj, klass) -> obj or null
    TypeGetObject,           // il2cpp_codegen_type_get_object(Il2CppType*) -> System.Type
    WouldBoxToNonNull,       // il2cpp_codegen_would_box_to_non_null(klass, ptr)

    // exceptions
    Throw,                   // il2cpp_codegen_raise_exception(ex, method)
    Rethrow,                 // rethrow the current exception
    ThrowNullReference,
    ThrowIndexOutOfRange,
    ThrowDivideByZero,
    ThrowInvalidCast,        // RaiseInvalidCastException(obj, klass)
    GetArrayTypeMismatchException,
    GetOverflowException,
    GetArgumentException,
    GetInvalidCastException,
    GetNotSupportedException,
    GetInvalidOperationException,
    GetIndexOutOfRangeException,
    GetMissingMethodException,
    ExceptionStackPush, ExceptionStackPop, ExceptionStackTop,

    // dispatch helpers
    InterfaceInvoker,        // Interface{Func,Action}InvokerN::Invoke(slot, interfaceKlass, obj, args...)
    VirtualInvoker,          // Virtual{Func,Action}InvokerN::Invoke(slot, obj, args...)
    GenericVirtualInvoker,   // GenericVirtual...::Invoke(method, obj, args...)
    GenericInterfaceInvoker,
    ConstrainedInvoker,
    InterfaceInvokeDataSlow, // ClassInlines::GetInterfaceInvokeDataFromVTableSlowPath(obj, klass, slot)
    GetGenericVirtualMethod, // il2cpp_codegen_get_generic_virtual_method_internal(def, inflated)
    RuntimeConstrainedCall,

    // statics, interop, misc
    StaticFieldsFor,         // il2cpp_codegen_static_fields_for(klass)
    ThreadStaticData,        // il2cpp_codegen_get_thread_static_data(klass)
    ResolveICall,            // il2cpp_codegen_resolve_icall("Namespace.Type::Method")
    ResolvePInvoke,          // il2cpp_codegen_resolve(PInvokeArguments&)
    MemoryBarrier,
    Memcpy, Memset, CheckStack,
    RgctxData,               // il2cpp_rgctx_data(rgctx, index) and its no-init variant
    MethodIsStatic, MethodIsInterface, MethodIsGenericInstance,
    GetInstanceFieldDataPointer, WriteInstanceFieldData,
    /// <summary>UnBox(object, class): the unboxed value's address, the object checked to be of that class first.</summary>
    UnboxChecked,
    /// <summary>__stack_chk_fail: the stack protector found its guard overwritten (does not return).</summary>
    StackCheckFail,
    /// <summary>sincos(x, &amp;sine, &amp;cosine) / sincosf.</summary>
    SinCos,
    ArrayGetAt, ArraySetAt, ArrayGetAddressAt,
    /// <summary>A C runtime math function (sqrt, sin, pow, ...); the helper's name says which.</summary>
    MathFunction,
    /// <summary>Interlocked.CompareExchange&lt;T&gt;(ref location, value, comparand) for reference types.</summary>
    InterlockedCompareExchange,
    /// <summary>Interlocked.Exchange&lt;T&gt;(ref location, value) for reference types.</summary>
    InterlockedExchange,
    /// <summary>CastclassClass / CastclassSealed(obj, klass): a checked cast.</summary>
    CastClass,
    /// <summary>il2cpp_codegen_get_type(name, [throwOnError, [ignoreCase,]] getTypeMethod, callingMethod): Type.GetType.</summary>
    GetType,
    /// <summary>il2cpp_codegen_initobj(pointer, size): the location takes its type's default value.</summary>
    InitObj,
    /// <summary>Il2CppFakeBox&lt;T&gt;(this, klass, value*): a value boxed in place, on the stack.</summary>
    FakeBoxInit,
    /// <summary>il2cpp_codegen_raise_profile_exception(method): throws NotSupportedException naming the method.</summary>
    RaiseProfileException,
    /// <summary>il2cpp_codegen_class_is_assignable_from(klass, oklass): an object of class oklass is a klass.</summary>
    IsAssignableFrom,
    /// <summary>_CxxThrowException(object, throwInfo): a C++ throw (in a catch handler: passing the caught exception on).</summary>
    CxxThrow,
    /// <summary>il2cpp_codegen_marshal_store_last_error(): after a P/Invoke call declared SetLastError.</summary>
    StoreLastError,
    /// <summary>modf(x, &amp;whole) / modff: returns the fraction of x and stores its whole part (IL2CPP's rounding uses it).</summary>
    Modf,
    /// <summary>
    /// il2cpp_codegen_get_virtual_call_method_pointer(method), Unity 2021: the code pointer a delegate to the method
    /// calls. Later versions read it out of the method's record in place (virtualMethodPointer).
    /// </summary>
    MethodVirtualCallPointer,
}

public sealed record HelperInfo(HelperKind Kind, int IntArgs, bool NoReturn, bool ReturnsValue, string Name)
{
    /// <summary>For math functions: number of floating point arguments and whether they are doubles.</summary>
    public int FloatArgs { get; init; }
    public bool IsDouble { get; init; }
    public string MathName { get; init; } = "";
    /// <summary>
    /// For a method invoker that returns a struct: the address the struct goes to comes first, before the slot
    /// ("Invoke(&amp;result, slot, interfaceClass, obj, args...)").
    /// </summary>
    public bool BufferFirst { get; init; }
}

/// <summary>Maps function addresses to the runtime helpers they implement.</summary>
public sealed class RuntimeHelpers
{
    private readonly Dictionary<ulong, HelperInfo> _byAddress = [];

    public IReadOnlyDictionary<ulong, HelperInfo> ByAddress => _byAddress;

    public HelperInfo? At(ulong address) => _byAddress.GetValueOrDefault(address);
    public HelperKind KindAt(ulong address) => _byAddress.TryGetValue(address, out HelperInfo? h) ? h.Kind : HelperKind.None;

    public void Add(ulong address, HelperInfo info) => _byAddress[address] = info;

    public IEnumerable<ulong> AddressesOf(HelperKind kind) => _byAddress.Where(kv => kv.Value.Kind == kind).Select(kv => kv.Key);

    // name fragment -> (kind, integer argument count, noreturn, returns a value)
    private static readonly (string Fragment, HelperKind Kind, int Args, bool NoReturn, bool Returns)[] SymbolRules =
    [
        ("CompareExchange_T@Interlocked", HelperKind.InterlockedCompareExchange, 3, false, true),
        ("Exchange_T@Interlocked", HelperKind.InterlockedExchange, 2, false, true),
        ("il2cpp_codegen_initialize_runtime_metadata_inline", HelperKind.MetadataInitInline, 1, false, true),
        ("il2cpp_codegen_initialize_runtime_metadata", HelperKind.MetadataInit, 1, false, false),
        ("il2cpp_codegen_runtime_class_init_inline", HelperKind.ClassInit, 1, false, false),
        ("il2cpp_codegen_runtime_class_init", HelperKind.ClassInit, 1, false, false),
        ("InitFromCodegenSlow", HelperKind.ClassInitSlow, 1, false, true),
        ("InitRgctxFromCodegenSlow", HelperKind.RgctxInitSlow, 1, false, true),
        ("Il2CppCodeGenWriteBarrierForClass", HelperKind.WriteBarrierForClass, 3, false, false),
        ("Il2CppCodeGenWriteBarrierForType", HelperKind.WriteBarrierForType, 3, false, false),
        ("Il2CppCodeGenWriteBarrier", HelperKind.WriteBarrier, 2, false, false),
        ("ArrayElementTypeCheck", HelperKind.ArrayElementTypeCheck, 2, false, false),
        ("il2cpp_codegen_object_new", HelperKind.ObjectNew, 1, false, true),
        ("SZArrayNew", HelperKind.SzArrayNew, 2, false, true),
        ("GenArrayNew", HelperKind.GenArrayNew, 2, false, true),
        ("UnBoxNullable_internal", HelperKind.UnboxNullable, 3, false, false),
        ("UnBox_Any", HelperKind.UnboxAny, 3, false, true),
        ("Unbox_internal", HelperKind.Unbox, 1, false, true),
        ("il2cpp_codegen_would_box_to_non_null", HelperKind.WouldBoxToNonNull, 2, false, true),
        ("il2cpp_codegen_type_get_object", HelperKind.TypeGetObject, 1, false, true),
        ("il2cpp_codegen_raise_null_reference_exception", HelperKind.ThrowNullReference, 0, true, false),
        ("il2cpp_codegen_raise_index_out_of_range_exception", HelperKind.ThrowIndexOutOfRange, 0, true, false),
        ("il2cpp_codegen_raise_divide_by_zero_exception", HelperKind.ThrowDivideByZero, 0, true, false),
        ("RaiseInvalidCastException", HelperKind.ThrowInvalidCast, 2, true, false),
        ("il2cpp_codegen_raise_exception", HelperKind.Throw, 2, true, false),
        ("il2cpp_codegen_rethrow_exception", HelperKind.Rethrow, 1, true, false),
        ("class_is_assignable_from", HelperKind.IsAssignableFrom, 2, false, true),
        ("_CxxThrowException", HelperKind.CxxThrow, 2, true, false),
        ("__cxa_throw", HelperKind.CxxThrow, 3, true, false),
        ("il2cpp_codegen_marshal_store_last_error", HelperKind.StoreLastError, 0, false, false),
        ("RethrowException", HelperKind.Rethrow, 1, true, false),
        ("il2cpp_codegen_get_array_type_mismatch_exception", HelperKind.GetArrayTypeMismatchException, 0, false, true),
        ("il2cpp_codegen_get_overflow_exception", HelperKind.GetOverflowException, 0, false, true),
        ("il2cpp_codegen_get_argument_exception", HelperKind.GetArgumentException, 2, false, true),
        ("il2cpp_codegen_get_invalid_cast_exception", HelperKind.GetInvalidCastException, 1, false, true),
        ("il2cpp_codegen_get_not_supported_exception", HelperKind.GetNotSupportedException, 1, false, true),
        ("il2cpp_codegen_get_invalid_operation_exception", HelperKind.GetInvalidOperationException, 1, false, true),
        ("il2cpp_codegen_get_index_out_of_range_exception", HelperKind.GetIndexOutOfRangeException, 0, false, true),
        ("il2cpp_codegen_get_missing_method_exception", HelperKind.GetMissingMethodException, 1, false, true),
        ("GetInterfaceInvokeDataFromVTableSlowPath", HelperKind.InterfaceInvokeDataSlow, 3, false, true),
        ("il2cpp_codegen_get_generic_virtual_method_internal", HelperKind.GetGenericVirtualMethod, 2, false, true),
        ("il2cpp_codegen_get_virtual_call_method_pointer", HelperKind.MethodVirtualCallPointer, 1, false, true),
        ("il2cpp_codegen_runtime_constrained_call", HelperKind.RuntimeConstrainedCall, 6, false, false),
        ("il2cpp_codegen_static_fields_for", HelperKind.StaticFieldsFor, 1, false, true),
        ("il2cpp_codegen_get_thread_static_data", HelperKind.ThreadStaticData, 1, false, true),
        ("il2cpp_codegen_resolve_icall", HelperKind.ResolveICall, 1, false, true),
        ("il2cpp_codegen_resolve_pinvoke", HelperKind.ResolvePInvoke, 1, false, true),
        ("il2cpp_codegen_memory_barrier", HelperKind.MemoryBarrier, 0, false, false),
        ("il2cpp_rgctx_data", HelperKind.RgctxData, 2, false, true),
        ("il2cpp_codegen_method_is_interface_method", HelperKind.MethodIsInterface, 1, false, true),
        ("il2cpp_codegen_method_is_generic_instance_method", HelperKind.MethodIsGenericInstance, 1, false, true),
        ("il2cpp_codegen_get_instance_field_data_pointer", HelperKind.GetInstanceFieldDataPointer, 2, false, true),
        ("il2cpp_codegen_write_instance_field_data", HelperKind.WriteInstanceFieldData, 4, false, false),
    ];

    /// <summary>
    /// Development path: names helpers from a symbol file (PDB public symbols or an unstripped ELF). Shipping
    /// binaries have no symbols; there the same table is filled by pattern-based discovery instead.
    /// </summary>
    public static RuntimeHelpers FromSymbols(IReadOnlyDictionary<ulong, List<string>> symbols, Func<ulong, bool> isManaged)
    {
        var helpers = new RuntimeHelpers();
        foreach (var (address, names) in symbols)
        {
            if (isManaged(address)) continue;
            HelperInfo? chosen = null;
            foreach (string name in names)
            {
                HelperInfo? info = Classify(name);
                if (info == null) continue;
                // The linker keeps one copy of functions with identical code. Where the two metadata initializers
                // are one function (Unity 2020), it is the one whose result the code uses: the other returns nothing.
                if (chosen == null || (chosen.Kind == HelperKind.MetadataInit && info.Kind == HelperKind.MetadataInitInline)) chosen = info;
                if (chosen.Kind != HelperKind.MetadataInit) break;
            }
            if (chosen != null) helpers._byAddress[address] = chosen;
        }
        return helpers;
    }

    /// <summary>
    /// C runtime name -> (argument count, operates on doubles, System.Math method name). "fmod" is not a method:
    /// it is what the IL remainder instruction does for floating point operands.
    /// </summary>
    private static readonly Dictionary<string, (int Args, bool IsDouble, string Managed)> MathFunctions = new(StringComparer.Ordinal)
    {
        ["sqrt"] = (1, true, "Sqrt"), ["sqrtf"] = (1, false, "Sqrt"),
        ["sin"] = (1, true, "Sin"), ["sinf"] = (1, false, "Sin"), ["cos"] = (1, true, "Cos"), ["cosf"] = (1, false, "Cos"),
        ["tan"] = (1, true, "Tan"), ["tanf"] = (1, false, "Tan"), ["asin"] = (1, true, "Asin"), ["asinf"] = (1, false, "Asin"),
        ["acos"] = (1, true, "Acos"), ["acosf"] = (1, false, "Acos"), ["atan"] = (1, true, "Atan"), ["atanf"] = (1, false, "Atan"),
        ["atan2"] = (2, true, "Atan2"), ["atan2f"] = (2, false, "Atan2"), ["pow"] = (2, true, "Pow"), ["powf"] = (2, false, "Pow"),
        ["exp"] = (1, true, "Exp"), ["expf"] = (1, false, "Exp"), ["log"] = (1, true, "Log"), ["logf"] = (1, false, "Log"),
        ["log10"] = (1, true, "Log10"), ["log10f"] = (1, false, "Log10"), ["fmod"] = (2, true, "fmod"), ["fmodf"] = (2, false, "fmod"),
        ["floor"] = (1, true, "Floor"), ["floorf"] = (1, false, "Floor"), ["ceil"] = (1, true, "Ceiling"), ["ceilf"] = (1, false, "Ceiling"),
        ["sinh"] = (1, true, "Sinh"), ["cosh"] = (1, true, "Cosh"), ["tanh"] = (1, true, "Tanh"), ["fabs"] = (1, true, "Abs"),
        // IL2CPP's own rounding: half to even, which is what Math.Round does.
        ["bankers_round"] = (1, true, "Round"), ["bankers_roundf"] = (1, false, "Round"),
    };

    private static int CountOf(string text, string part)
    {
        int count = 0;
        for (int at = text.IndexOf(part, StringComparison.Ordinal); at >= 0; at = text.IndexOf(part, at + part.Length, StringComparison.Ordinal)) count++;
        return count;
    }

    /// <summary>The helper a runtime function is, from its symbol name; null when the name is not one the decompiler translates.</summary>
    public static HelperInfo? Classify(string name)
    {
        // Strip C++ decoration so fragments match whole identifiers rather than parameter type names.
        string core = name;
        if (core.StartsWith('?'))
        {
            int at = core.IndexOf("@@", StringComparison.Ordinal);
            core = at > 0 ? core[1..at] : core[1..];
        }
        else if (core.StartsWith("_Z", StringComparison.Ordinal))
        {
            // Itanium: the qualified name, innermost first like MSVC's ("Invoke@VirtualFuncInvoker0").
            core = ItaniumNames.Core(core) ?? core;
        }

        // Invoker templates: Invoke@?$InterfaceFuncInvoker0@... (MSVC) or InterfaceFuncInvoker0<...>::Invoke (Itanium).
        if (core.Contains("Invoker", StringComparison.Ordinal) && core.Contains("Invoke", StringComparison.Ordinal))
        {
            if (core.Contains("GenericInterface", StringComparison.Ordinal)) return new HelperInfo(HelperKind.GenericInterfaceInvoker, 0, false, true, name);
            if (core.Contains("GenericVirtual", StringComparison.Ordinal)) return new HelperInfo(HelperKind.GenericVirtualInvoker, 0, false, true, name);
            if (core.Contains("Constrained", StringComparison.Ordinal)) return new HelperInfo(HelperKind.ConstrainedInvoker, 0, false, true, name);
            if (core.Contains("InterfaceFuncInvoker", StringComparison.Ordinal) || core.Contains("InterfaceActionInvoker", StringComparison.Ordinal))
                return new HelperInfo(HelperKind.InterfaceInvoker, 0, false, true, name);
            if (core.Contains("VirtualFuncInvoker", StringComparison.Ordinal) || core.Contains("VirtualActionInvoker", StringComparison.Ordinal))
                return new HelperInfo(HelperKind.VirtualInvoker, 0, false, true, name);
        }
        if (core.StartsWith("pop@?$ExceptionSupportStack", StringComparison.Ordinal)) return new HelperInfo(HelperKind.ExceptionStackPop, 1, false, true, name);
        if (core.StartsWith("top@?$ExceptionSupportStack", StringComparison.Ordinal)) return new HelperInfo(HelperKind.ExceptionStackTop, 1, false, true, name);
        if (core.StartsWith("push@?$ExceptionSupportStack", StringComparison.Ordinal)) return new HelperInfo(HelperKind.ExceptionStackPush, 2, false, false, name);
        if (core.StartsWith("GetAt@", StringComparison.Ordinal)) return new HelperInfo(HelperKind.ArrayGetAt, 2, false, true, name);
        if (core.StartsWith("SetAt@", StringComparison.Ordinal)) return new HelperInfo(HelperKind.ArraySetAt, 3, false, false, name);
        if (core.StartsWith("GetAddressAt@", StringComparison.Ordinal)) return new HelperInfo(HelperKind.ArrayGetAddressAt, 2, false, true, name);
        if (MathFunctions.TryGetValue(core, out var math))
            return new HelperInfo(HelperKind.MathFunction, 0, false, true, name) { FloatArgs = math.Args, IsDouble = math.IsDouble, MathName = math.Managed };
        if (core is "modf" or "modff") return new HelperInfo(HelperKind.Modf, 2, false, true, name) { FloatArgs = 1, IsDouble = core == "modf" };
        if (core is "sincos" or "sincosf") return new HelperInfo(HelperKind.SinCos, 2, false, false, name) { FloatArgs = 1, IsDouble = core == "sincos" };
        if (core is "__stack_chk_fail") return new HelperInfo(HelperKind.StackCheckFail, 0, true, false, name);
        // UnBox(Il2CppObject*, Il2CppClass*) as clang leaves it a function of its own (Itanium name).
        if (name == "_Z5UnBoxP12Il2CppObjectP11Il2CppClass") return new HelperInfo(HelperKind.UnboxChecked, 2, false, true, name);
        if (core is "memcpy" or "memmove") return new HelperInfo(HelperKind.Memcpy, 3, false, true, name);
        if (core is "memset") return new HelperInfo(HelperKind.Memset, 3, false, true, name);
        if (core is "__chkstk") return new HelperInfo(HelperKind.CheckStack, 0, false, false, name);
        if (core is "Box" or "NullCheck" or "IsInst" or "MethodIsStatic")
        {
            return core switch
            {
                "Box" => new HelperInfo(HelperKind.Box, 2, false, true, name),
                "NullCheck" => new HelperInfo(HelperKind.NullCheck, 1, false, false, name),
                "IsInst" => new HelperInfo(HelperKind.IsInst, 2, false, true, name),
                _ => new HelperInfo(HelperKind.MethodIsStatic, 1, false, true, name),
            };
        }
        // UnBox(object): the null check and Unbox_internal in one, where the compiler kept it a function (Unity 2020).
        // Its overload with a class to check against is something else.
        if (name == "?UnBox@@YAPEAXPEAUIl2CppObject@@@Z") return new HelperInfo(HelperKind.Unbox, 1, false, true, name);
        if (core == "il2cpp_codegen_resolve") return new HelperInfo(HelperKind.ResolvePInvoke, 1, false, true, name);
        // The runtime's allocators behind SZArrayNew and il2cpp_codegen_object_new, which whole-program optimized
        // code calls directly once the codegen wrapper is inlined: Array::NewSpecific(klass, length),
        // Object::New(klass) and Object::NewAllocSpecific(klass).
        if (core == "NewSpecific@Array@vm@il2cpp") return new HelperInfo(HelperKind.SzArrayNew, 2, false, true, name);
        if (core is "New@Object@vm@il2cpp" or "NewAllocSpecific@Object@vm@il2cpp") return new HelperInfo(HelperKind.ObjectNew, 1, false, true, name);
        if (core is "IsInstClass" or "IsInstSealed") return new HelperInfo(HelperKind.IsInst, 2, false, true, name);
        // (Plain Castclass - any class or interface - is pasted in place by MSVC, but clang keeps it a function.)
        if (core is "CastclassClass" or "CastclassSealed" or "Castclass") return new HelperInfo(HelperKind.CastClass, 2, false, true, name);
        if (core == "il2cpp_codegen_raise_profile_exception") return new HelperInfo(HelperKind.RaiseProfileException, 1, true, false, name);
        if (core == "il2cpp_codegen_initobj") return new HelperInfo(HelperKind.InitObj, 2, false, false, name);
        if (core.Contains("Il2CppFakeBox", StringComparison.Ordinal) && (name.StartsWith("??0", StringComparison.Ordinal) || name.Contains("C1E", StringComparison.Ordinal) || name.Contains("C2E", StringComparison.Ordinal)))
            return new HelperInfo(HelperKind.FakeBoxInit, 3, false, true, name);
        if (core == "il2cpp_codegen_get_type")
        {
            // Overloads by the number of bool parameters (_N in MSVC names, b in Itanium ones).
            string parameters = name.StartsWith('?') ? name[(name.IndexOf("@@", StringComparison.Ordinal) + 2)..] : name;
            int bools = name.StartsWith('?') ? CountOf(parameters, "_N") : CountOf(parameters[(parameters.IndexOf("String", StringComparison.Ordinal) + 1)..], "b");
            return new HelperInfo(HelperKind.GetType, 3 + Math.Min(2, bools), false, true, name);
        }

        foreach (var (fragment, kind, args, noReturn, returns) in SymbolRules)
            if (core.Contains(fragment, StringComparison.Ordinal))
                return new HelperInfo(kind, args, noReturn, returns, name);
        return null;
    }
}
