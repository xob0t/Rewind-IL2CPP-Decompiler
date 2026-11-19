// Modified by xob0t (2026): one AssemblyRef per assembly. See FORK.md.
using Mono.Cecil;
using Mono.Cecil.Cil;
using Rewind.Model;
using Rewind.Runtime;
using CecilAttribute = Mono.Cecil.CustomAttribute;
using ModelAttribute = Rewind.Model.CustomAttribute;

namespace Rewind.Output;

/// <summary>
/// Rebuilds .NET assemblies from the model: every type, member, signature, constant, layout and attribute.
/// Method bodies start as "throw null" placeholders; <see cref="IMethodBodyProvider"/> fills in recovered IL.
/// </summary>
public sealed class AssemblyEmitter
{
    private readonly Il2CppModel _model;
    private readonly BlobDecoder _blobs;
    private readonly Resolver _resolver = new();
    private readonly Dictionary<AssemblyModel, AssemblyDefinition> _assemblies = [];
    private readonly Dictionary<TypeDef, TypeDefinition> _types = [];
    private readonly Dictionary<MethodDef, MethodDefinition> _methods = [];
    private readonly Dictionary<FieldDef, FieldDefinition> _fields = [];
    private readonly Dictionary<GenericParam, GenericParameter> _genericParams = [];
    private readonly int _header;

    public List<string> Warnings { get; } = [];

    public AssemblyEmitter(Il2CppModel model)
    {
        _model = model;
        _blobs = new BlobDecoder(model);
        _header = 2 * model.Image.PointerSize;
    }

    public IReadOnlyDictionary<AssemblyModel, AssemblyDefinition> Assemblies => _assemblies;

    /// <summary>Gives a P/Invoke declaration the library, entry point and options its wrapper code names.</summary>
    public void SetImport(Rewind.Analysis.Runtime.PInvokeImport import)
    {
        if (!_methods.TryGetValue(import.Method, out MethodDefinition? method) || !method.IsPInvokeImpl) return;
        ModuleDefinition module = method.Module;
        ModuleReference? library = module.ModuleReferences.FirstOrDefault(r => r.Name == import.Module);
        if (library == null)
        {
            library = new ModuleReference(import.Module);
            module.ModuleReferences.Add(library);
        }
        // Il2CppCallConvention: default, C, stdcall, thiscall, fastcall. Il2CppCharSet: ANSI, Unicode, not specified.
        PInvokeAttributes attributes = import.CallingConvention switch
        {
            1 => PInvokeAttributes.CallConvCdecl,
            2 => PInvokeAttributes.CallConvStdCall,
            3 => PInvokeAttributes.CallConvThiscall,
            4 => PInvokeAttributes.CallConvFastcall,
            _ => PInvokeAttributes.CallConvWinapi,
        };
        attributes |= import.CharSet switch
        {
            0 => PInvokeAttributes.CharSetAnsi,
            1 => PInvokeAttributes.CharSetUnicode,
            _ => PInvokeAttributes.CharSetNotSpec,
        };
        if (import.NoMangle) attributes |= PInvokeAttributes.NoMangle;
        if (import.SetLastError) attributes |= PInvokeAttributes.SupportsLastError;
        method.PInvokeInfo = new PInvokeInfo(attributes, import.EntryPoint, library);
    }
    public TypeDefinition this[TypeDef type] => _types[type];
    public MethodDefinition this[MethodDef method] => _methods[method];
    public FieldDefinition this[FieldDef field] => _fields[field];

    /// <summary>Resolves references between the assemblies being built, which exist only in memory.</summary>
    private sealed class Resolver : IAssemblyResolver
    {
        public readonly Dictionary<string, AssemblyDefinition> ByName = new(StringComparer.OrdinalIgnoreCase);
        public AssemblyDefinition? Resolve(AssemblyNameReference name) => ByName.GetValueOrDefault(name.Name);
        public AssemblyDefinition? Resolve(AssemblyNameReference name, ReaderParameters parameters) => Resolve(name);
        public void Dispose() { }
    }

    // ---- build -------------------------------------------------------------------------------------------------

    public void Build()
    {
        CreateAssemblies();
        CreateTypeShells();
        MarkPrimitives();
        foreach (TypeDef type in _model.Types) DefineHierarchy(type);
        foreach (TypeDef type in _model.Types) DefineMembers(type);
        foreach (TypeDef type in _model.Types) DefineOverrides(type);
        DefineAttributes();
    }

    private void CreateAssemblies()
    {
        foreach (AssemblyModel asm in _model.Assemblies)
        {
            var name = new AssemblyNameDefinition(asm.Name, asm.Version);
            if (!string.IsNullOrEmpty(asm.Culture) && asm.Culture != "neutral") name.Culture = asm.Culture;
            var parameters = new ModuleParameters
            {
                Kind = ModuleKind.Dll,
                Runtime = TargetRuntime.Net_4_0,
                AssemblyResolver = _resolver,
                Architecture = TargetArchitecture.I386,
            };
            AssemblyDefinition assembly = AssemblyDefinition.CreateAssembly(name, asm.ImageName, parameters);
            _assemblies[asm] = assembly;
            _resolver.ByName[asm.Name] = assembly;
        }

        // Declare references up front so the core library reference resolves to the mscorlib we emit. A reference
        // names the assembly as it is rebuilt: the metadata keeps an assembly's public key token but not its key,
        // so a rebuilt assembly has none, and a reference with the original token would be another identity -
        // one the types imported from that assembly (which name the rebuilt one) do not use.
        foreach (AssemblyModel asm in _model.Assemblies)
        {
            ModuleDefinition module = _assemblies[asm].MainModule;
            foreach (AssemblyModel reference in asm.References)
            {
                if (reference == asm) continue;
                AssemblyNameDefinition rebuilt = _assemblies[reference].Name;
                module.AssemblyReferences.Add(new AssemblyNameReference(rebuilt.Name, rebuilt.Version) { Culture = rebuilt.Culture });
            }
        }
    }

    private void CreateTypeShells()
    {
        foreach (AssemblyModel asm in _model.Assemblies)
        {
            ModuleDefinition module = _assemblies[asm].MainModule;
            // Keep definition order (by token) so row numbering follows the original as closely as possible.
            foreach (TypeDef type in asm.Types.Where(t => t.DeclaringType == null).OrderBy(t => t.Token))
                CreateShell(module, type, null);
        }
    }

    private void CreateShell(ModuleDefinition module, TypeDef type, TypeDefinition? parent)
    {
        TypeDefinition definition;
        if (parent == null && type.Name == "<Module>" && type.Namespace.Length == 0)
        {
            definition = module.Types[0]; // Cecil creates <Module> itself
            definition.Attributes = (TypeAttributes)type.Flags;
        }
        else
        {
            definition = new TypeDefinition(type.Namespace, type.Name, (TypeAttributes)type.Flags);
            if (parent == null) module.Types.Add(definition);
            else parent.NestedTypes.Add(definition);
        }
        _types[type] = definition;

        foreach (GenericParam gp in type.GenericParameters)
        {
            var parameter = new GenericParameter(gp.Name, definition) { Attributes = (GenericParameterAttributes)gp.Flags };
            definition.GenericParameters.Add(parameter);
            _genericParams[gp] = parameter;
        }

        foreach (TypeDef nested in type.NestedTypes.OrderBy(t => t.Token))
            CreateShell(module, nested, definition);
    }

    // ---- type references ---------------------------------------------------------------------------------------

    private static readonly (Il2CppTypeEnum Element, string Name)[] PrimitiveNames =
    [
        (Il2CppTypeEnum.Void, "System.Void"), (Il2CppTypeEnum.Boolean, "System.Boolean"), (Il2CppTypeEnum.Char, "System.Char"),
        (Il2CppTypeEnum.I1, "System.SByte"), (Il2CppTypeEnum.U1, "System.Byte"), (Il2CppTypeEnum.I2, "System.Int16"),
        (Il2CppTypeEnum.U2, "System.UInt16"), (Il2CppTypeEnum.I4, "System.Int32"), (Il2CppTypeEnum.U4, "System.UInt32"),
        (Il2CppTypeEnum.I8, "System.Int64"), (Il2CppTypeEnum.U8, "System.UInt64"), (Il2CppTypeEnum.R4, "System.Single"),
        (Il2CppTypeEnum.R8, "System.Double"), (Il2CppTypeEnum.String, "System.String"), (Il2CppTypeEnum.Object, "System.Object"),
        (Il2CppTypeEnum.I, "System.IntPtr"), (Il2CppTypeEnum.U, "System.UIntPtr"), (Il2CppTypeEnum.TypedByRef, "System.TypedReference"),
    ];

    private readonly Dictionary<Il2CppTypeEnum, TypeDefinition> _primitives = [];

    /// <summary>
    /// Marks the core library's built-in types so signatures encode them as element types (ELEMENT_TYPE_I4 and so
    /// on) rather than as ordinary type tokens. Cecil normally does this while reading an existing core library;
    /// for one built in memory its TypeSystem helper cannot be used, so the marker is set directly.
    /// </summary>
    private void MarkPrimitives()
    {
        System.Reflection.FieldInfo? etype = typeof(TypeReference).GetField("etype",
            System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);
        foreach (var (element, name) in PrimitiveNames)
        {
            if (_model.FindType(name) is not { } def || !_types.TryGetValue(def, out TypeDefinition? definition)) continue;
            _primitives[element] = definition;
            etype?.SetValue(definition, Enum.ToObject(etype.FieldType, (byte)element));
        }
        if (etype == null) Warnings.Add("Mono.Cecil internals changed: built-in types may be encoded as plain type tokens.");
    }

    private TypeReference Primitive(ModuleDefinition module, Il2CppTypeEnum element)
    {
        if (_primitives.TryGetValue(element, out TypeDefinition? definition))
            return definition.Module == module ? definition : module.ImportReference(definition);
        // No core library in the model (should not happen for a real build): fall back to Cecil's own references.
        TypeSystem ts = module.TypeSystem;
        return element switch
        {
            Il2CppTypeEnum.Void => ts.Void,
            Il2CppTypeEnum.Boolean => ts.Boolean,
            Il2CppTypeEnum.Char => ts.Char,
            Il2CppTypeEnum.I1 => ts.SByte,
            Il2CppTypeEnum.U1 => ts.Byte,
            Il2CppTypeEnum.I2 => ts.Int16,
            Il2CppTypeEnum.U2 => ts.UInt16,
            Il2CppTypeEnum.I4 => ts.Int32,
            Il2CppTypeEnum.U4 => ts.UInt32,
            Il2CppTypeEnum.I8 => ts.Int64,
            Il2CppTypeEnum.U8 => ts.UInt64,
            Il2CppTypeEnum.R4 => ts.Single,
            Il2CppTypeEnum.R8 => ts.Double,
            Il2CppTypeEnum.String => ts.String,
            Il2CppTypeEnum.I => ts.IntPtr,
            Il2CppTypeEnum.U => ts.UIntPtr,
            Il2CppTypeEnum.TypedByRef => ts.TypedReference,
            _ => ts.Object,
        };
    }

    public TypeReference Import(ModuleDefinition module, TypeDef type)
    {
        TypeDefinition definition = _types[type];
        return definition.Module == module ? definition : module.ImportReference(definition);
    }

    /// <summary>Converts a model signature into a Cecil type reference usable inside <paramref name="module"/>.</summary>
    public TypeReference Import(ModuleDefinition module, TypeSig sig)
    {
        switch (sig)
        {
            case PrimitiveSig p:
                return Primitive(module, p.Element);
            case TypeDefSig d:
                return Import(module, d.Definition);
            case GenericInstSig g:
            {
                var instance = new GenericInstanceType(Import(module, g.Definition));
                foreach (TypeSig a in g.Arguments) instance.GenericArguments.Add(Import(module, a));
                return instance;
            }
            case SzArraySig s:
                return new ArrayType(Import(module, s.ElementType));
            case ArraySig a:
                return new ArrayType(Import(module, a.ElementType), a.Rank);
            case PointerSig p:
                return new PointerType(Import(module, p.ElementType));
            case ByRefSig r:
                return new ByReferenceType(Import(module, r.ElementType));
            case GenericParamSig gp:
                return _genericParams.TryGetValue(gp.Parameter, out GenericParameter? parameter)
                    ? parameter
                    : Primitive(module, Il2CppTypeEnum.Object);
            case OpaqueSig { Kind: SigKind.FunctionPointer }:
                return Primitive(module, Il2CppTypeEnum.I); // IL2CPP itself stores function pointer types as native int
            default:
                return Primitive(module, Il2CppTypeEnum.Object);
        }
    }

    // ---- hierarchy and members ---------------------------------------------------------------------------------

    private void DefineHierarchy(TypeDef type)
    {
        TypeDefinition definition = _types[type];
        ModuleDefinition module = definition.Module;
        if (type.BaseType != null) definition.BaseType = Import(module, type.BaseType);
        foreach (TypeSig i in type.Interfaces)
            definition.Interfaces.Add(new InterfaceImplementation(Import(module, i)));
        foreach (GenericParam gp in type.GenericParameters)
            foreach (TypeSig c in gp.Constraints)
                _genericParams[gp].Constraints.Add(new GenericParameterConstraint(Import(module, c)));

        uint layout = type.Flags & TypeDef.LayoutMask;
        if (layout != 0 && !type.IsInterface)
        {
            // Both "is default" bits are clear exactly when the type had a layout row; the packing is recorded,
            // the size has to be inferred.
            if (!type.PackingSizeIsDefault || !type.ClassSizeIsDefault)
            {
                definition.PackingSize = (short)type.PackingSize;
                definition.ClassSize = SpecifiedClassSize(type);
            }
        }
    }

    /// <summary>
    /// The metadata records that a class size was specified but not its value. The real size is known, so the
    /// specified value is either that size, or 0 when the fields alone already account for it.
    /// </summary>
    private int SpecifiedClassSize(TypeDef type)
    {
        long actual = (long)type.Sizes.InstanceSize - _header;
        if (actual <= 0) return 0;
        // Compilers give a struct with no instance fields an explicit size of 1.
        if (!type.Fields.Any(f => !f.IsStatic)) return (int)actual;
        // A layout row exists either for a packing or for a size. With no packing it must be for the size.
        if (type.PackingSize == 0) return (int)actual;
        int natural = NaturalSize(type);
        return natural == actual ? 0 : (int)actual;
    }

    private (int Size, int Align) SizeAndAlign(TypeSig sig, int depth = 0)
    {
        int ptr = _model.Image.PointerSize;
        switch (sig)
        {
            case PrimitiveSig p:
            {
                int size = p.SizeOf(ptr);
                return (size, Math.Max(1, size));
            }
            case PointerSig or ByRefSig or SzArraySig or ArraySig:
                return (ptr, ptr);
            case TypeDefSig { Definition: { IsValueType: true } def } when depth < 16:
            {
                if (def.IsEnum && def.EnumUnderlyingType != null) return SizeAndAlign(def.EnumUnderlyingType, depth + 1);
                long size = (long)def.Sizes.InstanceSize - _header;
                if (size <= 0) return (-1, 1);
                int align = 1;
                foreach (FieldDef f in def.Fields)
                {
                    if (f.IsStatic) continue;
                    var (fs, fa) = SizeAndAlign(f.Type, depth + 1);
                    if (fs < 0) return (-1, 1);
                    align = Math.Max(align, fa);
                }
                if (def.PackingSize > 0) align = Math.Min(align, def.PackingSize);
                return ((int)size, align);
            }
            case TypeDefSig { Definition.IsValueType: false }:
                return (ptr, ptr);
            case GenericInstSig { Definition.IsValueType: false }:
                return (ptr, ptr);
            default:
                return (-1, 1); // generic value type instances and type parameters: not computed here
        }
    }

    /// <summary>Size the fields alone would give the type, or -1 when it cannot be determined.</summary>
    private int NaturalSize(TypeDef type)
    {
        int end = 0, align = 1;
        foreach (FieldDef f in type.Fields)
        {
            if (f.IsStatic) continue;
            var (size, fieldAlign) = SizeAndAlign(f.Type);
            if (size < 0 || f.Offset < _header) return -1;
            end = Math.Max(end, f.Offset - _header + size);
            align = Math.Max(align, fieldAlign);
        }
        if (type.PackingSize > 0) align = Math.Min(align, type.PackingSize);
        if (end == 0) return 1;
        return (end + align - 1) / align * align;
    }

    private static object? ConstantValue(object? decoded) => decoded switch
    {
        EnumConstant e => e.Value,
        TypeConstant or ArrayConstant => null,
        _ => decoded,
    };

    private void DefineMembers(TypeDef type)
    {
        TypeDefinition definition = _types[type];
        ModuleDefinition module = definition.Module;
        bool explicitLayout = (type.Flags & TypeDef.LayoutMask) == TypeDef.ExplicitLayout;

        foreach (FieldDef f in type.Fields)
        {
            var field = new FieldDefinition(f.Name, (FieldAttributes)f.Attrs, Import(module, f.Type));
            definition.Fields.Add(field);
            _fields[f] = field;

            if (f.IsLiteral && f.HasDefault)
            {
                field.Constant = ConstantValue(_blobs.ReadFieldDefault(f));
                field.HasConstant = true;
            }
            else
            {
                field.HasConstant = false;
                field.HasDefault = false;
            }

            if ((f.Attrs & FieldDef.HasFieldRva) != 0)
            {
                byte[]? data = ReadRvaData(f);
                if (data != null) field.InitialValue = data;
                else field.Attributes &= ~FieldAttributes.HasFieldRVA;
            }

            if (explicitLayout && !f.IsStatic && f.Offset >= _header) field.Offset = f.Offset - _header;
        }

        foreach (MethodDef m in type.Methods)
        {
            var method = new MethodDefinition(m.Name, (MethodAttributes)m.Flags, Primitive(module, Il2CppTypeEnum.Void))
            {
                ImplAttributes = (MethodImplAttributes)m.ImplFlags,
            };
            definition.Methods.Add(method);
            _methods[m] = method;

            foreach (GenericParam gp in m.GenericParameters)
            {
                var parameter = new GenericParameter(gp.Name, method) { Attributes = (GenericParameterAttributes)gp.Flags };
                method.GenericParameters.Add(parameter);
                _genericParams[gp] = parameter;
            }
            foreach (GenericParam gp in m.GenericParameters)
                foreach (TypeSig c in gp.Constraints)
                    _genericParams[gp].Constraints.Add(new GenericParameterConstraint(Import(module, c)));

            // C# marks "ref readonly" returns, and "in" parameters of virtual methods and delegates, with a
            // required modifier that IL2CPP does not keep. The IsReadOnly attribute it also emits survives.
            bool modifiableSignature = m.IsVirtual || type.IsDelegate;
            method.ReturnType = Import(module, m.ReturnType);
            if (m.ReturnType is ByRefSig && m.ReturnParameterToken != 0 && HasIsReadOnly(type.Assembly, m.ReturnParameterToken))
                method.ReturnType = WithInModifier(module, method.ReturnType);
            foreach (ParamDef p in m.Parameters)
            {
                TypeReference parameterType = Import(module, p.Type);
                if (modifiableSignature && p.Type is ByRefSig && p.IsIn && HasIsReadOnly(type.Assembly, p.Token))
                    parameterType = WithInModifier(module, parameterType);
                var parameter = new ParameterDefinition(p.Name, (ParameterAttributes)p.Attrs, parameterType);
                if (p.HasDefault)
                {
                    parameter.Constant = ConstantValue(_blobs.ReadParameterDefault(p));
                    parameter.HasConstant = true;
                }
                else
                {
                    parameter.HasDefault = false;
                    parameter.HasConstant = false;
                }
                method.Parameters.Add(parameter);
            }

            if (method.IsPInvokeImpl)
            {
                // The import's library and entry point are not in the metadata; placeholders keep the row valid.
                var library = module.ModuleReferences.FirstOrDefault(r => r.Name == "__Internal");
                if (library == null)
                {
                    library = new ModuleReference("__Internal");
                    module.ModuleReferences.Add(library);
                }
                method.PInvokeInfo = new PInvokeInfo(PInvokeAttributes.CallConvWinapi, m.Name, library);
            }

            if (HasIlBody(m))
            {
                method.Body = new MethodBody(method);
                ILProcessor il = method.Body.GetILProcessor();
                il.Emit(OpCodes.Ldnull);
                il.Emit(OpCodes.Throw);
            }
        }

        foreach (PropertyDef p in type.Properties)
        {
            MethodDef? accessor = p.Getter ?? p.Setter;
            if (accessor == null) continue;
            TypeSig propertyType = p.Getter != null
                ? p.Getter.ReturnType
                : p.Setter!.Parameters.Length != 0 ? p.Setter.Parameters[^1].Type : _model.Sigs.Primitive(Il2CppTypeEnum.Object);
            TypeReference propertyTypeRef = p.Getter != null ? _methods[p.Getter].ReturnType : Import(module, propertyType);
            var property = new PropertyDefinition(p.Name, (PropertyAttributes)p.Attrs, propertyTypeRef);
            if (p.Getter != null) property.GetMethod = _methods[p.Getter];
            if (p.Setter != null) property.SetMethod = _methods[p.Setter];
            property.HasThis = !accessor.IsStatic;
            definition.Properties.Add(property);
        }

        foreach (EventDef e in type.Events)
        {
            var evt = new EventDefinition(e.Name, EventAttributes.None, Import(module, e.Type));
            if (e.Add != null) evt.AddMethod = _methods[e.Add];
            if (e.Remove != null) evt.RemoveMethod = _methods[e.Remove];
            if (e.Raise != null) evt.InvokeMethod = _methods[e.Raise];
            definition.Events.Add(evt);
        }
    }

    private bool HasIsReadOnly(AssemblyModel assembly, uint token)
    {
        if (token == 0) return false;
        try
        {
            foreach (ModelAttribute a in _blobs.ReadAttributes(assembly, token))
                if (a.AttributeType.Name == "IsReadOnlyAttribute" && a.AttributeType.Namespace == "System.Runtime.CompilerServices")
                    return true;
        }
        catch (Exception e) when (e is InvalidDataException or IndexOutOfRangeException or ArgumentException)
        {
        }
        return false;
    }

    private TypeReference WithInModifier(ModuleDefinition module, TypeReference type) =>
        _model.FindType("System.Runtime.InteropServices.InAttribute") is { } inAttribute
            ? new RequiredModifierType(Import(module, inAttribute), type)
            : type;

    /// <summary>Methods implemented in IL get a body; abstract, extern, runtime and native ones do not.</summary>
    public static bool HasIlBody(MethodDef m)
    {
        const ushort CodeTypeMask = 0x3, InternalCall = 0x1000;
        if (m.IsAbstract) return false;
        if ((m.Flags & MethodDef.PInvokeImpl) != 0) return false;
        if ((m.ImplFlags & CodeTypeMask) != 0) return false;
        if ((m.ImplFlags & InternalCall) != 0) return false;
        return true;
    }

    private byte[]? ReadRvaData(FieldDef field)
    {
        if (!field.HasDefault || field.DefaultDataIndex < 0) return null;
        int size = SizeOfRvaField(field.Type);
        if (size <= 0) return null;
        ReadOnlySpan<byte> data = _model.Metadata.GetDefaultValueData(field.DefaultDataIndex);
        return data.Length < size ? null : data[..size].ToArray();
    }

    private int SizeOfRvaField(TypeSig type)
    {
        if (type is PrimitiveSig p) return p.SizeOf(_model.Image.PointerSize);
        if (type.Definition is { IsValueType: true } def)
        {
            if (def.IsEnum && def.EnumUnderlyingType is PrimitiveSig underlying)
                return underlying.SizeOf(_model.Image.PointerSize);
            long size = (long)def.Sizes.InstanceSize - _header;
            if (size > 0) return (int)size;
        }
        return 0;
    }

    // ---- explicit overrides ------------------------------------------------------------------------------------

    /// <summary>
    /// IL2CPP does not keep the MethodImpl table, but the vtable does record which method fills each interface
    /// slot. Where the implementing method's name differs from the interface method's (explicit implementation),
    /// that pairing is restored as an override.
    /// </summary>
    private void DefineOverrides(TypeDef type)
    {
        if (type.IsInterface) return;
        ModuleDefinition module = _types[type].Module;

        // A C# destructor compiles to Finalize with an explicit override of System.Object::Finalize.
        if (!type.IsValueType && _model.FindType("System.Object") is { } objectType && type != objectType)
        {
            MethodDef? objectFinalize = objectType.Methods.FirstOrDefault(m => m.Name == "Finalize" && m.Parameters.Length == 0);
            foreach (MethodDef m in type.Methods)
            {
                if (objectFinalize == null || m.Name != "Finalize" || m.Parameters.Length != 0 || !m.IsVirtual) continue;
                if ((m.Flags & MethodDef.NewSlot) != 0 || !m.ReturnType.IsVoid) continue;
                _methods[m].Overrides.Add(ImportMethod(module, objectFinalize));
            }
        }

        if (type.VTable.Length == 0) return;
        foreach (var (iface, offset) in type.InterfaceOffsets)
        {
            TypeDef? ifaceDef = iface.Definition;
            if (ifaceDef == null) continue;
            foreach (MethodDef ifaceMethod in ifaceDef.Methods)
            {
                if (!ifaceMethod.HasSlot || ifaceMethod.IsStatic) continue;
                int slot = offset + ifaceMethod.Slot;
                if (slot < 0 || slot >= type.VTable.Length) continue;
                var (impl, _) = _model.DecodeVTableEntry(type.VTable[slot]);
                if (impl == null || impl.DeclaringType != type || !impl.IsVirtual) continue;
                // A public method with the interface method's name implements it implicitly. Anything else in
                // an interface slot (different name, or not public) can only have got there by an override.
                bool isPublic = (impl.Flags & MethodDef.AccessMask) == 6;
                if (impl.Name == ifaceMethod.Name && isPublic) continue;
                MethodDefinition implDefinition = _methods[impl];
                MethodReference target = ImportMethod(module, ifaceMethod, iface);
                if (!implDefinition.Overrides.Any(o => o.FullName == target.FullName))
                    implDefinition.Overrides.Add(target);
            }
        }
    }

    /// <summary>References a method, on an instantiated generic declaring type when one is given.</summary>
    public MethodReference ImportMethod(ModuleDefinition module, MethodDef method, TypeSig? declaringType = null)
    {
        MethodDefinition definition = _methods[method];
        if (declaringType is not GenericInstSig)
            return definition.Module == module ? definition : module.ImportReference(definition);

        // A method of a generic instance keeps the definition's signature (written in terms of the type's own
        // generic parameters) and only swaps the declaring type.
        MethodReference open = definition.Module == module ? definition : module.ImportReference(definition);
        var reference = new MethodReference(open.Name, open.ReturnType, Import(module, declaringType))
        {
            HasThis = open.HasThis,
            ExplicitThis = open.ExplicitThis,
            CallingConvention = open.CallingConvention,
        };
        foreach (ParameterDefinition p in open.Parameters)
            reference.Parameters.Add(new ParameterDefinition(p.ParameterType));
        foreach (GenericParameter gp in open.GenericParameters)
            reference.GenericParameters.Add(new GenericParameter(gp.Name, reference));
        return reference;
    }

    public FieldReference ImportField(ModuleDefinition module, FieldDef field, TypeSig? declaringType = null)
    {
        FieldDefinition definition = _fields[field];
        if (declaringType is not GenericInstSig)
            return definition.Module == module ? definition : module.ImportReference(definition);
        FieldReference open = definition.Module == module ? definition : module.ImportReference(definition);
        return new FieldReference(open.Name, open.FieldType, Import(module, declaringType));
    }

    // ---- custom attributes -------------------------------------------------------------------------------------

    private void DefineAttributes()
    {
        foreach (AssemblyModel asm in _model.Assemblies)
        {
            AssemblyDefinition assembly = _assemblies[asm];
            ModuleDefinition module = assembly.MainModule;
            Apply(module, assembly, asm, 0x20000001, -1);
            foreach (TypeDef type in asm.Types)
            {
                Apply(module, _types[type], asm, type.Token, type.CustomAttributeIndex);
                foreach (FieldDef f in type.Fields) Apply(module, _fields[f], asm, f.Token, f.CustomAttributeIndex);
                foreach (MethodDef m in type.Methods)
                {
                    MethodDefinition method = _methods[m];
                    Apply(module, method, asm, m.Token, m.CustomAttributeIndex);
                    for (int i = 0; i < m.Parameters.Length; i++)
                        Apply(module, method.Parameters[i], asm, m.Parameters[i].Token, m.Parameters[i].CustomAttributeIndex);
                }
                TypeDefinition definition = _types[type];
                for (int i = 0; i < type.Properties.Length && i < definition.Properties.Count; i++)
                    Apply(module, definition.Properties[i], asm, type.Properties[i].Token, type.Properties[i].CustomAttributeIndex);
                for (int i = 0; i < type.Events.Length && i < definition.Events.Count; i++)
                    Apply(module, definition.Events[i], asm, type.Events[i].Token, type.Events[i].CustomAttributeIndex);
            }
        }
    }

    private void Apply(ModuleDefinition module, ICustomAttributeProvider target, AssemblyModel asm, uint token, int legacyIndex)
    {
        if (token == 0 && legacyIndex < 0) return;
        List<ModelAttribute> attributes;
        try
        {
            attributes = _blobs.ReadAttributes(asm, token, legacyIndex);
        }
        catch (Exception e) when (e is InvalidDataException or IndexOutOfRangeException or ArgumentException)
        {
            return;
        }

        foreach (ModelAttribute a in attributes)
        {
            MethodDef? ctor = a.Constructor;
            if (ctor == null)
            {
                // Pre-v29 metadata names only the attribute type; it can be kept when a parameterless
                // constructor exists.
                ctor = a.AttributeType.Methods.FirstOrDefault(m => m.Name == ".ctor" && m.Parameters.Length == 0);
                if (ctor == null) continue;
            }
            try
            {
                var attribute = new CecilAttribute(ImportMethod(module, ctor));
                if (a.HasArguments)
                {
                    if (a.Arguments.Length != ctor.Parameters.Length) continue;
                    for (int i = 0; i < a.Arguments.Length; i++)
                        attribute.ConstructorArguments.Add(Argument(module, ctor.Parameters[i].Type, a.Arguments[i]));
                    foreach (var (field, value) in a.Fields)
                        attribute.Fields.Add(new CustomAttributeNamedArgument(field.Name, Argument(module, field.Type, value)));
                    foreach (var (property, value) in a.Properties)
                    {
                        TypeSig? type = property.Getter?.ReturnType ??
                                        (property.Setter is { Parameters.Length: > 0 } s ? s.Parameters[^1].Type : null);
                        if (type != null)
                            attribute.Properties.Add(new CustomAttributeNamedArgument(property.Name, Argument(module, type, value)));
                    }
                }
                target.CustomAttributes.Add(attribute);
            }
            catch (Exception e) when (e is InvalidOperationException or ArgumentException or InvalidCastException)
            {
                Warnings.Add($"attribute {a.AttributeType.FullName} on token 0x{token:X8}: {e.Message}");
            }
        }
    }

    private TypeReference PrimitiveForValue(ModuleDefinition module, object value) => Primitive(module, value switch
    {
        bool => Il2CppTypeEnum.Boolean,
        char => Il2CppTypeEnum.Char,
        sbyte => Il2CppTypeEnum.I1,
        byte => Il2CppTypeEnum.U1,
        short => Il2CppTypeEnum.I2,
        ushort => Il2CppTypeEnum.U2,
        int => Il2CppTypeEnum.I4,
        uint => Il2CppTypeEnum.U4,
        long => Il2CppTypeEnum.I8,
        ulong => Il2CppTypeEnum.U8,
        float => Il2CppTypeEnum.R4,
        double => Il2CppTypeEnum.R8,
        string => Il2CppTypeEnum.String,
        _ => Il2CppTypeEnum.Object,
    });

    private TypeReference SystemType(ModuleDefinition module) =>
        _model.FindType("System.Type") is { } t ? Import(module, t) : Primitive(module, Il2CppTypeEnum.Object);

    /// <summary>Wraps a decoded constant in the shape Cecil expects for the declared parameter type.</summary>
    private CustomAttributeArgument Argument(ModuleDefinition module, TypeSig declared, object? value)
    {
        TypeReference declaredRef = Import(module, declared);
        bool declaredIsObject = declared is PrimitiveSig { Element: Il2CppTypeEnum.Object };

        CustomAttributeArgument Typed()
        {
            switch (value)
            {
                case null:
                    return new CustomAttributeArgument(declaredIsObject ? Primitive(module, Il2CppTypeEnum.String) : declaredRef, null);
                case EnumConstant e:
                    return new CustomAttributeArgument(Import(module, e.EnumType), e.Value);
                case TypeConstant t:
                    return new CustomAttributeArgument(SystemType(module), Import(module, t.Type));
                case ArrayConstant a:
                {
                    TypeSig elementSig = declared is SzArraySig sz
                        ? sz.ElementType
                        : a.ElementEnumType != null
                            ? a.ElementEnumType.Sig
                            : _model.Sigs.Primitive(a.ElementType);
                    var items = new CustomAttributeArgument[a.Items.Length];
                    for (int i = 0; i < items.Length; i++) items[i] = Argument(module, elementSig, a.Items[i]);
                    return new CustomAttributeArgument(new ArrayType(Import(module, elementSig)), items);
                }
                default:
                    return new CustomAttributeArgument(declaredIsObject ? PrimitiveForValue(module, value) : declaredRef, value);
            }
        }

        CustomAttributeArgument typed = Typed();
        // An argument declared as object carries its real type in a nested argument.
        return declaredIsObject ? new CustomAttributeArgument(Primitive(module, Il2CppTypeEnum.Object), typed) : typed;
    }

    // ---- output ------------------------------------------------------------------------------------------------

    /// <summary>Writes every assembly as a .dll into <paramref name="directory"/>.</summary>
    public List<string> Write(string directory)
    {
        Directory.CreateDirectory(directory);
        var written = new List<string>();
        foreach (AssemblyModel asm in _model.Assemblies)
        {
            string path = Path.Combine(directory, asm.ImageName.EndsWith(".dll", StringComparison.OrdinalIgnoreCase)
                ? asm.ImageName
                : asm.ImageName + ".dll");
            try
            {
                // The same game gives the same files, byte for byte: no time of writing in them, and the module's
                // id worked out from its contents instead of made up.
                _assemblies[asm].Write(path, new WriterParameters { DeterministicMvid = true, Timestamp = 0 });
                written.Add(path);
            }
            catch (Exception e)
            {
                Warnings.Add($"{asm.Name}: could not be written: {e.GetType().Name}: {e.Message}");
            }
        }
        return written;
    }
}
