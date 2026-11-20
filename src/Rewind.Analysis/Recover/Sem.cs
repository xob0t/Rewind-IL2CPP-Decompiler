// Modified by xob0t (2026): objects copied into a merge before their constructor runs. See FORK.md.
using Rewind.Analysis.Hir;
using Rewind.Analysis.Ir;
using Rewind.Model;

namespace Rewind.Analysis.Recover;

/// <summary>What a machine-level value means in managed terms.</summary>
internal abstract class Sem;

/// <summary>An ordinary managed value: number, reference, struct. The expression says how to obtain it.</summary>
internal sealed class SVal(HExpr expr) : Sem
{
    public HExpr Expr = expr;
    public TypeSig? Type => Expr.Type;
}

/// <summary>A managed pointer to a storage location of a known type: a struct "this", a ref argument, &amp;local, &amp;obj.field.</summary>
internal sealed class SRef(HExpr location, TypeSig type) : Sem
{
    /// <summary>The location itself (reading it yields the value; HAddressOf of it yields the pointer).</summary>
    public HExpr Location = location;
    public TypeSig Type = type;
}

/// <summary>Il2CppClass* of a statically known type (from a metadata slot).</summary>
internal sealed class SKlass(TypeSig type) : Sem
{
    public TypeSig Type = type;
}

/// <summary>Il2CppClass* read from an object's header: the object's run-time class.</summary>
internal sealed class SObjKlass(Node obj) : Sem
{
    public Node Object = obj;
}

/// <summary>Pointer to a class's static field block.</summary>
internal sealed class SStatics(TypeSig type) : Sem
{
    public TypeSig Type = type;
}

/// <summary>The vtable entry that implements one slot of an interface for an object's run-time class.</summary>
internal sealed class SInterfaceEntry(Node obj, TypeSig iface, int slot) : Sem
{
    public Node Object = obj;
    public TypeSig Interface = iface;
    public int Slot = slot;
}

/// <summary>One half of a vtable entry of an object's run-time class.</summary>
internal sealed class SVTable(Node obj, int slot, bool methodInfo) : Sem
{
    public Node Object = obj;
    public int Slot = slot;
    /// <summary>Set when the slot is a slot of this interface rather than of the class's own vtable.</summary>
    public TypeSig? Interface;
    /// <summary>False: the code pointer. True: the MethodInfo* passed as the hidden last argument.</summary>
    public bool MethodInfo = methodInfo;
}

/// <summary>The native implementation of an "extern" method: what calls to it go through.</summary>
/// <summary>
/// Bytes [Offset, Offset + Size) of a struct value, read while the struct was copied in pieces that are not its
/// fields (a union moved eight bytes at a time). Snapshot holds the whole struct as it was when read.
/// </summary>
internal sealed class SChunk(HVar snapshot, TypeSig type, int offset, int size) : Sem
{
    public HVar Snapshot = snapshot;
    public TypeSig Type = type;
    public int Offset = offset, Size = size;
}

/// <summary>The native function a P/Invoke declaration imports: calling it is calling the declaration (with marshaled arguments).</summary>
internal sealed class SPInvoke(MethodDef method) : Sem
{
    public MethodDef Method = method;
}

internal sealed class SNativeCode(MethodDef method) : Sem
{
    public MethodDef Method = method;
}

/// <summary>MethodInfo* constant.</summary>
internal sealed class SMethod(MethodDef method, MethodInst? inst) : Sem
{
    public MethodDef Method = method;
    public MethodInst? Inst = inst;
}

/// <summary>
/// The code pointer read out of a method's runtime record. Unity 2021 calls from code shared between
/// instantiations this way ("il2cpp_codegen_get_method_pointer(method)(arguments, method)"): calling it is
/// calling the method.
/// </summary>
internal sealed class SMethodCode(MethodDef method, MethodInst? inst) : Sem
{
    public MethodDef Method = method;
    public MethodInst? Inst = inst;
}

/// <summary>
/// The runtime generic context of an instantiated generic class or method: the table of classes, types and
/// methods its shared code needs, for these type arguments.
/// </summary>
internal sealed class SRgctx(IReadOnlyList<Rewind.Runtime.RgctxItem> items, TypeSig[] classArguments, TypeSig[] methodArguments) : Sem
{
    public IReadOnlyList<Rewind.Runtime.RgctxItem> Items = items;
    public TypeSig[] ClassArguments = classArguments, MethodArguments = methodArguments;
}

/// <summary>Il2CppType* constant (what ldtoken yields for a type).</summary>
internal sealed class SType(TypeSig type) : Sem
{
    public TypeSig Type = type;
}

/// <summary>FieldInfo* constant (what ldtoken yields for a field).</summary>
internal sealed class SFieldInfo(FieldDef field) : Sem
{
    public FieldDef Field = field;
}

/// <summary>Raw address inside the stack frame that has not (yet) been tied to a typed local.</summary>
internal sealed class SFrame(int offset) : Sem
{
    public int Offset = offset;
}

/// <summary>Low or high 32 bits of a 64-bit quantity that is one managed value (a double, or two packed floats).</summary>
internal sealed class SHalf(HExpr whole, bool high, HExpr? part) : Sem
{
    /// <summary>The 64-bit value this is half of.</summary>
    public HExpr Whole = whole;
    public bool High = high;
    /// <summary>When the 64 bits are really two separate 4-byte values, this half's own expression.</summary>
    public HExpr? Part = part;
}

/// <summary>Two independent 4-byte values travelling together in 64 bits (how compilers move pairs of floats).</summary>
internal sealed class SPair(HExpr low, HExpr high) : Sem
{
    public HExpr Low = low, High = high;
}

/// <summary>Pointer to the payload of a boxed value (result of the unbox helper).</summary>
internal sealed class SUnboxed(Node obj) : Sem
{
    public Node Object = obj;
}

/// <summary>A freshly allocated object whose constructor has not been seen yet.</summary>
internal sealed class SNewObject(TypeSig type, HVar variable) : Sem
{
    public TypeSig Type = type;
    public HVar Variable = variable;
    public bool Constructed;
    /// <summary>The statement that stands for the bare allocation until a constructor call replaces it.</summary>
    public HAssign? Allocation;
    /// <summary>
    /// The object was copied into a merged value before its constructor ran (the register allocator moved the
    /// allocation's result to where a later merge wants it, ahead of the call). "new T(args)" at the call would
    /// leave those copies with what the variable held before.
    /// </summary>
    public bool CopiedEarly;
    /// <summary>The "o = new T(args)" each constructor call that claimed the object made, with its block and the same
    /// call on the raw object, for when the allocation has to stay (HirBuilder.SettleNewObjects).</summary>
    public List<(HBlock Block, HAssign Made, HCall OnRaw)> Claims = [];
    /// <summary>Where each claiming constructor call is: its block and the clock of its node (HirBuilder._nodeClock).</summary>
    public List<(Block Block, long Clock)> ClaimSites = [];
    /// <summary>
    /// Where the object was read while the blocks were built (stores through it, copies into merges, arguments): per
    /// block, the clock of the first read there. "new T(args)" can stand for the allocation only when the claiming
    /// call comes before every one of them (HirBuilder.ClaimComesFirst).
    /// </summary>
    public Dictionary<Block, long> Uses = [];

    public void NoteUse(Block block, long clock)
    {
        if (!Uses.TryGetValue(block, out long first) || clock < first) Uses[block] = clock;
    }
    /// <summary>
    /// More than one constructor call claimed the object: MSVC put one allocation before a branch and a
    /// constructor call on each arm. "new T(args)" on one arm would leave the other arm's call nothing allocated.
    /// </summary>
    public bool Shared;
}

/// <summary>How deep a class sits in its inheritance chain: of a known type, or of an object's run-time class.</summary>
internal sealed class SDepth(TypeSig? type, Node? obj) : Sem
{
    public TypeSig? Type = type;
    public Node? Object = obj;
}

/// <summary>The list of base classes of an object's run-time class.</summary>
internal sealed class SHierarchy(Node obj) : Sem
{
    public Node Object = obj;
}

/// <summary>
/// The base class an object's run-time class has at the depth of a known type. It is that type exactly when
/// the object is an instance of it: how generated code tests "is" for classes that can be derived from.
/// </summary>
internal sealed class SHierarchyEntry(Node obj, TypeSig type) : Sem
{
    public Node Object = obj;
    public TypeSig Type = type;
}

/// <summary>A value with no managed meaning (undefined register contents, the hidden MethodInfo argument).</summary>
internal class SJunk : Sem
{
    public static readonly SJunk Instance = new();
}

/// <summary>
/// A callee-saved register the protected code changes, as a catch handler sees it: what it held at the call that
/// raised the exception, which one path into the handler cannot say. Junk like any other until something uses it:
/// a catch handler saves such registers on entry, and a call captures whatever its stack slots held, without
/// either meaning anything.
/// </summary>
internal sealed class SLostRegister : SJunk
{
    public new static readonly SLostRegister Instance = new();
}

/// <summary>
/// What shared code hands a method it calls through a constraint ("constrained. T; callvirt Dispose", as a
/// foreach over a struct enumerator ends): the runtime's record of that method as the type has it. No value
/// of the program, but it says which type the call is made on.
/// </summary>
internal sealed class SConstrained(TypeSig on) : SJunk
{
    public TypeSig On = on;
}
