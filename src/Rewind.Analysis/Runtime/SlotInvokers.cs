// Added by xob0t (2026): slot-specialized invokers. See FORK.md.
using Iced.Intel;
using Rewind.Analysis.X64;

namespace Rewind.Analysis.Runtime;

/// <summary>Where one argument a slot invoker hands on comes from: one of its own arguments (by position), or a constant.</summary>
public readonly record struct InvokerSource(bool IsConstant, int Position, long Constant);

/// <summary>
/// A copy of IL2CPP's "VirtualActionInvokerN/VirtualFuncInvokerN::Invoke(slot, obj, args...)" made for one call
/// site's slot: whole-program optimization (MSVC's LTCG) specializes the invoker for a slot that is the same at
/// every call, so the slot argument is no longer read - the code takes the method from that slot of the
/// object's class and calls it, each of its own arguments moved down one position, and arguments that were the
/// same at every call written in as constants. No library can name such a copy: its arguments are the
/// program's own. It is told by its code.
/// </summary>
public sealed class SlotInvoker
{
    /// <summary>The slot in the class's table whose method is called.</summary>
    public int Slot;
    /// <summary>How many argument positions the invoker itself takes (slot and object included).</summary>
    public int Count;
    /// <summary>Of the register positions (0-3): those the invoker reads from a floating point register.</summary>
    public bool[] FloatIn = new bool[4];
    /// <summary>The position in the called method's arguments where its method record goes: one past the last argument.</summary>
    public int MethodInfoPosition;
    /// <summary>
    /// Per position of the called method's arguments: where the value in the integer register (or, past the
    /// registers, on the stack) comes from, and where the value in the floating point register does. Null:
    /// nothing the invoker was handed, or nothing at all.
    /// </summary>
    public InvokerSource?[] IntSources = [], FloatSources = [];
    /// <summary>The invoker jumps to the method rather than calling it.</summary>
    public bool Tail;

    private enum Kind { Unknown, Param, Const, Klass, Entry, Frame }

    private readonly record struct Value(Kind Kind, long N = 0, bool Float = false)
    {
        public static readonly Value Unknown = new(Kind.Unknown);
    }

    private static readonly Register[] IntArgs = [Register.RCX, Register.RDX, Register.R8, Register.R9];

    /// <summary>
    /// The specialized invoker at <paramref name="address"/>, or null when the code there is anything else.
    /// Windows x64 only: straight-line code that reads the class of the object (the second argument), moves
    /// arguments and constants into place, and calls or jumps through one entry of the class's table. Any
    /// instruction it does not know the effect of makes it no invoker.
    /// </summary>
    public static SlotInvoker? Recognize(ICodeContext context, KlassLayout klass, ulong address)
    {
        X64Cfg cfg = X64Cfg.Build(context, address);
        if (cfg.Problems.Count != 0 || cfg.Blocks.Count is 0 or > 4) return null;
        var code = cfg.Blocks.OrderBy(b => b.Start).SelectMany(b => b.Instructions).ToList();
        if (code.Count is < 3 or > 160) return null;

        var regs = new Dictionary<Register, Value>();
        var xmm = new Dictionary<int, Value>();
        var stack = new Dictionary<long, Value>();
        for (int k = 0; k < 4; k++)
        {
            regs[IntArgs[k]] = new Value(Kind.Param, k);
            xmm[k] = new Value(Kind.Param, k, Float: true);
        }
        long sp = 0; // relative to the stack pointer on entry, where the return address is
        long? calledAt = null;
        bool tail = false;
        long spAtCall = 0;
        Dictionary<Register, Value>? regsAtCall = null;
        Dictionary<int, Value>? xmmAtCall = null;
        Dictionary<long, Value>? stackAtCall = null;

        // What of its own arguments the invoker reads, and from which kind of register: what a caller hands it.
        bool[] readInt = new bool[4], readFloat = new bool[4];
        int highest = 1;
        Value Read(Value v, bool viaFloat)
        {
            if (v.Kind != Kind.Param) return v;
            highest = Math.Max(highest, (int)v.N);
            if (v.N < 4) (viaFloat ? readFloat : readInt)[v.N] = true;
            return v;
        }
        Value RegValue(Register r) => Read(regs.TryGetValue(r.GetFullRegister(), out Value v) ? v : Value.Unknown, false);
        Value XmmValue(Register r) => Read(xmm.TryGetValue(r.GetNumber(), out Value v) ? v : Value.Unknown, true);

        long? AddressOf(in Instruction i)
        {
            if (i.MemoryIndex != Register.None || i.MemorySegment is not (Register.SS or Register.DS)) return null;
            long disp = (long)i.MemoryDisplacement64;
            if (i.MemoryBase == Register.RSP) return sp + disp;
            if (RegValue(i.MemoryBase) is { Kind: Kind.Frame } frame) return frame.N + disp;
            return null;
        }

        Value Load(in Instruction i)
        {
            if (i.MemoryIndex != Register.None) return Value.Unknown;
            Value b = RegValue(i.MemoryBase);
            long disp = (long)i.MemoryDisplacement64;
            if (b.Kind == Kind.Param && b.N == 1 && !b.Float && disp == 0 && i.MemorySize == MemorySize.UInt64) return new Value(Kind.Klass);
            if (b.Kind == Kind.Klass) return new Value(Kind.Entry, disp);
            if (AddressOf(i) is not { } at) return Value.Unknown;
            if (stack.TryGetValue(at, out Value kept)) return kept;
            // An argument of the invoker's own past the registers (above the return address and the home area).
            if (at >= 8 + 8 * 4 && (at - 8) % 8 == 0) return Read(new Value(Kind.Param, (at - 8) / 8), false);
            return Value.Unknown;
        }

        bool Store(in Instruction i, Value v)
        {
            if (AddressOf(i) is not { } at) return false;
            stack[at] = v;
            return true;
        }

        foreach (Instruction i in code)
        {
            if (calledAt != null)
            {
                // After the call: only the frame is given back, then the method's result is the invoker's.
                if (i.Mnemonic == Mnemonic.Add && i.Op0Register == Register.RSP && i.Op1Kind is OpKind.Immediate8to64 or OpKind.Immediate32to64) continue;
                if (i.Mnemonic == Mnemonic.Ret) break;
                return null;
            }
            switch (i.Mnemonic)
            {
                case Mnemonic.Nop:
                    continue;
                case Mnemonic.Sub or Mnemonic.Add when i.Op0Kind == OpKind.Register && i.Op0Register == Register.RSP:
                    if (i.Op1Kind is not (OpKind.Immediate8to64 or OpKind.Immediate32to64)) return null;
                    sp += i.Mnemonic == Mnemonic.Sub ? -(long)i.GetImmediate(1) : (long)i.GetImmediate(1);
                    continue;
                case Mnemonic.Lea when i.Op0Kind == OpKind.Register:
                    regs[i.Op0Register.GetFullRegister()] = AddressOf(i) is { } frameAddress ? new Value(Kind.Frame, frameAddress) : Value.Unknown;
                    continue;
                case Mnemonic.Xor or Mnemonic.Sub when i.Op0Kind == OpKind.Register && i.Op1Kind == OpKind.Register && i.Op0Register == i.Op1Register && i.Op0Register.IsGPR():
                    regs[i.Op0Register.GetFullRegister()] = new Value(Kind.Const, 0);
                    continue;
                case Mnemonic.Xorps or Mnemonic.Xorpd or Mnemonic.Pxor when i.Op0Kind == OpKind.Register && i.Op1Kind == OpKind.Register && i.Op0Register == i.Op1Register:
                    xmm[i.Op0Register.GetNumber()] = new Value(Kind.Const, 0, Float: true);
                    continue;
                case Mnemonic.Mov or Mnemonic.Movzx or Mnemonic.Movsx or Mnemonic.Movsxd:
                {
                    if (i.Op0Kind == OpKind.Register && i.Op0Register.IsGPR())
                    {
                        Register to = i.Op0Register.GetFullRegister();
                        if (i.Op1Kind == OpKind.Register)
                            regs[to] = i.Op1Register == Register.RSP ? new Value(Kind.Frame, sp) : RegValue(i.Op1Register);
                        else if (i.Op1Kind == OpKind.Memory) regs[to] = Load(i);
                        else if (i.Op1Kind is OpKind.Immediate8 or OpKind.Immediate16 or OpKind.Immediate32 or OpKind.Immediate64 or OpKind.Immediate32to64 or OpKind.Immediate8to32 or OpKind.Immediate8to64)
                            regs[to] = new Value(Kind.Const, (long)i.GetImmediate(1));
                        else return null;
                        continue;
                    }
                    if (i.Op0Kind == OpKind.Memory && i.Mnemonic == Mnemonic.Mov)
                    {
                        Value v = i.Op1Kind == OpKind.Register ? RegValue(i.Op1Register)
                            : i.Op1Kind is OpKind.Immediate8 or OpKind.Immediate16 or OpKind.Immediate32 or OpKind.Immediate32to64
                                ? new Value(Kind.Const, i.MemorySize switch
                                {
                                    MemorySize.UInt8 or MemorySize.Int8 => (sbyte)i.GetImmediate(1),
                                    MemorySize.UInt16 or MemorySize.Int16 => (short)i.GetImmediate(1),
                                    MemorySize.UInt32 or MemorySize.Int32 => (int)i.GetImmediate(1),
                                    _ => (long)i.GetImmediate(1),
                                })
                                : Value.Unknown;
                        if (v.Kind == Kind.Unknown || !Store(i, v)) return null;
                        continue;
                    }
                    return null;
                }
                case Mnemonic.Movsd or Mnemonic.Movss or Mnemonic.Movaps or Mnemonic.Movapd or Mnemonic.Movups or Mnemonic.Movupd
                    or Mnemonic.Movdqa or Mnemonic.Movdqu or Mnemonic.Movq:
                {
                    bool toXmm = i.Op0Kind == OpKind.Register && i.Op0Register.IsXMM();
                    if (toXmm)
                    {
                        Value v = i.Op1Kind == OpKind.Memory ? Load(i)
                            : i.Op1Kind == OpKind.Register && i.Op1Register.IsXMM() ? XmmValue(i.Op1Register)
                            : i.Op1Kind == OpKind.Register && i.Op1Register.IsGPR() ? RegValue(i.Op1Register)
                            : Value.Unknown;
                        xmm[i.Op0Register.GetNumber()] = v;
                        continue;
                    }
                    if (i.Op0Kind == OpKind.Memory && i.Op1Kind == OpKind.Register && i.Op1Register.IsXMM())
                    {
                        Value v = XmmValue(i.Op1Register);
                        if (v.Kind == Kind.Unknown || !Store(i, v)) return null;
                        continue;
                    }
                    if (i.Op0Kind == OpKind.Register && i.Op0Register.IsGPR() && i.Op1Kind == OpKind.Register && i.Op1Register.IsXMM())
                    {
                        regs[i.Op0Register.GetFullRegister()] = XmmValue(i.Op1Register);
                        continue;
                    }
                    return null;
                }
                case Mnemonic.Call or Mnemonic.Jmp when i.Op0Kind == OpKind.Memory && i.MemoryIndex == Register.None && RegValue(i.MemoryBase).Kind == Kind.Klass:
                {
                    calledAt = (long)i.MemoryDisplacement64;
                    tail = i.Mnemonic == Mnemonic.Jmp;
                    if (tail && sp != 0) return null;
                    spAtCall = sp;
                    regsAtCall = new Dictionary<Register, Value>(regs);
                    xmmAtCall = new Dictionary<int, Value>(xmm);
                    stackAtCall = new Dictionary<long, Value>(stack);
                    if (tail) goto done;
                    continue;
                }
                default:
                    return null;
            }
        }
        done:
        if (calledAt is not { } entryAt || regsAtCall == null || xmmAtCall == null || stackAtCall == null) return null;
        long rel = entryAt - klass.VTable;
        if (rel < 0 || klass.VTableEntrySize <= 0 || rel % klass.VTableEntrySize != 0) return null;

        // Where the callee finds its argument at a position: in a register, or on the stack above its return address.
        long StackOf(int position) => tail ? 8 + 8L * position : spAtCall + 8L * position;
        Value IntAt(int position)
        {
            if (position < 4) return regsAtCall.TryGetValue(IntArgs[position], out Value v) ? v : Value.Unknown;
            if (stackAtCall.TryGetValue(StackOf(position), out Value s)) return s;
            // (A tail call leaves the invoker's own stack arguments where they are: then they are the callee's.)
            return tail ? new Value(Kind.Param, position) : Value.Unknown;
        }
        Value FloatAt(int position) => position < 4 ? (xmmAtCall.TryGetValue(position, out Value v) ? v : Value.Unknown) : IntAt(position);

        // The method record (the entry after the code pointer) goes after the last argument.
        int methodInfo = -1;
        for (int position = 0; position < 32 && methodInfo < 0; position++)
            if (IntAt(position) is { Kind: Kind.Entry } e && e.N == entryAt + klass.VTableEntrySize / 2) methodInfo = position;
        if (methodInfo < 1) return null;
        // The object the class was read from is what the method is called on.
        if (IntAt(0) is not { Kind: Kind.Param, N: 1, Float: false }) return null;

        InvokerSource? Source(Value v) => v.Kind switch
        {
            Kind.Param => new InvokerSource(false, (int)v.N, 0),
            Kind.Const => new InvokerSource(true, 0, v.N),
            _ => null,
        };
        var result = new SlotInvoker
        {
            Slot = (int)(rel / klass.VTableEntrySize),
            MethodInfoPosition = methodInfo,
            IntSources = new InvokerSource?[methodInfo],
            FloatSources = new InvokerSource?[methodInfo],
            Tail = tail,
        };
        for (int position = 0; position < methodInfo; position++)
        {
            result.IntSources[position] = Source(IntAt(position));
            result.FloatSources[position] = Source(FloatAt(position));
        }
        // (An argument read both ways is no argument of one kind: what it is is not known.)
        for (int k = 0; k < 4; k++)
        {
            if (readInt[k] && readFloat[k]) return null;
            result.FloatIn[k] = readFloat[k];
        }
        result.Count = highest + 1;
        return result;
    }
}
