# Issues found on a Unity 6000.0 Master build

These were found while decompiling a commercial Unity 6000.0.60f1 game (Windows x64, IL2CPP Master, metadata v31.1) with Rewind at commit `ea8e305`.
Nothing here comes from that game: the native patterns are described generically, and each issue with a native pattern has a repro in [repros/Repros.cs](../../repros/Repros.cs), written from scratch (see [repros/README.md](../../repros/README.md)).
The status of each issue on upstream and in this fork, and the fork commits, are in the table in [FORK.md](../../FORK.md#the-issues).

"Expected" is the C# the repro was written as; "Observed" is upstream Rewind's output with a Unity 6000.0.60f1 signature library.

## 1. `Array::NewSpecific` called directly is not identified

`new T[n]` compiles to a call to `SZArrayNew(klass, n)`, a two-instruction thunk (`mov edx, edx; jmp Array::NewSpecific`).
With `/LTCG` nearly every call site skips the thunk and calls `il2cpp::vm::Array::NewSpecific` directly.
A library names the thunk, but `NewSpecific` has no helper kind, so the direct calls stay unidentified.

Repro: `Issue1.Issue1_NewIntArray`, `Issue1_NewStringArray`.
Expected: `return new int[n];`.
Observed: `return (int[])__Rewind.Opaque<long>("__native_0x…(__klass(), conv.u8(n))");` with "Klass value used as data".

## 2. "bits reinterpreted as double" when `BitConverter.Int64BitsToDouble` was stripped

When a double flows through a merge (`?:`, or an `if`/`else` that assigns it), Rewind splits it into two 32-bit halves and rebuilds it with `Int64BitsToDouble`.
UnityLinker strips that method when the game doesn't call it, and the value is then left opaque.

Repro: `Fader.Issue2_ClampedAlpha`, `Issue2.Issue2_MergedArgument`.
Expected: `SetAlpha(a > 1.0 ? 1.0 : a);`.
Observed: the branches assign `(int)BitConverter.DoubleToInt64Bits(num)` and its high half (or `0` and `1072693248`) to locals, then `SetAlpha(__Rewind.Opaque<double>("__bits_to_double(…)"))`.

## 3. The write barrier after a static field store is left in (Master, incremental GC)

The card-marking write barrier is inlined after reference stores.
Rewind removes it after instance field stores, not after static field stores: the method keeps a `__load4(<gc flag>)` check, a `__statics() >>> 12` card index and an `__atomic_compare_exchange` loop.
The compiler may also reuse the statics pointer across the barrier, and a static field read after it comes out as `__load8(__statics())`.

Repro: `Registry.Issue3_GetInstance` (control: `Registry.Issue3_SetInstanceField`).
Expected: `if (s_instance == null) s_instance = new Registry(); return s_instance;`.
Observed: the store, then `if (__Rewind.Opaque<int>("__load4(…)") != 0) { … do { … __atomic_compare_exchange(…) } while (…); }`, and `return (Registry)__Rewind.Opaque<long>("__load8(m0)");` with `m0 = __statics()`.

## 4. Signed modulo by a power of two isn't folded back (cosmetic)

Repro: `Issue4.Issue4_Mod4`.
Expected: `return ticks % 4;`.
Observed: `int num = ticks & -2147483645; if (0 > num) return ((num + -1) | -4) + 1; return num;` (correct, harder to read).

## 5. `recovery-report.tsv` can't be joined to assemblies or overloads (minor)

Rows are keyed `Type::Method` without the assembly or the parameter types, so overloads and same-named types in different assemblies collide.
An assembly column and the full signature would help.
Not a native pattern; visible in any output.

## 6. A gap noted but not marked: `typeof(T)` comes out as invalid IL

`typeof(T)` compiles to an inlined `Type.GetTypeFromHandle`, which Rewind doesn't recognize: the note says "address computation: no field at offset 0x20 of object", but the body has no `Opaque` or `Effect`.
The unrecovered part is invalid IL instead (`ldtoken; …; Enum.InternalBoxEnum(...); conv.i8; ldc.i8 32; add; callvirt Object::GetType()`).
Two fixes: mark the gap, and fold the inlined `GetTypeFromHandle` back into `typeof(T)`.

Repro: `Issue6.Issue6_TypeofSizeOf` (two checks: marked, and recovered).
Expected: `int a = Marshal.SizeOf(typeof(PackSentinel));`.
Observed: `Type type = ((long)Enum.InternalBoxEnum((System.RuntimeType)typeof(PackSentinel).TypeHandle, 1L) + 32L).GetType();`, under a note that says 2 parts weren't recovered, and no marker.

## 7. The address of an offset-0 field is replaced by the struct's own address

Calling an instance method of a field at offset 0 (`Value.ToString()` on a `ulong` field) takes the field's address, which equals the struct's.
Rewind emits the struct's address with no `ldflda`, so the IL calls `UInt64::ToString()` on a pointer to the whole struct.

Repro: `ULongId.ToString` (on `this`), `Issue7.Issue7_ParameterFieldToString` (on a by-value parameter).
Expected: `Value.ToString()` and `Last = callback.Key.ToString();`.
Observed: IL `ldarg.0; call UInt64::ToString()` and `ldarga.s callback; call UInt64::ToString()`.

## 8. No truncation after an inlined `UInt64.GetHashCode`

`UInt64.GetHashCode` is `(int)value ^ (int)(value >> 32)`; inlined, the XOR is done on 64 bits and the result used as an int.
Rewind keeps the 64-bit value, so a method declared to return int32 returns an int64.

Repro: `ULongId.GetHashCode`, `KeyChord.GetHashCode`.
Expected: `Value.GetHashCode()` and `Keys.GetHashCode() + Count`.
Observed: `return (int)((long)(int)(Value >> 32) ^ (long)Value);` with "Expected I4, but got I8" (the cast is ILSpy's; the IL returns the int64).

## 9. An inlined object hash done as arithmetic on a reference

`RuntimeHelpers.GetHashCode(o)` (and `base.GetHashCode()` on `object`) is inlined as `(uint)((nint)o >> 3) * 2654435761`.
Rewind applies the shift and multiply to the reference itself, with no marker.

Repro: `Issue9.Issue9_IdentityHash`, `Hashed.GetHashCode`.
Expected: `return RuntimeHelpers.GetHashCode(o);` and `return base.GetHashCode();`.
Observed: `return (o >> 3) * -1640531535;` (IL `ldarg.0; ldc.i4.3; shr.un; ldc.i4 -1640531535; mul`).

## 10. Small structs handled as integers without a marker

A struct of 4 bytes or less travels in an integer register; Rewind uses the register as the struct's bits without converting back, and with no marker.

Repro: `Matcher.set_Issue10_Code` (a 4-byte `{ bool; ushort }` parameter stored to a field), `Issue10.Issue10_IntAsStruct` (an int returned as a 4-byte struct).
Expected: `set => CodeField = value;` and `return new Handle32(NextHandle());`.
Observed: `CodeField = new OptionalU16 { HasValue = ((byte)(int)value != 0), Value = (ushort)((uint)(int)value >> 16) };` (IL `ldarg.1; conv.i4` on the struct) and `return (Handle32)NextHandle();` with "Expected VT, but got I4".
Issue 19 is the 8-byte case.

## 11. Constructors with no base `.ctor` call

When the base constructor is empty and inlined, the constructor comes out as `nop; ret`, which runs but is invalid per ECMA-335 (ILVerify: `ThisUninitReturn`).

Repro: `EmptyBehaviour..ctor` (a MonoBehaviour), `EmptyDerived..ctor` (a plain class over an empty base).
Expected: `ldarg.0; call MonoBehaviour::.ctor(); ret` (and `EmptyBase::.ctor()`).
Observed: `nop; ret`.

## 12. Two AssemblyRef rows per class library

Each rebuilt assembly references mscorlib twice, and System / System.Core where it uses them: one row with the original signed identity, which no TypeRef uses, and one unsigned, which every TypeRef uses.
The rebuilt class libraries themselves have `PublicKeyToken=null`.
Not a native pattern.

## 13. Floating-point negation turned into a wrong integer value, unmarked (high priority)

Negation compiles to `xorps` with a sign-mask constant, often loaded into a register outside a loop.
Rewind lifts it as an XOR on the double's high 32 bits.
When the negated value is a stack argument of a call, the call gets the int low half instead of the negated double, with no marker, in a method reported complete.
As a register argument the same lifting becomes a "bits reinterpreted as double" opaque (issue 2).

```
movsd xmm11, [<0x8000000000000000>]   ; before the loop
...
xorps xmm6, xmm11                      ; -x
movsd [rsp+0x20], xmm6                 ; fifth argument
```

Repro: `Issue13.Issue13_NegatedStackArgument` (silent), `Issue13_NegatedRegisterArgument`, `Issue13_NegatedFieldArgument` (opaque).
Expected: `double vy = Mode == 8 ? 0.0 : -(Rng.NextDouble() * 6.0 + 2.0); Spawned[i & 7] = new Particle(57, 0, true, vx, vy, 0.0, i);`.
Observed: `num3 = (int)BitConverter.DoubleToInt64Bits(value);`, then `new Particle(57, 0, animated: true, vx, num3, 0.0, num)` with "Expected F8, but got I4", no note and no row in the recovery report.
To find more in a real game: `Expected F8, but got I4` in the C#, and `DoubleToInt64Bits` outside a gap.

## 14. The value argument of a non-inlined `double[]` element store is dropped

A bounds-checked store into a `double[]` that isn't inlined (the array class's `SetAt`, value in XMM2) was unidentified with a library for another 6000.0 version, and its `Effect` dropped the XMM argument: `__native_0x…(t1, 0L)`.
A library built for the exact version identifies it as `ArraySetAt`.
No repro in Repros.cs: the pattern needs methods large enough that the store isn't inlined; `repros/sigtest/gen_tables.py` makes such methods for the library.

## 15. Direct calls to `Array::NewSpecific` stay unidentified while its thunk is named

Detail of issue 1, shown by the same repro: `rewind-lab sig-apply` identifies the thunk `SZArrayNew` (`mov edx, edx; jmp <NewSpecific>`), but not the function it jumps to, which the repro calls directly.
A thunk's target could inherit the thunk's identification.

## 16. A 2- or 4-byte store that spans inherited bool fields isn't split

MSVC merges stores to adjacent bool fields into one wider store (`mov word [rcx+0x16], 0x01`, or `mov dword [rcx+0x14], 0x10100` for four).
Rewind splits it when the fields are declared in the method's own class, not when they are inherited: "store: access of 2 bytes spans fields of <class>", and `__store2`.

Repro: `FlagsDerived.Issue16_SetInheritedBools`, `Issue16_ClearInheritedBools` (2 bytes), `Issue16_SetFourInheritedBools` (4 bytes); control `Flags16.Issue16_SetTwoBools`.
Expected: `Kind = kind; Visible = true; Solid = false;`.
Observed: `__Rewind.Effect("__store2(&this.Visible, 1)")`, `__store2(&this.Solid, 0)`, `__store4(&this.Pinned, 65792)`.

## 17. A virtual call isn't recognized after tail-merging

When two paths end in the same virtual call with different arguments, MSVC keeps one call site and jumps to it from both; the receiver's class pointer and the differing argument reach it merged.
Rewind doesn't follow the class pointer through the merge: `__call_indirect(__load8(klass + 408L), receiver, arg, 180L, __load8(klass + 416L))`, with an `__objklass()` opaque on each path.

```
; each path: rcx = receiver, rax = [rcx], edx = 0x3C or 0x78
mov  r9, [rax+0x1A0]
mov  r8d, 0xB4
call [rax+0x198]
```

Repro: `Issue17b.Issue17_TailMergedNoCctor` (`Random.Next` on a static field's object, from two paths); controls `Issue17b.Issue17_TailMergedFieldArgs`, `Walker.Issue17_*`.
Expected: `t = mode != 8 ? RandomHolder.Rng.Next(60, 180) : 120;` (and the other path).
Observed: `Random rng = RandomHolder.Rng; long num = __Rewind.Opaque<long>("__objklass()"); …` and `__Rewind.Opaque<long>("__call_indirect(__load8((m0 + 408L)), m1, conv.u8(m2), 180L, __load8((m0 + 416L)))")`.
The same happens for calls on `this` through a merged vtable-entry address or a merge of merges (seen on the game, not reproduced).

## 18. A misleading marker for an invoker specialized for one vtable slot

In a large method MSVC stops inlining IL2CPP's invoker templates, so `VirtualActionInvokerN<…>::Invoke(slot, obj, args…)` stays a call.
When every remaining call passes the same slot, LTCG specializes the invoker: the slot argument (RCX) goes dead and the invoker calls through `[klass+slot]`.
Invokers are generated per signature, so no library can name them.
Rewind's `Effect` prints the dead RCX as an argument and the receiver as the next one, and drops the floating-point and stack arguments.

Repro: `Brawler.Issue18_SpecializedInvoker` (a 13-argument virtual method called from a large `switch`).
Expected: `Arm(X, Y, 48, 48, Knock, Damage * 3, Facing, Facing * 6.0, -6.0, Kinds, Tags, true, true);` (one of the cases).
Observed: `__Rewind.Effect("__native_0x…(conv.u8(t39), this)")`, where the callee is `VirtualActionInvoker13<…>::Invoke` and calls `[r8+0x178]` without reading RCX.

## 19. 8-byte struct returns in RAX aren't rebuilt as structs

A `Vector2` return is packed into RAX from two floats; Rewind returns the packed integer cast to the struct, which doesn't compile.

Repro: `Issue19.Issue19_SnapVector2`; control `Issue19.Issue19_OrderedPair`.
Expected: `return new Vector2(Math.Sign(x), Math.Sign(y));` (and `(0, sign y)`, `(sign x, 0)`).
Observed: `return (Vector2)((uint)BitConverter.SingleToInt32Bits(num4) | ((ulong)(uint)BitConverter.SingleToInt32Bits(Math.Sign(y)) << 32));`, in a method with no note.

## 20. Smaller coverage gaps

- Inlined constructors that call virtual methods aren't folded back: `new VirtualTint(1, 1, 1, 0)` comes out as `FormatterServices.GetUninitializedObject(typeof(VirtualTint))`, the field stores and the virtual calls. Repro: `InlinedCtor.InlinedCtor_NewVirtualTint`, `InlinedCtor_NewVirtualTintLocal` (the object kept in a local); control `InlinedCtor_NewTint` (sealed class, non-virtual calls).
- An interface invoker with a double return is typed `Opaque<long>`, so the method returns a long where a double is declared.
- The covariance check isn't folded back into a plain array store.
- Unboxing a struct in an `is` pattern: `obj is ULongId other && other.Value == Value` reads the boxed value as `__load8((obj + 16L))` (marked). Seen in `ULongId.Equals`; no check.

## 21. Stack arguments of a call with many arguments are not captured

A virtual call with 13 arguments, inlined into a small method, loses its last six: `__Rewind.Opaque<double>("__missing_argument()")` ("call argument was not captured").
The native code stores the stack arguments out of order, interleaved with the register setup, and calls `[r10+0x178]`.

Repro: `Shooter.Issue18_InvokerCallA` (also `B`, `C`).
Expected: `Configure(X + 4.0, Y, 32, 32, Strong, damage, Facing, Facing * 2.0, Vy, Kinds, Tags, true, Strong);`.
Observed: `Configure(x, y, 32, 32, strong, damage2, Facing, __Rewind.Opaque<double>("__missing_argument()"), …)` with six such arguments.

## 22. Card markings left in where the address is in a local, an element or a static

Issue 3 and the instance-field pass remove the card marking when it has their shape. Three more shapes:

- the card table indexed from the image base (`[__ImageBase + index*8 + <offset>]`), where neither constant alone is in the image's data;
- a marking after the first in a run of stores: the GC flag is read again after each marking, and the next test takes it merged from both ways;
- the last marking of a path that ends in a copy of the method's epilogue, which returns by itself instead of rejoining.

A card table address left in a register after a loop (handed on as an unused argument of the next call) also kept a marking.
The output then has `address >> 12 & 0x1FFFFF` on a field's address.
No repro yet.

## 23. An object handed on from a long stack slot

An outgoing stack-argument slot holds the bools of one call (merged in as bytes: `slot & -256`) and then the object argument of the next.
Stack splitting only splits slots it finds contradictory, and an untyped slot is taken to be a long, so the object reaches the call as an `int64`.
Not covered: a slot whose address is also kept in a value, and a long that is an inlined box (`new object[] { 0 }`).
No repro yet.

## 24. A class check pasted in, the object stored uncast

An inlined `castclass` (the hierarchy compare and the throw) is taken out as a check, and Rewind casts the checked object where it is a call's argument or receiver.
Stored into a field it goes in uncast, so an object of the base type is stored into a field of the derived type, in a method with no gap.
No repro yet.

## 25. A struct slot reused for another struct, handed by reference

The compiler builds a `Color` and later a `Vector3` in the same stack memory, each handed to a call by reference.
The check for a struct handed where another is taken read the type of the address it makes, which is already the parameter's, so the slot stays one `Color` local passed as a `Vector3`.
No repro yet.

## 26. A class's statics pointer merged from several paths

When several paths each read a class's static data pointer (`[klass + 0xB8]`) and the compiler merges them, the field reads after the merge go through a variable marked `__statics()`.
The main remainder of issue 3. No repro yet.

## 27. An inlined compare-exchange on a reference field is left opaque

A field-like event's `add` and `remove` loop over `Delegate.Combine` (or `Remove`) and `Interlocked.CompareExchange` on the field.
Pasted in, the exchange is a `lock cmpxchg`, kept as `__atomic_compare_exchange(&field, value, comparand)` typed long, and the delegate compared with its result becomes a number.
Rewind already turns the runtime's compare-exchange helper into `Interlocked.CompareExchange<T>`; the intrinsic on a reference field can be treated the same, and the delegate folding then gives back `add_`/`remove_`.
No repro yet.

## 28. Smaller items found by running the output

Running the recovered C# as a player found, besides 25 and 27:

- internal calls through a cached function pointer: Unity 6 caches the resolved internal call in a static, `__load8(<address>)`, resolves and stores it when null (`__nativecode()`), then `__call_indirect`; when that lookup is merged from several paths (a tail-merged inlined internal call) it isn't recognized;
- an unboxing read as `__load4(obj + 16)` behind a type test that proved the object is a boxed value.

No repro yet.

## 29. A switch through a byte-indexed jump table loses its case bodies

MSVC compiles a sparse `switch` (many cases sharing few bodies) as two tables: a byte per case value giving a body's index, then 32-bit offsets from the image base:

```
movzx eax, byte ptr [rdx + rax + <index table>]
mov   ecx, dword ptr [rdx + rax*4 + <offset table>]
add   rcx, rdx          ; rdx = image base
jmp   rcx
```

`X64Cfg.TryReadJumpTable` takes the `cmp` bound (the number of case values) as the length of the table of targets, reads past it, finds the count wrong and gives up; the jump becomes an indirect tail call and the bodies reached only through the table are missing: the method ends at the marker.
A one-level table is recovered as a `switch`.

Repro: `Issue29.Issue29_ByteTable`, `Issue29_ByteTableFrom400`.
Observed: `__Rewind.Opaque<int>("__load4(((conv.u8(__load1((t + <index>))) * 4L) + <offsets>))")` and `__call_indirect(t, t, __klass(), 6442450944L, ...)`, then nothing.

## 30. Every call is taken to clobber every volatile register

With LTCG, MSVC knows which registers a function of the same image leaves alone, and keeps values in them across the call, for example r9 or xmm1 across the write-barrier helper:

```
xor   r9d, r9d
...
call  <write barrier>       ; doesn't write r9
mov   dword ptr [rbx + 0x..], r9d
```

Rewind treats every call as clobbering rax, rcx, rdx, r8 to r11 and the volatile xmm registers, so the store reads an undefined value: `obj.field = __undefined();`.
The registers a direct callee writes are known from its code.

Repro: `Issue30.Issue30_DoubleInLoop`, `Issue30_ReferenceInLoop`; controls `Issue30_ZeroAfterStores`, `Issue30_ZeroInLoop`, `Issue30_DoubleAfterStores` (where the barrier is inlined).

## 31. An instruction MSVC duplicated into a block that falls into a join is lost there

MSVC sinks a loop's `j++` into both paths of an `if` in the loop body: the taken path increments before its call, and the other path is one instruction that falls into the loop test.

```
  comisd xmm6, xmm8
  jae    skipped           ; several tests branch here
  ...
  inc    ebx               ; j + 1 on the drawing path
  ...
  call   <draw>
  jmp    test
skipped:
  inc    ebx               ; j + 1 on the other path
test:
  cmp    ebx, 4
  jl     loop
```

Rewind gives the first `inc ebx` its own local (`V10 = V3 + 1`) and tests that local at `test:`, but leaves the `skipped` block empty, so on that path the test reads the previous iteration's value (or its initial 0) and the loop never ends.
The value at the join should be a phi of both paths' definitions of ebx.
Not every block of this shape goes wrong; this one is the loop's induction variable, tested at the join and carried round the back edge.
No repro yet.
