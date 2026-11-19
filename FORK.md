# About this fork

This is a fork of [Rewind](https://github.com/ratman-bit/Rewind-IL2CPP-Decompiler) with fixes for issues found while decompiling a commercial Unity 6000.0.60f1 game (Windows x64, IL2CPP Master, metadata v31.1), for a port of that game to another platform.
It is upstream's commit `ea8e305` plus 33 small commits, one change each, and a folder of game-free repros.
Upstream is welcome to take any part of it, as is or reworked; nothing here needs to be taken whole.

- Base: [`ea8e305`](https://github.com/ratman-bit/Rewind-IL2CPP-Decompiler/commit/ea8e305) (upstream `main` as of 2026-11-19).
- The issues, each with the native pattern, the expected and observed output and its repro: [docs/fork-issues](docs/fork-issues/README.md).
- The repros and how to build and check them: [repros](repros/README.md).
- Most changes have a `REWIND_NO_*` environment variable that turns them off, named in the commit message, so the fork's output can be compared with upstream's change by change (commits 2, 3, 17 and 23 have none).

## The issues

"Repro" is the repro method in [repros/Repros.cs](repros/Repros.cs); 5 and 12 are not about native code, and those marked "none yet" were found on the game and have no repro.
Status is the result of the issue's checks in `repros/check_repros.py` where there is a repro, otherwise what was seen on the game.
"Partly" means the value is now right and nothing is left unmarked, but the output isn't yet the expected form, or some variants are still open.
With a 6000.0.60f1 library, 14 of the 46 checks pass on upstream (the controls and issue 1) and 36 in the fork (checked 2026-11-20).

| # | Issue | Short description | Repro | Upstream | Fork | Fork commits |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `Array::NewSpecific` called directly is not identified | `new T[n]` calls the allocator behind the `SZArrayNew` thunk; it stays an unidentified native call | `Issue1_NewIntArray`, `Issue1_NewStringArray` | open (fixed with a 6000.0.60f1 library that names it, which needs the fork's helper rules) | fixed | 58ca489, 3d9de09 |
| 2 | "bits reinterpreted as double" when `Int64BitsToDouble` was stripped | a double merged from two paths is split into halves and rebuilt with a stripped method, left opaque | `Issue2_ClampedAlpha`, `Issue2_MergedArgument` | open | partly: no gap, right value, still built from halves | 9dda983 |
| 3 | Write barrier after a static field store left in | the card marking stays, and a statics pointer reused across it is read as `__statics()` | `Issue3_GetInstance` | open | fixed | ef29ed8, c1e35ae |
| 4 | Signed modulo by a power of two not folded back | correct but unreadable bit arithmetic for `x % 4` | `Issue4_Mod4` | open | open | |
| 5 | `recovery-report.tsv` can't be joined to assemblies or overloads | rows are keyed `Type::Method` only | (not native) | open | open | |
| 6 | A gap noted but not marked: `typeof(T)` as invalid IL | an inlined `GetTypeFromHandle` gives invalid IL with no marker | `Issue6_TypeofSizeOf` | open | partly: marked; `typeof(T)` not folded back | dc75ede |
| 7 | Address of an offset-0 field replaced by the struct's address | `Value.ToString()` on a field at offset 0 is called on the whole struct | `ULongId.ToString`, `Issue7_ParameterFieldToString` | open | fixed | 6074b65 |
| 8 | No truncation after an inlined `UInt64.GetHashCode` | an int-returning method returns int64 | `ULongId.GetHashCode`, `KeyChord.GetHashCode` | open | fixed | cca495b |
| 9 | Inlined object hash done as arithmetic on a reference | `RuntimeHelpers.GetHashCode` becomes shift and multiply on the reference, unmarked | `Issue9_IdentityHash`, `Hashed.GetHashCode` | open | fixed | 5234976 |
| 10 | Small structs handled as integers without a marker | a 4-byte struct in a register is used as an int | `set_Issue10_Code`, `Issue10_IntAsStruct` | open | partly: rebuilt or marked; the return is correct in another form than the check wants | 1d3a02a |
| 11 | Constructors with no base `.ctor` call | `nop; ret` constructors, invalid per ECMA-335 | `EmptyBehaviour..ctor`, `EmptyDerived..ctor` | open | fixed | c8be167 |
| 12 | Two AssemblyRef rows per class library | a signed and an unsigned reference to each class library | (not native) | open | fixed | a49cf9b |
| 13 | Floating-point negation turned into a wrong integer value, unmarked | `xorps` with a sign mask passes the int low half instead of `-x`, silently | `Issue13_Negated*` | open | partly: right value and no gap; a merged negated double is still built from halves | 822587e, 9dda983 |
| 14 | Value argument of a non-inlined `double[]` store dropped | the XMM value argument of an unidentified `SetAt` is lost | (signature test project) | fixed with a library for the exact version | fixed, also without one | 0450f11, c464a1c |
| 15 | Thunk named, its target not | a library names `SZArrayNew` but not the function it jumps to | as 1 | open | fixed | 3d9de09 |
| 16 | A 2- or 4-byte store over inherited bool fields isn't split | `__store2` / `__store4` over fields of a base class | `Issue16_*InheritedBools` | open | fixed | 2d1694e |
| 17 | Virtual call not recognized after tail-merging | a call site shared by two paths gets the class pointer merged and becomes `__call_indirect` | `Issue17_TailMergedNoCctor` | open | fixed (also the `this` form, seen on the game) | 0132d4d, 2bf0398 |
| 18 | Misleading marker for an invoker specialized for one slot | the dead slot register is shown as an argument, real arguments dropped | `Issue18_SpecializedInvoker` | open | fixed | 6839059, 25b3afa |
| 19 | 8-byte struct returns in RAX not rebuilt | a `Vector2` return is a packed integer cast to the struct | `Issue19_SnapVector2` | open | partly: rebuilt; one path still fills a field from reinterpreted bits | f569de2 |
| 20 | Smaller coverage gaps | inlined constructors with virtual calls; double-returning interface invoker; covariance check; `is` unboxing | `InlinedCtor_NewVirtualTint`, `InlinedCtor_NewVirtualTintLocal` | open | partly: constructors folded back (not when kept in a local), unboxing reads fixed; the rest open | 8064f4c, f448411 |
| 21 | Stack arguments of a call with many arguments not captured | the last six of 13 arguments are `__missing_argument()` | `Issue18_InvokerCallA` | open | fixed | 25b3afa |
| 22 | Card markings left in where the address is in a local, an element or a static | three more shapes of the write barrier | none yet | open | fixed (a few markings inside larger regions left) | c69836a |
| 23 | An object handed on from a long stack slot | a slot that held bools and then an object passes the object as int64 | none yet | open | partly | f0d5e82 |
| 24 | A class check pasted in, the object stored uncast | an object checked by an inlined `castclass` is stored uncast | none yet | open | fixed | b4451fb |
| 25 | A struct slot reused for another struct, handed by reference | a `Color` slot passed where a `Vector3` is taken | none yet | open | fixed | b4451fb |
| 26 | A class's statics pointer merged from several paths | field reads through a merged statics pointer stay `__statics()` | none yet | open | fixed | c1e35ae |
| 27 | An inlined compare-exchange on a reference field left opaque | event `add`/`remove` loops keep `__atomic_compare_exchange` | none yet | open | fixed | 64a804b |
| 28 | Smaller items found by running the output | merged lookups of cached internal-call pointers; unboxing reads behind a type test | none yet | open | fixed | 6a5e893, f448411 |
| 29 | A switch through a byte-indexed jump table loses its case bodies | the two-level table is misread and the bodies disappear | `Issue29_ByteTable`, `Issue29_ByteTableFrom400` | open | fixed | a00faad |
| 30 | Every call taken to clobber every volatile register | a value kept in r9 or xmm1 across the write-barrier helper becomes `__undefined()` | `Issue30_DoubleInLoop`, `Issue30_ReferenceInLoop` | open | fixed | 08bf547 |
| 31 | An instruction duplicated into a block that falls into a join is lost | a loop counter incremented on both paths is lost on one, and the loop never ends | none yet | open | open | |

## The changes

One commit per change, on `ea8e305`, in this order; each applies and builds on the ones before it.
Commit 22 adds a line to each changed or added source file saying it was changed (Apache-2.0 §4(b)), and the later commits keep those lines up to date, so 22 is the only one that touches files for that alone.

| # | Commit | Change |
| --- | --- | --- |
| 1 | 3d9de09 | Support functions reached through a wrapper that only widens its arguments are identified. |
| 2 | 58ca489 | Signature libraries can name `Array::NewSpecific`, `Object::New` and `Object::NewAllocSpecific`. |
| 3 | ef29ed8 | The write barrier inlined after a store to a static field is removed. |
| 4 | ef89044 | The metadata initializer is found by how it is called when no library names it. |
| 5 | 0450f11 | Floating-point arguments of unidentified native calls are kept. |
| 6 | c464a1c | Array element accessors are identified by their code. |
| 7 | 2d1694e | A wide store over inherited fields is split into those fields. |
| 8 | 0132d4d | A virtual call through a class pointer merged from several paths is recognized. |
| 9 | 6839059 | Invokers specialized for one vtable slot are recognized. |
| 10 | 6074b65 | The address of a struct's first field is kept where the field is meant. |
| 11 | 11ea549 | A string's characters read by index become the indexer. |
| 12 | dc75ede | Every unrecovered part is marked; a note goes with its markers. |
| 13 | c8be167 | Base constructor calls are put back. |
| 14 | 8064f4c | Inlined constructors are folded back; calls IL does not accept get a note. |
| 15 | 5234976 | The runtime's inlined object hash becomes a call; arithmetic on a reference is marked. |
| 16 | 1d3a02a | Small structs computed with as numbers are rebuilt or marked. |
| 17 | a49cf9b | One assembly reference per assembly. |
| 18 | 822587e | Floating-point negation through a sign mask is folded. |
| 19 | 9dda983 | Bits read as a float or double are reinterpreted without BitConverter. |
| 20 | f569de2 | 8-byte structs returned in a register and merged are rebuilt from their bits. |
| 21 | cca495b | A 32-bit read of a 64-bit field is narrowed. |
| 22 | 8f16fd9 | Each changed or added source file carries a line saying so (Apache-2.0 §4(b)). |
| 23 | c69836a | The write barrier's card marking is removed in more shapes: a card table indexed from the image base, a flag read again after each marking, a marking that ends in a copy of the method's ending. |
| 24 | f0d5e82 | A long stack slot that held a reference and a number is split into two variables. |
| 25 | b4451fb | An object checked as a class is stored cast; a struct's address handed to a call is typed as its target. |
| 26 | c1e35ae | A class's static data pointer merged from several paths is that class's statics. |
| 27 | 64a804b | An inlined compare-exchange on a reference field becomes `Interlocked.CompareExchange<T>`. |
| 28 | 25b3afa | A call whose target isn't known yet takes as many stack arguments as the run of outgoing slots written before it. |
| 29 | 6a5e893 | An engine-method lookup merged from several paths (a tail-merged inlined internal call) collapses into the internal-call method. |
| 30 | f448411 | A read past the header of an object a type test proved to be a boxed value is the unboxed value, or a field of it. |
| 31 | 2bf0398 | Virtual calls on `this` merged from several paths, through a merged vtable-entry address or a merge of merges, are recovered. |
| 32 | a00faad | A switch through a byte table of case indexes and a table of targets is recovered; the register a jump table jumps through is dead after the jump. |
| 33 | 08bf547 | A direct call changes only the volatile registers the callee's code writes. |

After them: the repros (`repros/`) and these docs.

## Building

As upstream, with the .NET 10 SDK:

    dotnet build -c Release src/Rewind.Cli      # rewind.exe in src/Rewind.Cli/bin/Release/net10.0
    dotnet build -c Release src/Rewind.Lab      # rewind-lab.exe, for signature libraries

The repros need Unity 6000.0.60f1's files, MSVC 14.50 and a 6000.0.60f1 signature library; [repros/README.md](repros/README.md) shows how to build the library from a game-free test project (`repros/sigtest`, with `repros/pdbsyms.py` for the `symbols.tsv` step upstream's README mentions).

## License

Rewind is Copyright 2026 ratman-bit and licensed under the Apache License 2.0; so is this fork.
Upstream's [LICENSE](LICENSE) and [NOTICE](NOTICE) are unchanged.
Every source file the fork changes or adds carries a line saying so (`// Modified by xob0t (2026): … See FORK.md.` or `// Added by …`), as Apache-2.0 §4(b) asks.
The fork holds no code or data from the game the issues were found on.
