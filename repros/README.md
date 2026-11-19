# Repros

Minimal, game-free reproductions of the issues in [docs/fork-issues](../docs/fork-issues/README.md).
[Repros.cs](Repros.cs) is written from scratch: each method is ordinary C# that an IL2CPP Master build (MSVC `/GL` `/LTCG`) compiles into the native pattern an issue is about.
Method names start with the issue number (`Issue13_NegatedStackArgument`).

The scripts build Repros.cs into a Windows x64 IL2CPP player without the Unity editor, decompile it with a given Rewind build and print PASS (fixed) or FAIL (still reproduces) per repro.
Checks named "control" are variants Rewind already recovers; they guard against regressions.

## What you need

- Unity 6000.0.60f1's `Editor/Data` folder with the Windows IL2CPP player module (`PlaybackEngines/windowsstandalonesupport`). Only its files are read: Roslyn, UnityLinker, il2cpp. No license or sign-in is needed, so the files can come from the editor's and the module's installers.
- An installed Visual Studio C++ toolset (il2cpp's Bee build picks it itself), and a portable MSVC 14.50 toolset: the C++ build is then replayed with 14.50 (`sigtest/replay_msvc.py`), the compiler of the build where the issues were found.
- Python 3.10+, the .NET 10 SDK (`dotnet` on PATH, or `DOTNET=<dotnet.exe>`), and rizin on PATH for the native excerpts of `--report` and for `disasm.py`.
- A Unity 6000.0.60f1 Windows x64 signature library (see below).

| Setting | Argument | Environment variable |
| --- | --- | --- |
| Unity `Editor/Data` | `--unity <dir>` | `UNITY_DATA` |
| Folder holding an MSVC 14.50 toolset (searched for `VC/Tools/MSVC/14.50.*/bin`) | `--msvc <dir>` | `MSVC_ROOT` |
| Signature library | `--sig <file>` | `REWIND_SIGNATURES` |
| Repro build folder (default `repros/work/build`) | `--work <dir>` | `REPROS_WORK` |

## Build and check

    python -I repros/build_repros.py --unity <Editor/Data> --msvc <msvc dir>
    python -I repros/check_repros.py src/Rewind.Cli/bin/Release/net10.0 --sig <unity-6000.0.60f1-windows-x64.sig> [--report results.md] [--only 13 2]

The build takes 10 to 25 minutes and is cached in `<work>/master` while Repros.cs and the scripts don't change (`--force` rebuilds).
It leaves `<work>/master/game` (a folder Rewind reads like a game), `GameAssembly.pdb`, `symbols.tsv` (the PDB's public symbols) and `cpp/` (the generated C++).
check_repros.py runs `rewind decompile <game> --signatures <sig> --assembly Repros`, reads the C# (and, for a few checks, the IL through `IlDump/`, built on first use), and exits with the number of failing checks.
`--report` writes the expected C#, Rewind's C# and IL, and a native excerpt per repro.

    python -I repros/disasm.py [--build <work>/master] <symbol part>...

disassembles any function of the build, with calls annotated from the PDB symbols.

To compare upstream and the fork, build each (`dotnet build -c Release src/Rewind.Cli`) in its own clone and run check_repros.py on both; the output goes to `repros/work/check/<clone name>`.

## The signature library

Rewind ships no library for 6000.0.60f1, and the repros need one: with a library for another 6000.0 version, the runtime's helpers are named differently and several checks fail for that reason alone.
The library can be built from a game-free test project, [sigtest/SigTest.cs](sigtest/SigTest.cs), which makes IL2CPP generate the helper calls a game's code would:

    python -I repros/sigtest/build_sigtest.py <Editor/Data> <work dir> --msvc <…/VC/Tools/MSVC/14.50.xxxxx> master release master-size master-nogc
    dotnet build -c Release src/Rewind.Lab     # rewind-lab.exe lands in src/Rewind.Lab/bin/Release/net10.0
    rewind-lab sig-build unity-6000.0.60f1-windows-x64.sig \
      <work dir>/master/game <work dir>/master/symbols.tsv \
      <work dir>/release/game <work dir>/release/symbols.tsv \
      <work dir>/master-size/game <work dir>/master-size/symbols.tsv \
      <work dir>/master-nogc/game <work dir>/master-nogc/symbols.tsv

The compiler matters as much as the Unity version: signatures compare code bytes, so the test builds must be compiled with the same MSVC as the game (14.50 here; `--msvc` replays the build with it).
For issue 1 the library must name `Array::NewSpecific`, `Object::New` and `Object::NewAllocSpecific`, which needs the helper rules of the fork's commit "Name Array::NewSpecific and Object::New / NewAllocSpecific in signature libraries"; build rewind-lab from the fork for that.

## Issues without a repro here

5 and 12 are not about native code. 14 needs methods large enough that an array accessor isn't inlined; the signature test project covers it (`sigtest/gen_tables.py`). 15 shows in issue 1's repro.
22 to 28 and 31 were found on the game and have no repro yet; their docs describe the native pattern.
