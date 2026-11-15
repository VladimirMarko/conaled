# Exact Lean 4.35.0 launcher and path investigation

Read-only investigation on 2026-11-03, assigned to
`/root/lean_native_path_options`. Governing clarification:
`requirements/REQUEST-direct-toolchain-041.md`. Nix is optional, while the
exact compiler/dependency pins and stock formal verification gates remain.

## Result

No supported environment variable, CLI option or alternate bundled launcher
was found in the inspected exact-release sources that lets the ordinary Lean
source compiler avoid its native application-path discovery. This is a
specific Linux-runtime requirement, not a requirement to use Nix.

The parent has already downloaded and checksum-verified the official release.
With the bundled library directories supplied through `LD_LIBRARY_PATH`, its
actual Lake version probe succeeds as `Lake version 5.0.0-src+eb6cafb (Lean
version 4.35.0)`. Actual Lean `--version` and `--print-prefix` probes still
exit 1 with `error: failed to locate application`, despite `LEAN_SYSROOT`.
Those observations are preserved in
`environment/direct-toolchain-smoke-041-r2.json`; this investigation did not
rerun any compiler or binary.

## Why the usual path variables do not fix this call

The packaged `Lean/Util/Path.lean` distinguishes two functions:

- `getBuildDir` obtains `IO.appDir` and takes its parent. It has no environment
  override. The exported `lean_init_search_path` calls
  `initSearchPath (← getBuildDir)` unconditionally.
- `findSysroot` first checks `LEAN_SYSROOT`, then otherwise invokes
  `lean --print-prefix`. Its documentation calls this the external-user route
  and directs Lean-internal callers to `getBuildDir`.

`LEAN_PATH` is added only while constructing the search path after the system
root has already been obtained. An explicit `LEAN_PATH` therefore cannot skip
the failing application-path call.

The coordinating investigation independently inspected the exact native
runtime and shell providers. It reports that Linux `IO.appPath` obtains its
path by reading `/proc/<pid>/exe`, and native shell startup initializes the
search path before processing CLI options. Its complete evidence belongs in
`environment/direct-toolchain-validation-plan.md`; no independent native
runtime modification or probe was made here.

## Inspected official alternatives

| Entry point | Actual role and relevant behavior | Consequence |
| --- | --- | --- |
| `lean` CLI options in `Lean/Shell.lean` | `--root` sets the package root used to derive a module name. There is no system-root override in `ShellOptions`. `--print-prefix` directly calls `getBuildDir`. | Neither option supplies the missing native executable location. |
| `lake env lean ...` | `Lake.Cli.env` prepares environment variables and spawns the requested command. | It runs the same external Lean binary; Lake's successful version probe does not establish that Lean will start. |
| `lake lean File.lean` | `Workspace.evalLeanFile` prepares the command through `prepareLeanCommand`, then spawns it. The prepared command is `(← getLean).toString`. | It is not an in-process replacement compiler and inherits the native Lean startup dependency. |
| `leanir` | Its main procedure performs code generation from an existing module/setup/IR state and calls `initSearchPathInternal`. | It is not a source elaborator and retains the same internal application-path dependency. |
| `leanchecker` | Uses `findSysroot` and can replay declarations from existing `.olean` data, or check an already produced export stream. | It may have a different startup route, but it cannot produce the missing compiled project modules or replace the required source build/audit. No execution was attempted here. |
| `leanexport` | Uses `findSysroot`, imports compiled modules, and emits an export representation. | It consumes existing compiled modules; it is not a replacement source compiler. No execution was attempted here. |

The exact `lake lean` subprocess evidence is in `Lake/CLI/Main.lean` around
1285–1292, `Lake/CLI/Actions.lean` around108–117, and
`Lake/Build/Module.lean` around1539–1572. This rules out treating Lake's working
version-only path as an alternate elaboration path.

No fake version output, custom compiler launcher, binary patch, interposition,
mount change, permission workaround, gate weakening or substitute checker was
implemented or recommended. The stock release needs the normal native
application-path facility, or a separately established supported environment
that supplies it. This investigation does not prove that every conceivable
custom embedding is impossible; it establishes no such embedding as an
accepted replacement for this project's pinned stock checks.

## Exact provider identities

The inspected bytes came from the parent's verified official
`lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
The local source root is `toolchains/lean-4.35.0-linux/src/lean/`.
Each source has a matching official v4.35.0 URL below. Hashes were computed
directly from those packaged source bytes; no Git branch-tip source was used.

| Source | SHA256 |
| --- | --- |
| [Lean/Util/Path.lean](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/Lean/Util/Path.lean) | `52cf9aa41a82db18d0d3c93bf6257d064f773af9e62b8b43be89ce1b0e00055f` |
| [Lean/Shell.lean](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/Lean/Shell.lean) | `bbfcf01a93bcb9ca3f4d1264d3ad9890f3a6384dbbc949f5bf3cc286c0ec2225` |
| [LeanIR.lean](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/LeanIR.lean) | `cb0e362fc299ab84ead24874efacc462e25c8c43aaa9d24276518a9ef538dee2` |
| [LeanChecker.lean](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/LeanChecker.lean) | `4a406b8ed95da0377206600b7b00a03bedc05102c0fadad641ffe0bfdb95122f` |
| [LeanExport.lean](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/LeanExport.lean) | `ec95c53d108c5b014e7a53d6b88a4dbe41dc75c2e55102b2f8211268fcb94cf5` |
| [Lake/CLI/Main.lean](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/lake/Lake/CLI/Main.lean) | `330d8ebde227bee7234892dabe2191fcd387c8d582559537baca1e207f9196d3` |
| [Lake/CLI/Actions.lean](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/lake/Lake/CLI/Actions.lean) | `6bf40d09e59f84f1a213065e8e65794ed4735001e2d07d1656e8096914b2269b` |
| [Lake/Build/Module.lean](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/lake/Lake/Build/Module.lean) | `c67fff2c7bd95671b49ea64482c4f843f55fefdc4c038858f22a269f0b070b69` |

No source, dependency, toolchain, project configuration, tracker or existing
evidence file was changed. Only this report was written. It is not a compiler
success, full validation, proof-audit or acceptance record.
