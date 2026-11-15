# Native validation performance follow-up

## Disposition

Keep the accepted native route and the active fresh4 run unchanged. Static
inspection found no demonstrated drop-in option that would substantially
accelerate the complete current validation while preserving its exact
execution/evidence model. There are plausible import-loading costs, but no
current per-process measurement separates import work, proof work, and storage
waiting in the two slow AD modules. No further experiment is proposed now.

The active formal candidate is
`c988f183887896c00b09aaff9077a6ea7fb8d68f`; the inspected compiler is official
Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Operational
#1033 acceptance and the completed #1034 foundation correction are not reopened
by this assessment.

## Observed evidence

The fresh4 [child log](../1002-candidate-c988f18-native-fresh4/child.log), read
while the run remained active, recorded:

| Module | Completed wall time |
| --- | ---: |
| `Squares` | 5.33 s |
| `Applications.AD.Core` | 430.83 s |
| `Applications.AD.Modes` | 832.33 s |
| `FirstOrder` | 35.53 s |

The earlier [native Squares resource sample](native-squares-resource-sample.json)
recorded 136.8226 s wall time, 2.9872 s user CPU, 35.0429 s system CPU,
844,264 KiB maximum RSS, 144,730 major faults, and an input-block counter of
71,899,496. That supports substantial disk-backed page-in/I/O activity in
that earlier process. It does not identify the active AD process's resource
use or establish the cause of all waiting. The input-block counter is retained
as recorded; this assessment does not convert it into a measured byte count.

The [Init-only Squares experiment](import-footprint-experiment.json) completed
in 4.7896 s with 2,944 major faults. Together with current Squares at 5.33 s,
this supports the already-adopted foundation import correction. It does not
justify applying its speed ratio to Mathlib-heavy modules.

The existing [aggregate memory observation](host-memory-observation.json)
reported 10,451,427,328 bytes total RAM, 954,830,848 free RAM, and no swap at
that earlier instant. It is neither current task headroom nor a process/cgroup
limit. CPU affinity alone therefore provides no evidence that two concurrent
heavy import processes will fit or run faster.

## What the sources explain

The [fresh scheduler](../../../vfa-native-validation/scripts/check.py),
`compile_modules` at lines 70–109, starts a separate Lean process for each
module. Its dependency traversal at lines 259–273 sorts local imports, putting
AD.Core and AD.Modes early in the serial run. Merely rearranging imports in
`SquareApplications.lean` cannot change that order. The early slow modules are
not representative timings for all 953 compilation tasks; the run has already
moved beyond them. The scheduler's bookkeeping is not an evidenced explanation
for hundreds of seconds inside a completed Lean subprocess.

`Applications.AD.Core` directly imports four FDeriv modules and uses actual
Fréchet derivative rules. In particular its multiplication proof calls
`HasFDerivAt.mul`; the pinned Mathlib
`Mathlib/Analysis/Calculus/FDeriv/Mul.lean` defines that theorem and publicly
imports `FDeriv.Analytic`. This is a genuine mathematical dependency, unlike
the removed foundation `import Lean`. The complete transitive external module
closure was not counted here. The 9,031 previously downloaded cache objects
are the project cache retrieval total, not an AD.Core import count.

That external closure and the *parts loaded per member* are distinct costs.
The pinned local [import elaborator](../../../toolchains/lean-4.35.0-linux/src/lean/Lean/Elab/Import.lean),
`processHeaderCore` at lines 141–160, selects `.private` import level for legacy
files. The pinned [environment loader](../../../toolchains/lean-4.35.0-linux/src/lean/Lean/Environment.lean)
states at lines 2121–2123 that this mode follows all transitive imports and
ignores module-system annotations. Its `go` function at lines 2178–2227 sets
`importAll` and requests IR; its fallback file loader at lines 2079–2106 reads
the available `.olean`, `.olean.server`, `.olean.private`, `.ir.sig`, and `.ir`
parts. `finalizeImport`, starting at line 2308, then assembles constant maps and
extension state. Thus an ordinary small source file can require substantial
dependency metadata before elaborating its own declarations.

The local [CompactedRegion API](../../../toolchains/lean-4.35.0-linux/src/lean/Lean/CompactedRegion.lean)
documents file-backed mappings. Read-only inspection of the matching upstream
[`src/library/module.cpp`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/library/module.cpp)
found the mmap path and malloc/read fallback controlled by compiled platform
support and mapping success, not a runtime environment toggle. Its inspected
SHA256 was `9b85a9a7610e73f240282fe288ad81c8b160fc975caa80bd5b13ddacdd6012a8`.
The source was read in memory; no installed binary or source was patched.

## Options and limits

**Supported worker count:** A later invocation may use `--fresh --jobs 2`
without changing the formal source candidate: this is already supported by
`check.py` lines 208–218 and the README. It preserves per-module commands,
dependency ordering constraints, fresh private outputs, and the final audit.
It needs its own complete result; the existing launch record binds worker
count because the checker success JSON does not store it. There is currently
no positive memory evidence that makes two simultaneous heavy imports a
recommended change. More workers can overlap I/O, but can also increase
resident/private state and paging. Keep current one-worker/one-thread settings.

**Module mode:** It is not a visibility-neutral compiler optimization.
[DeclModifiers.lean](../../../toolchains/lean-4.35.0-linux/src/lean/Lean/Elab/DeclModifiers.lean)
line 85 makes ordinary declarations private in a `module` outside a public
section; `Elab/Import.lean` lines 29–39 change ordinary imports' re-export
behavior. `Environment.lean` lines 2116–2120 also reject a module-mode root
importing a legacy dependency. AD.Core still imports legacy Squares. A source
header or setup override cannot silently preserve these interfaces: a real
module/public-export migration is a broader source/API change and is outside
this task.

**Experimental header snapshots:** The pinned
[Shell.lean](../../../toolchains/lean-4.35.0-linux/src/lean/Lean/Shell.lean)
lines 181–184 exposes `--incr-header-save` and `--incr-load`.
[Frontend.lean](../../../toolchains/lean-4.35.0-linux/src/lean/Lean/Elab/Frontend.lean)
lines 314–333 explicitly describe an initializer-replay caveat; lines 374–376
save only a truncated header. The local
[language processor](../../../toolchains/lean-4.35.0-linux/src/lean/Lean/Language/Lean.lean)
lines 462–474 reuse it only for matching header syntax; lines 815 onward
discard command bodies for a header snapshot. A static grouping by import
lists found 893 distinct nonempty headers, with only 58 possible repeated
assemblies among 42 groups; exact syntax matching can reduce reuse further.
Differing headers do not gain a common-prefix import cache from this feature.
Snapshot creation also has a cost and references exact dependency artifacts.
Full-command snapshots would reuse completed source elaboration, which is not
the current fresh gate. Header-only snapshots would still change the checker
execution/input model. Neither is a drop-in optimization for this run.

`LEAN_IMPORT_WORKERS` is read only in the snapshot loader in
`Frontend.lean` lines 196–229, not the ordinary import path used here. Setting
it for the unchanged fresh command is not an evidenced acceleration. The
built-in `--profile` can distinguish import and elaboration costs if diagnosis
is later needed, but no overlapping or additional Lean invocation was run or
requested in this follow-up.

## Integrity and scope

All runtime, source, dependency, cache, and active validation inputs were left
unchanged. No Lean process, build, test, process-control action, or `/proc`
probe was performed. This report is the only written output. It neither
claims formal success nor changes any existing validation or audit gate.

Pinned local source hashes used for the central conclusions:

- `Lean/Environment.lean`: `6c90105aecc4d28efe94cc9aef1704c284e7a748b28270b5f8513d2562331e43`
- `Lean/Elab/Import.lean`: `5d46fc36944ed3cbb9b862cb954fdd8ea2d2036f135e4b48adc368b69dc8b8fc`
- `Lean/Elab/DeclModifiers.lean`: `9665a12a50dfb92b42f87759941bad09e9f7357f6042cd660c3795859c804749`
- `Lean/Elab/Frontend.lean`: `423d17e49722e901e5f82bd4b86e7cf2dd80c352fc55b3d72ac1301a79ead634`
- `Lean/Language/Lean.lean`: `90abb52c6f84836fce3606d2f4e03c9f717992b842c98e0283cddeb8a1611d86`
- `scripts/check.py`: `80794fe95dd2f15ac872da3b6908921ef2898635911832ce0993176308288a29`
