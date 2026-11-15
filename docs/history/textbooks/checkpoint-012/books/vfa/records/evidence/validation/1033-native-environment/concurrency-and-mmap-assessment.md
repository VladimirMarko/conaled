# Lake concurrency, Lean CLI threads, and compacted-region mmap assessment

Date: 2026-11-03 UTC.

Scope: operational source analysis of the exact accepted Lean 4.35.0 / Lake
5.0.0-src+eb6cafb environment, plus the separately recorded bounded explicit
`-j1` probe described below. This is not Standards or Spec approval and does not
complete any formal candidate gate. The current formal candidate is
`c988f183887896c00b09aaff9077a6ea7fb8d68f`.

The source investigation ran no Lean/build command and changed no formal
source, compiler, launcher, dependency, cache, or active process. Its only
persisted write is this report. The root agent separately conducted the
bounded probe and supplied its record; this report reads that evidence without
repeating the experiment.

## Disposition

`LEAN_NUM_THREADS=1` in the accepted helper serializes the ordinary external
compiler jobs used by this project's pinned Lake build. It does not establish
one internal worker in each Lean CLI process. Lean's shell uses its own
hardware-concurrency default unless it receives an explicit `-j` / `--threads`
argument.

Keep fresh4 and the accepted helper/wrappers unchanged. Retain the existing
non-repairing pre-guard capture and subsequent guarded incremental/audit
workflow. No extra Lake concurrency flag is required for that incremental
command. Do not force the compacted-region mmap fallback without demonstrated
memory headroom: the fallback introduces full-file private allocations and
pointer-relocation work, and the current evidence does not establish a net
benefit.

## 1. Lake's ordinary external compiler jobs

All upstream source references in this report are pinned to Lean commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

The relevant source chain is:

| Stage | Exact source evidence |
| --- | --- |
| Compiled Lake executable startup | [`src/Lean/Compiler/LCNF/EmitC.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Compiler/LCNF/EmitC.lean), lines 1118–1133, emits a call to `lean_init_task_manager()` before running main. |
| Runtime environment setting | [`src/runtime/object.cpp`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/runtime/object.cpp), lines 1106–1121, reads `LEAN_NUM_THREADS` and passes the resulting count to `lean_init_task_manager_using`. |
| Module compilation job priority | [`src/lake/Lake/Build/Module.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/lake/Lake/Build/Module.lean), lines 1011–1024, uses `presetupJob.mapM` in `recBuildLean`. [`src/lake/Lake/Build/Job/Monad.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/lake/Lake/Build/Job/Monad.lean), lines 222–227, defaults this to normal task priority and asynchronous scheduling. |
| External compiler launch | [`src/lake/Lake/Build/Actions.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/lake/Lake/Build/Actions.lean), lines 29–65, calls `rawProc` for Lean. [`src/lake/Lake/Util/Proc.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/lake/Lake/Util/Proc.lean), lines 29–36, calls `IO.Process.output`. |
| Worker remains occupied until child completion | [`src/Init/System/IO.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Init/System/IO.lean), lines 1537–1557, uses a dedicated task only to read stdout. The calling worker reads stderr synchronously and waits for the child; `stdout.get` comes after `child.wait`. |
| Native waits are blocking IO | [`src/runtime/io.cpp`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/runtime/io.cpp), lines 594–614, uses `fread` for handle reading. [`src/runtime/process.cpp`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/runtime/process.cpp), line 358, uses blocking `waitpid`. Neither operation releases a Lake compiler slot through a task-manager wait hook. |

The runtime distinguishes normal-pool and dedicated tasks. Its ordinary queue
and worker limit are implemented in `object.cpp`, lines 788–865 and 963–965.
It may add replacement workers when a pool task waits on `Task.get`
(lines 1020–1041), preventing deadlock. This does not make the synchronous
stderr read or child-process wait available for another compiler job. Thus a
normal compiler child occupies the single normal execution slot throughout
its lifetime. The separate stdout reader is not another compiler.

This conclusion covers the standard compiler jobs in the current project. It
is not a bound on every OS thread or on arbitrary custom targets that might
explicitly launch several subprocesses.

The pinned Lake CLI/help and build configuration contain no built-in `-j`,
`--jobs`, `--threads`, `LAKE_JOBS`, or equivalent compiler-job-count setting.
`-K` supplies package configuration values; it is not a built-in scheduler
limit. Relevant primary sources are
[`CLI/Help.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/lake/Lake/CLI/Help.lean),
[`CLI/Main.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/lake/Lake/CLI/Main.lean),
and [`Build/Context.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/lake/Lake/Build/Context.lean).

The frozen project checker invokes `lake --no-cache --rehash build` for the
incremental targets. Its own `--jobs` flag is fresh-only. From the frozen
`vfa-native-validation` checkout, the intended later incremental invocation
therefore remains:

```bash
python3 -B /workspace/scratch/83865511e965/recovery/conaled-vfa-checkpoint-035-returned-archive-preservation/work-state/tooling/pinned_native_toolchain.py -- ./check.sh --candidate HEAD
```

This command is documented here, not executed by this assessment. The helper
already sets `LEAN_NUM_THREADS=1`.

## 2. Lean CLI's internal task count is separate

[`src/Lean/Shell.lean`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Shell.lean),
lines 220–224, chooses the shell default from
`Platform.Internal.getHardwareConcurrency()` when multithreading is enabled.
`ShellOptions.numThreads` uses that default at line 238. The `-j` /
`--threads` handler at lines 301–308 replaces it explicitly.

[`src/util/shell.cpp`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/util/shell.cpp),
lines 331–353, constructs/parses the shell options and starts the task manager
using their thread count. The native hardware-concurrency implementation in
[`src/runtime/thread.h`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/runtime/thread.h),
line 53, calls `std::thread::hardware_concurrency()`. There is no
`LEAN_NUM_THREADS` lookup on this shell-option path.

Consequently, prior environment records containing `LEAN_NUM_THREADS=1`
accurately capture that environment setting, but must not be interpreted as a
measured or guaranteed one-worker Lean CLI bound. A real `lean -j1 ...` or
`lean --threads=1 ...` argument is the supported selector for the internal
count. No numeric observation of the current compiler's worker count is
claimed here. The source distinction does not prove that internal parallelism
caused the slowdown.

## 3. Existing compacted-region mmap fallback

[`src/library/module.cpp`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/library/module.cpp),
lines 452–619, opens and stats the region, reads/checks its header, then
attempts a private writable file mapping at the saved base address. On Linux
the flags include `MAP_FIXED_NOREPLACE`. Failure, or a mapping at the wrong
address, selects the existing fallback: allocate the full file size with
`malloc`, seek to the start, and read all its bytes. The region reader then
processes that buffer. Its allocation remains owned by the imported
`CompactedRegion`; it is not discarded after parsing.

`LEAN_MMAP` is a compile-time conditional for this path. No runtime disable
switch was found in the loader. Read-only `readelf --dyn-syms --wide` inspection
of the official `lib/lean/libleanshared.so` found `mmap@GLIBC_2.2.5` as an
undefined global function symbol and the exported
`lean_compacted_region_read`. Together with the exact source call, this makes
ordinary dynamic interposition technically plausible without patching the
compiler binary. No such interposition was implemented or run.

## 4. Performance, memory, permission, and trust limits

[`src/runtime/compact.cpp`](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/runtime/compact.cpp),
lines 643–656, skips the structural relocation walk when the region and its
dependencies occupy their saved addresses. The malloc route normally loses
this condition and reaches the pointer-fixup walk at lines 659–684, including
dependency-region validation/sorting where applicable. Hence it changes both
IO behavior and deserialization work.

| Possible benefit | Cost or unresolved condition |
| --- | --- |
| Sequential reads may avoid many demand faults. | Every selected region is read eagerly, including bytes not otherwise touched. |
| Heap-backed copies may avoid subsequent faults against the file backing. | Full buffers consume private anonymous memory and lose the normal mapping's clean file-backed sharing. |
| The compiler already implements relocation. | Additional object traversal and pointer writes replace its preferred-address fast path. |
| An external hook can leave compiler bytes intact. | The runtime validation environment still changes; binary identity alone does not prove equivalent execution. |

The live region-buffer allocation total can approach the sum of the full
sizes of retained imported region files, in addition to the compiler's other
heap and runtime allocations. This is different from the resident subset of
file mappings. File-cache pages may coexist with the copied buffers. Earlier
RSS and wall-time samples do not establish sufficient current headroom for
large Mathlib closures, nor the net effect of this copying and relocation.

A hypothetical hook must pass through anonymous and unrelated file mappings
unchanged: `malloc` may itself use mmap. A blanket mmap-failure hook could
therefore break the fallback it intends to select. Precise file/call/header
matching would be an implementation obligation, not something established by
this feasibility review.

Returning a normal failure for a mapping of an already permitted file would
not itself elevate permissions, access denied host information, or require
`/proc`. Nevertheless, it would be a broader runtime change than the accepted
startup adapter. Imported `.olean` contents are trusted serialized runtime
data; unchanged compiler bytes and subsequent kernel checking do not make
arbitrary loader/adapter defects automatically harmless. The existing native
adapter evidence does not validate an unimplemented mmap adapter.

Existing major-fault observations and slow module wall times make storage
behavior a plausible hypothesis, but do not identify the cause or show that
bulk copying would outperform the current mapping. No forced fallback is
recommended absent demonstrated headroom and separate evidence. There is no
reason in this assessment to disturb the ongoing fresh4 run.

## 5. Recorded bounded explicit `-j1` probe

Evidence: `explicit-j1-firstorder-probe.json` in this directory. The root agent
ran one Init-only FirstOrder fixture with a 45-second bound while fresh4
remained active, writing separate outputs. Its exact argv and cwd are retained
in that JSON. The compiler command included an actual `lean -j1` argument.

| Recorded field | Value |
| --- | --- |
| Candidate | `c988f183887896c00b09aaff9077a6ea7fb8d68f` |
| Start / finish | `2026-11-03T17:23:06.232861+00:00` / `2026-11-03T17:23:22.551218+00:00` |
| Outcome / return code | `completed` / `0` |
| Wall time | `16.31800584300072` seconds |
| User / system CPU time | `3.98996` / `2.826828` seconds |
| Maximum RSS | `636576` KiB |
| Major faults | `8590` |
| Input-block counter | `4359888`; retained in its recorded units, not converted to measured bytes |
| Source still matches candidate | `true` |
| Output matches foundation output | `true` |

Source SHA-256:

```text
7bc6796a3c9866111b6833ddfcd3d952951e87c5c355f38a1b3737a3118bb523
```

Both the probe and foundation `FirstOrder.olean` SHA-256 values are:

```text
0462a1395162fc9d28372bc673f370523e5fbacfb2555b68b7baaaf9d76777d4
```

The record's own SHA-256 when read for this report was:

```text
5d450d218500dc1eb1e34ed8f949186eee76292754bf2a94ea9a153f9daeb6bb
```

This establishes successful selector invocation and byte-identical output for
that particular module under the captured conditions. Fresh4 was concurrent;
cache state, IO contention, and other conditions were uncontrolled. It is not
a causal speedup measurement, a measured bound on every OS thread, a test of
Mathlib-heavy memory behavior, or a replacement for either full formal gate.
No source or production launcher was changed for it.

## 6. Source and local-input identity

The official release archive was previously authenticated with SHA-256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
The Lean source files below were read from the corresponding verified local
distribution under `toolchains/lean-4.35.0-linux/src/lean`. Paths in this table
are upstream paths; locally, Lake's files are beneath `src/lean/lake/Lake`.
C++ files not shipped in that directory were read from the exact pinned
official upstream source during the source assessment; the two saved shell/IO
copies were also hashed locally. No different-version documentation is used
to establish behavior.

| Upstream source | SHA-256 |
| --- | --- |
| `src/Lean/Compiler/LCNF/EmitC.lean` | `fb2069c82c5f874a41ce791a6a4e1ab9060fbbe4b178a8d7691f11c579f7317b` |
| `src/lake/Lake/Build/Module.lean` | `c67fff2c7bd95671b49ea64482c4f843f55fefdc4c038858f22a269f0b070b69` |
| `src/lake/Lake/Build/Job/Monad.lean` | `37e72e8c86410e64672e750aa77b92b947fa5028b061c38ae449aa9baaba3f8c` |
| `src/lake/Lake/Build/Actions.lean` | `9c7d7101f89eb1d0618d8a76b86c30d628932ed2d2088db29792fdf88fb1e870` |
| `src/lake/Lake/Util/Proc.lean` | `ac766e6c3ffd82923781cb302deee636d1d80018e72366f0cbcf6ad589f95097` |
| `src/Init/System/IO.lean` | `409886ee25dd6ee5455dbb83269edbef98012dd22c5b6c45198b47514aeaca25` |
| `src/Lean/Shell.lean` | `bbfcf01a93bcb9ca3f4d1264d3ad9890f3a6384dbbc949f5bf3cc286c0ec2225` |
| `src/lake/Lake/CLI/Help.lean` | `82e09cc8d8318305b0ba239d740f8650b5435c2f9e8a91b4a58fff7a0b19f6dd` |
| `src/lake/Lake/CLI/Main.lean` | `330d8ebde227bee7234892dabe2191fcd387c8d582559537baca1e207f9196d3` |
| `src/lake/Lake/Build/Context.lean` | `2aa6b7bbd3ddc9ffb5b852ebff0233adaf8483c99a9b97c22571634e32d65c97` |
| `src/runtime/object.cpp` | `1dba3476a698ab05f8f0a56c323487755790675046e90219218cb9727658ead4` |
| `src/runtime/process.cpp` | `9afd636fd49a2b67c3f90def4429c6198b457e4047c4112328cc4fd70408d0d2` |
| `src/runtime/thread.h` | `b96540b10258e4ca1d9012f8a6a33da520fdf2089a3af8f3965d52728e2929a9` |
| `src/runtime/thread.cpp` | `da93387e057790e22afed42f1fea98a99d020af29a6fff28496137e6d089256b` |
| `src/util/shell.cpp` | `502eaa752396cdff5bb448833a63be54cbbcbb3d36881eb10e235c04c64c0832` |
| `src/runtime/io.cpp` | `c8ef5d102a706d2aae710eac1f2dc9a2b6a81e5245cf5ccb36500973b32aa77f` |
| `src/library/module.cpp` | `9b85a9a7610e73f240282fe288ad81c8b160fc975caa80bd5b13ddacdd6012a8` |
| `src/runtime/compact.h` | `01dd04a27a3761c3855e2a271c1267c1b1c2e87948c293800c8a33edf8097a2e` |
| `src/runtime/compact.cpp` | `d2243af4a8d6d774d47cdf781cb15de56e257111b9c84dcd028110c601e75bae` |

Local operational inputs, relative to the recovery root:

| Input | SHA-256 |
| --- | --- |
| `work-state/tooling/pinned_native_toolchain.py` | `ab9e236bb60bf3bbd96e682cc1d48bd1b8566791a5d2213f325c3f5f81d8f19f` |
| `vfa-native-validation/scripts/check.py` | `80794fe95dd2f15ac872da3b6908921ef2898635911832ce0993176308288a29` |

These hashes identify the evidence inspected. They do not broaden the scope
of either the read-only source assessment or the single bounded probe.
