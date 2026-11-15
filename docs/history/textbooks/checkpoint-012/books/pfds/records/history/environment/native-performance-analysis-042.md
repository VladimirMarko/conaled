# Native Lean import performance: evidence and limits

Recorded 2026-11-03 for checkpoint 042. This report preserves the completed
read-only source investigation and the coordinator's supplied measurements.
It belongs to the existing toolchain implementation/review loop. It does not
record runtime approval, a full project check, a proof audit, or acceptance of
either formal candidate.

## User requirement and current outcome

The authoritative steering is retained in
`session/requirements/REQUEST-native-toolchain-042.md`: the user found the
emulated tooling too slow and requested alternatives. The earlier exception
making Nix optional remains in force. Exact Lean/Lake/dependency pins, genuine
compiler behavior, candidate isolation, source/proof policy, independent
review, and final verification remain required.

The native profile executes checksum-matched copies of the official Lean
4.35.0 release binaries. Its separately recorded compatibility library supplies
the missing own-executable metadata under the launch contract in
`native-own-exe.c` and `run-native-toolchain.py`. Genuine native probes have
reported the expected Lean and Lake versions, accepted the valid theorem,
rejected the false theorem, and built and executed a small Lake executable.
Those are feasibility results. The native runtime is still awaiting approval
through the existing review loop, and the full formal gates remain pending.

The performance observations are mixed in elapsed time, but informative about
where the time goes. The measured native import mapped all 11,870 regions;
mapping failure and wholesale heap relocation are therefore **not supported
as the explanation for that run**. Large page-fault/input counters and elapsed
times substantially exceeding charged CPU time instead support import I/O and
page-fault latency as the current bottleneck. A sequential comparison showed
less elapsed and CPU time with native execution, but one pair cannot establish
a general speedup factor.

## Actual observations

The following values were supplied by the coordinator from the named retained
records. The report author did not start another compiler or rerun these
measurements while writing this report.

### Native import with mapping statistics

Evidence: `native-import-stats-042-r1.json`.

| Measurement | Observed value |
| --- | ---: |
| Imported regions | 11,870 |
| Memory-mapped regions | 11,870 |
| Imported artifact bytes | 2,009,200,824 |
| Elapsed time | 102.32 s |
| User CPU time | 1.864 s |
| System CPU time | 22.263 s |
| Major page faults | 120,020 |
| Input-block counter | 54,233,160 |
| Maximum resident set | 1,050,360 KiB |

Lean's printed label says “number of imported modules,” but its implementation
counts compacted regions, which can include multiple artifact parts per module.
The byte total likewise describes imported artifact regions, not resident
memory. The resource input-block counter is retained as measured; this report
does not convert it into an asserted number of bytes transferred.

### Sequential native/QEMU comparison

Evidence: `native-qemu-import-comparison-042-r1.json`. Both invocations used the
same import-Lean fixture under the coordinator's controlled sequential
comparison, with no live formal builds.

| Measurement | Native | QEMU |
| --- | ---: | ---: |
| Elapsed time | 31.786 s | 86.080 s |
| User CPU time | 1.473 s | 9.486 s |
| System CPU time | 7.885 s | 21.369 s |
| Major page faults | 39,473 | 95,493 |
| Input-block counter | 15,703,624 | 41,582,248 |

Native execution was faster in this pair and used substantially less user CPU
time. The page-fault and input counters also differed greatly, so the elapsed
time difference cannot be attributed solely to CPU emulation overhead. Native
elapsed time varied from approximately 32 seconds in this comparison to
approximately 102 seconds in the separately recorded statistics run. Cache
state, file-backed page faults, and surrounding resource conditions were not
held identical across all observations. This evidence supports a native CPU
advantage while leaving end-to-end performance variable; it does not support
a universal “2.7 times faster” claim.

### Earlier genuine feasibility results

`session/validation/native-cli-042-r1.json`, read during the investigation,
records all four public CLI checks passing:

- Exact Lean version: exit 0 in 0.180 seconds.
- Exact Lake version: exit 0 in 0.110 seconds.
- Valid theorem, including `import Lean`: exit 0 in 57.976 seconds, reporting
  that the theorem does not depend on any axioms.
- False theorem, including `import Lean`: exit 1 in 99.896 seconds, with the
  actual type-mismatch diagnostic.

Thus the initially slow CLI suite eventually completed; those invocations
were not demonstrated to be deadlocked. A separate bounded import probe in
`session/validation/native-import-diagnosis-042-r1.json` timed out after about
25 seconds, while its implicit-Init counterpart completed in 5.390 seconds.
That timeout remains a timeout, not an inferred compiler failure or success.

`session/validation/native-lake-build-042-r1.json` records a genuine Lake build
through Lean, C compilation, and native linking in 4.735 seconds, followed by
execution printing `42`. That small program uses implicit `Init`; it does not
exercise the full `import Lean` artifact footprint. Historical QEMU smoke
timings are preserved separately and are not treated as a cache-controlled
benchmark against these native runs.

## What the exact compiler source establishes

The investigation used the installed v4.35.0 Lean sources and matching
versioned upstream C++ sources. None was modified or compiled as a replacement.

### Ordinary import scope

`Lean/Elab/Import.lean`, `processHeaderCore`, selects `OLeanLevel.private` for a
file without a `module` header. In `Lean/Environment.lean`, ordinary imports
without a precomputed artifact setup can load the exported, server, and private
`.olean` parts and the `.ir.sig` and `.ir` parts. These operations go through
`CompactedRegion.read`. This explains why a plain `import Lean` smoke test
exercises substantially more artifact data than the small implicit-Init
executable. It does not itself identify which I/O operation caused a delay.

`Environment.importModules` is instrumented with `profileitIO "import"`.
The supported `--profile` option and `-Dprofiler.threshold=0` expose component
timings. `--stats` calls `Environment.displayStats`, which reports the region
count, `isMemoryMapped` count, and region byte total. The frontend prints those
statistics even when an ordinary theorem error occurs after successful import.
These diagnostics require no process-filesystem inspection or custom compiler
instrumentation.

### Mapping and relocation

`src/library/module.cpp`, `lean_compacted_region_read`, reads the saved
`base_addr` from each artifact header and, when built with `LEAN_MMAP`, attempts:

```text
mmap(saved_address, artifact_size,
     PROT_READ | PROT_WRITE,
     MAP_PRIVATE | MAP_FIXED_NOREPLACE, file_descriptor, 0)
```

Only a mapping at exactly the saved address is accepted. A successful mapping
at another address is unmapped and treated as unavailable. If no acceptable
mapping exists, the implementation allocates a buffer and reads the full
artifact into it.

`src/runtime/compact.cpp`, `region_reader::read`, has a fast path when both the
region and all supplied dependency regions occupy their saved addresses. It
then skips the structural object walk. Otherwise it sorts and validates the
dependency regions and walks the data to repair pointers. This made mapping
failure a plausible initial performance hypothesis.

The observed statistics supersede that hypothesis for the measured native
run: all 11,870 imported regions reported successful memory mapping. The
investigation therefore does not attribute that run's 102-second elapsed time
to the allocation/full-read fallback or propose changing mmap behavior.

### Configuration limits

`src/CMakeLists.txt` declares `option(MMAP "MMAP" ON)` and adds the preprocessor
definition `LEAN_MMAP` when that build option is enabled. This is a compile-time
choice, not a runtime environment setting. The inspected read/relocation code
provides no supported CLI or environment knob to disable mapping or select a
preferred address. Saved addresses are derived from module names during
artifact creation and stored in the artifact headers.

The supported `LEAN_IMPORT_WORKERS` setting appears in the incremental snapshot
loader in `Lean/Elab/Frontend.lean`. It does not control the ordinary import
path used by these CLI fixtures. It therefore supplies no established remedy
for their observed latency.

## Operational implications and remaining gates

The current evidence favors continuing the native route through independent
review because it removes the observed CPU emulation cost while preserving
the original compiler bytes. The elapsed-time evidence must remain qualified:
large import I/O delays can dominate either runtime. The exact-source analysis
and measurements do not justify an mmap interposer, compiler patch, fabricated
result, unsupported runtime flag, changed resource budget, or weaker proof gate.

No additional ordinary native execution host is exposed in the current
environment. A separate developer machine or runner would need to be an
available, authorized execution environment; this investigation did not
provision one. QEMU remains a recorded recovery fallback, while native
feasibility is the current development direction requested by the user.

The interrupted QEMU formal run and its partial record remain historical
evidence. Changing the execution route is not continuation of the same formal
run. After runtime review, genuine full validation must use fresh run records,
the exact isolated candidates, frozen dependencies and helpers, unchanged stock
build/audit commands, and final stock candidate verification. None of the
performance or smoke-test records grants formal acceptance.

## Source provenance

Exact upstream source read during the completed investigation:

| Source | SHA-256 |
| --- | --- |
| [v4.35.0 `src/library/module.cpp`](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/library/module.cpp) | `9b85a9a7610e73f240282fe288ad81c8b160fc975caa80bd5b13ddacdd6012a8` |
| [v4.35.0 `src/runtime/compact.cpp`](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/runtime/compact.cpp) | `d2243af4a8d6d774d47cdf781cb15de56e257111b9c84dcd028110c601e75bae` |
| [v4.35.0 `src/CMakeLists.txt`](https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/CMakeLists.txt) | `0cc2ed9110836428d6d48d73c9042faa7980c3475f3943837de577fd5a04d1c4` |

Installed exact-release source references:

- `toolchains/lean-4.35.0-linux/src/lean/Lean/Environment.lean`:
  `readModuleDataPartsOfMod`, `readIRPartsOfMod`, `importModulesCore`,
  `importModules`, and `displayStats`.
- `toolchains/lean-4.35.0-linux/src/lean/Lean/CompactedRegion.lean`:
  region metadata and the public `isMemoryMapped` field.
- `toolchains/lean-4.35.0-linux/src/lean/Lean/Elab/Import.lean`:
  `processHeaderCore` import-level selection.
- `toolchains/lean-4.35.0-linux/src/lean/Lean/Elab/Frontend.lean`:
  `loadIncrSnapshot`, its `LEAN_IMPORT_WORKERS` setting, and statistics reporting.
- `toolchains/lean-4.35.0-linux/src/lean/Lean/Util/Profile.lean`:
  supported profiler options.

No compiler job or new diagnostic command was run to create this report. The
only change made for this preservation task is this report file.
