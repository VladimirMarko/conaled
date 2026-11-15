# Build resources and timing assessment

Prepared 14 November 2026 from checkpoint 008, restored Git objects, the pinned Lean source, and one bounded read-only resource observation. No compiler, installation, benchmark, or configuration change ran during this assessment.

## Findings

**Yes: an agent-selected scheduling restriction was present.** The last full command explicitly used native-kit `--threads 1`; the kit also defaults to 1. It sets `LEAN_NUM_THREADS=1`. This is a conservative launcher choice, not a user requirement or conaled proof policy. Relaxing this setting to 2, then considering 4 if observed memory and paging permit, is reasonable. It is not evidence that a nine-way build would be faster or fit this host.

**Important precision: this does not mean every Lean compiler ran on one core.** At pinned Lean commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`:

- The ordinary executable runtime reads `LEAN_NUM_THREADS` to size its task pool. Lake jobs use that task machinery.
- The `lean` CLI initializes its own task manager from `ShellOptions.numThreads`. Its default is detected hardware concurrency; the separate `lean -j N` option overrides it.
- The launcher supplies an environment variable, not `lean -j 1`. The inspected conaled configuration does not add that compiler flag.
- The runtime can add workers when a pool worker waits for another task. The setting is therefore neither a global OS-thread ceiling nor an exact bound on all child processes.

Primary sources: pinned [runtime](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/runtime/object.cpp), [Lean shell options](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Shell.lean), [CLI initialization](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/util/shell.cpp), and [Lake jobs](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/lake/Lake/Build/Job/Monad.lean).

## Which limits actually apply?

| Control | Observed behavior |
| --- | --- |
| Native-kit `--threads` | Defaults to 1; last full command selected 1. Controls Lake/runtime task-pool scheduling through the environment. |
| Normal full-check wall time | The launcher's `run` path passes no timeout. Its smoke, compiler-adapter and cache-relink timeouts are separate operations. |
| Launcher memory or CPU-time cap | No `setrlimit`, `ulimit`, `lean --memory`, CPU affinity or CPU-quota setting was found in the inspected launch path and check commands. |
| conaled `--jobs N` | Bounds simultaneous compiler processes only in `--fresh` mode. Default is up to four. It is rejected for the ordinary incremental full check used here. |
| Current shell limits | Address-space, data-size and CPU-time resource limits report unlimited. This does not rule out platform controls. |
| Source/proof checks | Pins, source checks, artifact-integrity guards, cache policy and exhaustive audit are required validation behavior; resource tuning should preserve them. |

The last full candidate and new master `04514fc144dcebdd2b6d4aea5faf2f9cbf229362` have identical `lakefile.toml`, `scripts/check.py`, `lean-toolchain`, `lake-manifest.json` and `flake.lock` bytes. Thus the checked scheduling distinction remains applicable at the requested new pin.

## Host evidence and interruption diagnosis

The current observation reports 9 CPUs, affinity to those 9 CPUs, 10,206,472 KiB total memory (about 9.73 GiB), roughly 8.99 GiB available at observation, no visible swap, and about 57.8 GiB free workspace space. Standard cgroup CPU/memory quota files were unavailable. These are visible resource figures, not a verified sustained CPU quota or proof that no platform memory limit exists.

There is no matched historical CPU/quota/memory observation in the selected evidence. **Downscaling is unproven.** The checkpoint instead establishes three concrete differences from older book work: a larger integrated library, many cold project outputs, and the conservative Lake scheduling setting. Historical native probes also show substantial variability associated with file-backed page faults. None of these observations identifies why process handles disappeared.

The last full run started at 03:29:12 UTC and was still nonterminal at 03:48:22. At 03:54:13 its handle was unavailable and its lock was free. There was no terminal exit code or candidate verification record. No theorem error, explicit out-of-memory result, disk failure or timeout was recorded. Describe this as **lost execution state with incomplete validation**, not a diagnosed compiler or capacity failure.

## Timing evidence and its limits

| Run | Actual scope and result | Timing |
| --- | --- | --- |
| Older FDSA `e61bb6f`, 5 Nov | Successful full check of 1,116 project modules; 50,422 kernel-safe declarations audited; integrity guard invalidated 0 modules. Mostly reusable outputs. | 1,495.42 s total (24m55s); umbrella module 701 s; audit 739.07 s. |
| Integrated C1, 14 Nov | 3,278 cold project targets; 630 completed cold targets observed; no terminal result. | Retained summary does not establish a complete wall-time interval. |
| Integrated R3 `16440863`, 14 Nov | 3,361 integrated source modules; 2,652 missing project traces. After about 19 minutes, three additional FRP modules were recorded as built; no terminal result. | Individual module times 185, 442 and 141 s; these are not a representative sample for extrapolation. |
| R3 map-focused check | Exact corrected candidate; successful targeted build using reusable outputs. | 7.58 s; cannot predict a cold full check. |

The older successful gate demonstrates that the smaller predecessor did complete in this environment family. It does not demonstrate that the present larger candidate has ever completed here. The old total is also not a cold-build benchmark: the expensive umbrella compilation and exhaustive audit account for most of its runtime.

**There is no defensible point estimate for a full build in the newly restored workspace.** There is no completed current-candidate run or matched cold benchmark, and the previous runtime/caches were pruned. A cold full gate should be budgeted as a substantial, plausibly multi-hour task; that is a planning assessment, not a measured ETA or a promised upper bound. Do not scale the three FRP times across thousands of modules, treat Lake's job counter as newly compiled project modules, or divide an old total by the visible CPU count.

## Recommended operational decision

Use native-kit `--threads 2` explicitly for the next appropriate local build; consider 4 after an ordinary representative focused build shows useful progress without excessive paging or memory pressure. Reuse that development work as the observation rather than starting a separate environment benchmarking campaign. Record the chosen setting and actual elapsed time. The kit already supports these settings.

Keep the ordinary guarded incremental check for routine acceptance. Do not add `--jobs` to it or switch to `--fresh` solely to gain that option: fresh mode intentionally discards project reuse and would increase the work. If fresh validation is independently required, use its supported memory-appropriate `--jobs N` control and account separately for compiler-internal threads.

The user has authorized handing the complete full gate to the receiving integrator's normal development environment. Continue focused mathematical checks locally and keep the final full check, exhaustive audit, two final review approvals, immediate candidate verification, and snapshot comparison explicitly pending for the exact receiving candidate. This delegates execution; it does not convert incomplete validation into success.

## Evidence

The accompanying [structured evidence](../evidence/build-resource-assessment-20261114.json) gives compact input bindings and extracted measurements. Primary local inputs are the frozen native-kit runtime/launcher, common full-run records, the older FDSA full-run terminal record and log, the native-kit performance decision, and the [current resource observation](../evidence/current-resource-observation-20261114.json). Only intake artifacts were written; source and checkpoint contents were unchanged.

