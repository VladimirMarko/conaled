# Validation concurrency follow-up — 2026-11-02

Read-only assessment for corrected candidate `70a1477`, while its exact full
check ran alone in `validation-persistence`. No job, source, artifact, runtime
limit, or check command was changed by this reviewer.

## Current resource evidence

At approximately 03:12–03:13 UTC, three narrowly scoped process samples each
showed one active Lean compiler for this task's full check. Both the Lake
process and its compiler children had `LEAN_NUM_THREADS=1`. The log showed
project modules finishing in roughly 2–4 seconds, substantially faster than
the earlier resource-pressure episode. One sampled Mathlib compiler had used
5.17 CPU seconds over 2.49 elapsed seconds and about 758 MiB resident memory.

Aggregate observations:

- CPU quota: 8 cores; observed load average approximately 4.85.
- Memory: 8,567,222,272 bytes used against an 8,589,934,592-byte limit.
- Anonymous memory: about 1.11 GB; file cache: about 5.79 GB;
  kernel accounting: about 1.60 GB.
- No OOM or OOM-kill event recorded. Reclaim counters remain high.

Near-full total memory therefore includes a large file-cache component. The
snapshot supplies no memory-specific reason to rule out two workers, although
additional concurrency can still cause reclaim pressure and slower execution.
Only this task's process arguments and narrowly selected scheduling variables
were inspected; other workspaces and process arguments were not inspected.

## Supported scheduler control

The installed Lean 4.35.0 Lake sources establish that:

- `Lake/Build/Job/Monad.lean`, `Job.async`, creates a `BaseIO.asTask` with default
  task priority.
- `Lake/Build/Actions.lean`, `compileLeanModule`, invokes `rawProc`.
- `Lake/Util/Proc.lean`, `rawProc`, waits for `IO.Process.output`.
- The installed Lake CLI help exposes no `--jobs`/`-j` build option; source
  searches found no separate `maxJobs`/`LAKE_JOBS` setting.

Exact versioned primary runtime source:

<https://raw.githubusercontent.com/leanprover/lean4/v4.35.0/src/runtime/object.cpp>

Lines 1097–1122 define `lean_init_task_manager_using`, read `LEAN_NUM_THREADS`
through `getenv`/`atoi`, fall back to `hardware_concurrency()` when it is absent,
and initialize the task manager with the resulting worker count. This file was
read directly from the official repository. The initial guessed `task.cpp`
path did not exist; the official runtime directory listing identified
`object.cpp`. No external code was installed or executed.

Together with the observed single compiler, this establishes why
`LEAN_NUM_THREADS=1` constrains Lake's ordinary asynchronous compile jobs.
It does not mean the entire OS process has exactly one thread: process I/O and
compiler internals can have additional threads.

## Recommendation

`LEAN_NUM_THREADS=2` is a supported, modest increase to the runtime worker pool.
There is no measured reason to reject it here, but speedup is an inference,
not a benchmark result or a guarantee. The setting takes effect at process
initialization; changing it requires a new check invocation.

The root coordinator may interrupt only the known task-owned run, record the
interruption, and restart the same `./check.sh --candidate HEAD` in the same
isolated checkout with `LEAN_NUM_THREADS=2`. Preserve the completed incremental
outputs and all existing source, coverage, integrity, exhaustive audit, saved
record and final-verification gates. No fresh-mode rebuild or repository
tooling change is needed merely to alter execution concurrency. This reviewer
performed no interruption or restart.
