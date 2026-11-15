# Validation health check — 2026-11-02

Read-only diagnostics for local candidate `ad730010ab1929bbd7a16a035c7990a6f328b178`.
Only processes whose current directory was this task's workspace (or a child
directory) were inspected. No processes, source files, build outputs, resource
limits, or validation commands were changed.

## Observed progress

At approximately 03:01–03:02 UTC, the isolated full check had one active Lean
compiler, checking pinned Mathlib's `Analysis.Normed.Operator.Mul`; the focused
check had one active Lean compiler, checking the new `SharedList.Observation`.
Both parent Lake processes remained alive. There was no evidence of runaway
parallelism within either job.

Across a 20.0007-second sample, the full check's compiler accumulated 5.24 CPU
seconds and the focused compiler accumulated 3.88 CPU seconds. Thus both were
making computational progress despite an unchanged end of log. Sleeping process
leader states (`__futex_wait`) alone did not imply a stalled multithreaded process.

## Resource evidence

- Visible CPU count: 9; cgroup CPU quota: `800000 100000` (8 CPUs).
- Observed aggregate load average: approximately 15.
- Cgroup memory limit: 8,589,934,592 bytes (8 GiB).
- Observed memory use: 8,589,807,616 bytes, effectively at the limit.
- Memory events: 17,545,993 `max` events; no OOM or OOM-kill events recorded.
- Memory counters included 930,620,150 page scans, 806,707,700 page steals and
  15,170,132 major page faults since the cgroup's counters began.
- The full compiler's sampled RSS was about 350 MiB; the focused compiler's
  sampled RSS was about 254 MiB. These are snapshots, not peak-memory bounds.

The evidence is consistent with substantial shared resource/reclaim pressure.
It does not establish which other workload accounts for pressure, and no other
workspace or process command line was inspected.

## Recommendation and limits

Avoid starting additional compilation. The current check is alive, so waiting
for it is justified. Finishing or stopping genuinely redundant focused work
would release that process's memory; changing machine-wide resource settings or
interfering with other workloads is not justified by this task.

Do not switch gates merely because the build is slow. `README.md` delegates
incremental scheduling to Lake, disallows `--jobs` outside fresh mode, and
requires the exact candidate check, exhaustive audit, saved verification record
and final `--verify-candidate`. This diagnostic is neither validation success
nor an acceptance decision.
