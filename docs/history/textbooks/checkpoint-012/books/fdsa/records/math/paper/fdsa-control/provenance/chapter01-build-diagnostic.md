# Chapter 1 frozen-build diagnostic

Read-only sample: `2026-11-02T05:31:25.643241+00:00`–`2026-11-02T05:31:45.701449+00:00` (20.06 seconds).
Evidence: [chapter01-build-diagnostic.json](chapter01-build-diagnostic.json).
Exact initial process identities:
[chapter01-build-processes.json](chapter01-build-processes.json).

## Conclusion

**Persistent memory reclaim and file-page I/O remain the observed bottleneck.
No evidence-supported acceleration is available within the frozen-gate
constraints.** Keep the current gate running and avoid additional compilers.
This diagnosis recommends no tuning, restart, or source/tool change.

Only checker **82650**, its Lake child **83003**, and their single active Lean
child **155844** were inspected, together with aggregate cgroup counters.
All process working directories matched
`/workspace/scratch/845aa1048b05/conaled-ch01-review`; parent relationships and
kernel start times matched the recorded task. The active module was
`SquareKit.SmoothPresentedDual`. The checker command remains
`python3 scripts/check.py --candidate HEAD`; Lake runs
`--no-cache --rehash build` with the explicit integrated targets.

## Evidence

| Counter | Change / observation over 20.06 seconds |
| --- | --- |
| Cgroup memory | 8.000000 → 7.999935 GiB against an 8 GiB ceiling |
| Memory-limit events | +238,141 |
| Direct reclaim page scans | +10,415,744 |
| File-page workingset refaults | +9,367,829 |
| Aggregate accounted block reads | +35.74 GiB |
| Lean child major faults | +32,270 |
| Lean child accounted block reads | +6.85 GiB |
| Lean child user / kernel CPU | 0.42 / 4.39 seconds |
| Lean active-thread runnable-queue wait | +0.389 seconds |
| CPU quota | 8 cores; no additional throttled periods or time |
| Lean process count | One at both samples |
| Swap usage / OOM kills | Zero; no increase |

The Lean child spent 91.3% of its measured CPU time in the kernel.
Its active worker's final wait channel was `folio_wait_bit_common`, consistent
with waiting on a memory folio/page; combined with the major-fault and read
counters, this supports the paging/I/O diagnosis. CPU runnable-queue delay was
small compared with wall time, and quota throttling did not increase.

The child's RSS/PSS changed from
511.5/493.0 MiB to
316.0/307.6 MiB.
Its anonymous PSS slightly increased while file-backed PSS fell from
293.8 to 100.4 MiB.
This is consistent with file residency being reclaimed; low instantaneous RSS
does not demonstrate that the file working set fits comfortably in memory.
The checker and Lake mostly waited for their child and did not show meaningful
CPU work during the interval.

The resource counters are shared aggregates. This task did not inspect
unrelated processes or identify who accounts for the remaining resource use.
It also does not establish physical disk throughput or prove all blocked time
has a single cause. With one compiler already active, no further local
concurrency reduction is available while keeping the gate running. Additional
CPU parallelism is not supported by this evidence as a remedy.

No signals, resumed processes, builds, Git commands, source mutations, or
toolchain changes were performed. The terminated secondary session and its old
PIDs were not accessed. The gate and root's exit-status collection are unchanged.
