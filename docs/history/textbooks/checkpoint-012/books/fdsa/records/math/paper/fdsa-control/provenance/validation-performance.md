# Fresh validation performance diagnosis

Candidate: `1aabd512284fe86254278ac631eda061d311050b`.
Checkout: `/workspace/scratch/845aa1048b05/conaled-ch01-review`.
Command under observation: `./check.sh --fresh --jobs 4 --candidate HEAD`.

## Finding and recommendation

The observed slowdown is dominated by memory-pressure-driven file-page reclaim
and rereading, with heavy kernel/I/O work. It is not explained by a one-core CPU
quota, increased CPU quota throttling, or an unbounded number of checker workers.
This is an inference from the counters below; it is not a performance proof or
a storage hardware benchmark.

**Recommendation to the coordinator:** preserve the first attempt's log and
process evidence, then restart the unchanged candidate check with
`./check.sh --fresh --jobs 1 --candidate HEAD`, with no additional focused builds
running concurrently during the comparison. The evidence supports trading the
partial first attempt for a smaller active working set. The measured RSS/PSS
does not contradict this: residency is being constrained by reclaim, while our
own four workers repeatedly fault and reread substantial file data. A material
improvement is plausible, but its magnitude cannot be established without the
new run. The task did not inspect other workspaces or attribute all shared
resource consumption to this build.

The coordinator explicitly owns any restart. **This diagnosis sent no signals,
changed no process, started no validation build, and changed no checker, source,
compiler, manifest, or acceptance policy.** The existing observer remains an
observation-only process. An interrupted first attempt must be recorded as
superseded before completing its audit, not as successful validation.

## Bounded counter evidence

Two samples ran from `2026-11-02T03:02:41.676274+00:00` to `2026-11-02T03:03:01.707714+00:00`,
an interval of 20.03 seconds. Raw evidence is in
[validation-performance-samples.json](validation-performance-samples.json).
Only checker PID 46434, its direct Lean children, and aggregate host/cgroup
counters were inspected.

| Observation | Measured result |
| --- | --- |
| Cgroup memory ceiling | 8 GiB (`memory.max = 8589934592`) |
| Cgroup memory usage, first / second sample | 7.999989 / 7.999935 GiB |
| Additional memory-limit events | 247,286 |
| Additional direct reclaim page scans | 11,050,273 |
| Additional file workingset refaults | 9,828,646 pages |
| Additional cgroup major page faults | 164,014 |
| Additional cgroup-accounted block reads | 37.60 GiB |
| Cgroup CPU quota | 800,000 / 100,000 microseconds = 8 cores |
| Additional CPU throttled periods / throttled time | 0 / 0 microseconds |
| Cgroup CPU usage during interval | 66.58 CPU-seconds (3.32 cores on average) |
| Cgroup CPU time in kernel | 59.97 CPU-seconds |
| Swap usage; OOM kills | 0; no increase (counter remains 0) |

The host-level memory counter showed substantially more available memory, but
that does not remove the cgroup's 8 GiB ceiling. Pressure-stall information
files were unavailable, so no PSI percentages are claimed. Block-read counters
show accounted traffic; they do not identify physical storage characteristics.

## Our workers during the sampled interval

| PID | Module | User CPU seconds | Kernel CPU seconds | Major faults | Accounted reads, GiB |
| --- | --- | ---: | ---: | ---: | ---: |
| 60742 | Applications/Progress/Examples.lean | 0.83 | 3.14 | 15,250 | 1.81 |
| 64542 | SquareKit/SmoothAlgebra.lean | 0.07 | 4.98 | 11,470 | 4.28 |
| 64925 | SquareKit/SmoothHadamard.lean | 0.01 | 3.71 | 12,762 | 3.12 |
| 64941 | Examples/AlgebraicScalar.lean | 0.09 | 3.55 | 14,703 | 2.61 |
| **Total** | Four fresh-check workers | **1.00** | **15.38** | **54,185** | **11.81** |

Our four workers used only 0.82 cores on average, and
93.9% of that CPU time was kernel time. Those observations,
combined with refaults and reads, explain why wall time can rise into hundreds
of seconds without corresponding proof-elaboration CPU time. The checker's
Python process remained effectively idle while awaiting its workers.

There were exactly four compiler children, consistent with the configured
`--jobs 4` bound. The sampled Lean processes generally had five OS threads;
one grew to thirteen late in the sample. A raw thread count alone is not
proof of CPU oversubscription. The absence of added CPU throttling and the
fault/I/O evidence identify memory pressure as the primary observed bottleneck.

## RSS and PSS

A separate snapshot at `2026-11-02T03:05:05.110881+00:00` is retained in
[validation-performance-pss.json](validation-performance-pss.json). PSS apportions
shared resident pages rather than counting each mapping in full. These are
instantaneous residency figures under active reclaim, not maximum required
working sets. They must not be added to cgroup file-cache totals, which overlap
with resident file pages.

| PID | Module | RSS, MiB | PSS, MiB | Anonymous PSS, MiB | Page tables, MiB |
| --- | --- | ---: | ---: | ---: | ---: |
| 64542 | SquareKit/SmoothAlgebra.lean | 455.8 | 352.3 | 170.9 | 65.3 |
| 64925 | SquareKit/SmoothHadamard.lean | 279.4 | 204.5 | 127.8 | 76.5 |
| 64941 | Examples/AlgebraicScalar.lean | 368.6 | 262.5 | 90.4 | 57.6 |
| 66434 | SquareKit/AlgebraicKL.lean | 221.0 | 157.1 | 82.6 | 57.6 |
| **Total** | Four fresh-check workers | **1324.9** | **976.5** | **471.7** | **257.1** |

The checker itself used approximately 11.4 MiB RSS/PSS. The four workers do not
account for all 8 GiB of shared cgroup usage. Nevertheless, reducing our active
worker count should reduce concurrent file working sets, private memory, and
page-table demand. Because the current run is reclaim-bound, losing nominal
parallelism is a reasonable tradeoff. Ending overlapping work owned by this
task normally, and avoiding new overlaps, may also help; no other workload was
inspected or changed.

## Why the change requires a new attempt

The unchanged `scripts/check.py` initializes
`ThreadPoolExecutor(max_workers=jobs)` and caps active jobs at the supplied
value. It provides no supported control channel for changing that value in an
already-running attempt. The README explicitly supports `--fresh --jobs 1` for
serial compilation. A new attempt preserves the candidate commit and all proof
gates but gives up the first attempt's incomplete, private build progress.

## Verified process snapshot for coordinator handoff

At `2026-11-02T03:06:09.124287+00:00`, the following snapshot contained only the checker and
its recursively enumerated descendants. All executable working directories
were verified as `/workspace/scratch/845aa1048b05/conaled-ch01-review`.
The checker executable was the pinned Nix Python 3.13.15; each child executable
was `/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean`, with output
under this checkout's `.lake/fresh-check-pb_o_nw4/`.

| PID | Parent PID | Kernel start ticks | Role / module |
| --- | --- | --- | --- |
| 46434 | 46431 | 2069560 | checker |
| 64925 | 46434 | 2235296 | SquareKit/SmoothHadamard.lean |
| 64941 | 46434 | 2235750 | Examples/AlgebraicScalar.lean |
| 66434 | 46434 | 2250443 | SquareKit/AlgebraicKL.lean |
| 67719 | 46434 | 2267311 | SquareKit/SmoothLocalGluing.lean |

The exact executable, command, working directory, and start time fields are in
[validation-attempt1-processes.json](validation-attempt1-processes.json).
**This is a snapshot, not an instruction to signal stale PIDs.** Revalidate
identity and parent relationships immediately before any coordinator action;
the running checker can finish workers and spawn replacements. The wrapper
parent, observer, focused build, and all unrelated processes are outside this
PID list. No process intervention was performed by the diagnosing agent.
