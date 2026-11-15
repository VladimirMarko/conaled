# Exit 137 during unrestricted full validation

One bounded inspection was made at **2026-11-14 21:39:31 UTC**. The candidate
remained frozen; this agent did not launch a build, retry, kill, source edit,
resource change or environment repair.

## Established observations

The observed log prefix records:

```text
✖ [9478/9590] Building Applications.FRP.Spec (189s)
error: Lean exited with code 137
```

The preceding message is a Mathlib module-system warning, not a theorem error.
Other modules completed after this failure. The inspected prefix contains no
overall terminal result or full-audit success. It covers 1,004,505 bytes, SHA-256
`3550800d56c5a516b2fc56b5de361eac503118ddcef5777e5c5636263071948d`.

**The failing module is unchanged upstream.** Its 12,007 bytes are identical in
the live build, delivered candidate
`18235331da1fe343d09080ca4c41173f9b4d9963`, pinned master
`04514fc144dcebdd2b6d4aea5faf2f9cbf229362`, and previous master
`983d0b6b602b71541f182737011621a8805be27b`.
Its SHA-256 is
`c0b5d8155c574329fac0b4aced18c69322b33f8e4e6bbb5278365a7fc57211f8`.
No `Applications/FRP` or `SquareKit` source path differs between the delivered
candidate and pinned master.

## Memory observation and limits

These exact `/proc/meminfo` fields were read **after** the failure:

| Field | Observed value |
| --- | ---: |
| MemTotal | 10,206,472 kB |
| MemFree | 1,545,560 kB |
| MemAvailable | 6,612,064 kB |
| Cached | 4,840,936 kB |
| SwapTotal | 0 kB |
| SwapFree | 0 kB |

Here **6.31 GiB means available memory**, not used memory. It is neither the
failed compiler's peak nor a measurement at the instant of its termination.
The companion JSON retains all selected meminfo fields exactly.

Cgroup memory limits, current/peak usage, OOM-event counters, CPU quotas, and
pressure telemetry were unavailable at the inspected standard paths. Inspector
address-space, data-size and CPU-time limits were unlimited. Those observations
do not establish the failed child's peak, effective platform quota, or absence
of an earlier resource shortage.

Exit 137 is compatible with the conventional encoding of SIGKILL. It alone
does not prove the signal, identify its sender, or establish an OOM kill. No
accessible OOM counter or kernel diagnostic in this inspection settles the
cause. Do not describe this as a theorem failure or a diagnosed OOM.

## Effect of unrestricted scheduling

Removing `LEAN_NUM_THREADS` allows Lake's ordinary hardware-based task-pool
default. Lean CLI children already had their own hardware-based default before
that change; removing the environment setting does not by itself multiply each
child's thread allowance.

More simultaneous compiler jobs can increase combined private heaps and active
working sets. That is a plausible memory-risk mechanism, **not an established
cause of this failure**. File-backed import pages may be shared, and task-pool
behavior is not an exact process ceiling; multiplying a single child RSS by a
visible CPU count would not estimate aggregate memory reliably.

## Conditional next step; not executed

After the actual overall terminal result, **one unchanged, uncapped incremental
retry** is reasonable if substantial valid outputs completed and the remaining
failures are exclusively exit 137. Preserve the first run's terminal evidence,
keep the exact candidate and inputs, and use the same unrestricted command and
full checker/audit.

The integrity guard can reuse successful outputs, leaving fewer independent
modules requiring simultaneous compilation. This may reduce aggregate resource
pressure without introducing a numerical cap. It is not guaranteed: retrying a
failed prerequisite may also release a large downstream dependency set.

A proof error, integrity mismatch or other failure needs its own handling.
Repeated exit 137 or lost execution state leaves final receiving validation
pending; it does not justify an automatic environment-repair campaign.
**No retry has occurred as part of this assessment.**

