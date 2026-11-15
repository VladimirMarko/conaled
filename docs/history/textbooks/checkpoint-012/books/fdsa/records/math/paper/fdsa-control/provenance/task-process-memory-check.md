# Task-owned build process check

Read-only snapshot: 2026-11-02T06:15:49.835972+00:00.
Evidence: `task-process-memory-check.json`.

The distinct question was whether task-owned orphaned workers from the
superseded build attempts were consuming resources outside the current
checker process tree. The earlier diagnostic sampled only that active tree.
The current build was still progressing, with 180 normal project `.olean`
files observed earlier against 956 initial cold project targets; file presence
is only progress information, not a verified build or audit outcome.

## Result

No leftover worker was found among processes whose working directory was this
task workspace or one of its subdirectories. The only Lean compiler was PID
180927, a child of the known Lake 83003 / checker 82650 chain in the frozen
`conaled-ch01-review` checkout. Other scoped processes were that check's shell
and this read-only diagnostic's shell/Python process. Start ticks, parents and
working directories are retained in the JSON. No task-owned alternate compiler
or suspended secondary worker appeared in this snapshot.

The cgroup was at its 8 GiB memory ceiling. Approximate primary components were
1.13 GiB anonymous memory, 5.02 GiB file memory and 1.84 GiB kernel memory.
The kernel figure includes 1.41 GiB of slab memory; the file figure includes
the mapped-file portion. These subcategories must not be added again as
independent usage. Swap usage was zero. This is aggregate accounting and does
not attribute unrelated processes or establish a new throughput diagnosis.

The active Lean process had RSS about 695 MiB, including about 143 MiB anonymous
and 552 MiB file-backed memory. No additional owner-scoped worker was available
to stop as a supported remedy. The earlier measured file-refault/reclaim
diagnosis remains relevant; no source, checker, toolchain, resource quota,
cache, process state or concurrency setting was changed.

This was a single working-directory-scoped inventory, not a complete inventory
of unrelated processes or a proof about all future process states. No command
lines, environments, credentials or unrelated file contents were collected.
There is no further diagnostic or tuning action recommended by this result.
Continue the current gate and do not start another compiler concurrently.
