# First unrestricted full check — 14 November 2026

**The first attempt returned a real terminal failure after 1h40m19s.** The checker
exited 1 after eight Lean compiler jobs reported exit 137. It did not reach the
exhaustive axiom audit and produced no verification record. Source and worktree
were unchanged and clean at the end. This is stronger execution evidence than a
lost process handle, but it is not a passing validation gate.

## Identity and observed outcome

The isolated candidate was `18235331da1fe343d09080ca4c41173f9b4d9963`, tree
`63205d8a3ff27deb3680c613b70085163f289b83`, incorporating pinned upstream
`04514fc144dcebdd2b6d4aea5faf2f9cbf229362`. The full-spec review base remains
`9175737c2b14ef738cfb6c2cdc68d885c0805ddd`.

| Item | Actual observation |
| --- | --- |
| Start | 2026-11-14 21:27:30.162016 UTC |
| Finish | 2026-11-14 23:07:48.922060 UTC |
| Elapsed | 6,018.760 seconds |
| Source, public coverage and version checks | Passed in 29.13 seconds |
| Initial integrity guard | Passed; 3,363 ordinary cold/missing project traces invalidated; no prior artifacts hashed |
| Compilation log | 3,174 successful `Built` completion lines |
| Compiler job failures | Eight exits 137; no theorem-error diagnostic reported |
| Whole checker exit | 1 |
| Exhaustive axiom audit | Not reached after failed build |
| Verification record | Absent |
| Candidate and tracked source at end | Same commit, clean worktree |

The authenticated native setup had already completed in about 159 seconds, with
the exact Lean 4.35.0 distribution, nine dependency revisions, 9,031 requested
cache files and the prescribed smoke checks. Setup time is separate from the
elapsed check above. Installed tools and caches are outside the checkpoint.

The complete log is retained once: 1,624,681 bytes, SHA-256
`4745a20204e25c44b88bce4f4cb4f661359dfad379dc722a5e4fc690e60b5445`.
The wrapper's terminal JSON and the native launcher's actual result agree on
exit 1. A successful exit of the outer evidence-recording Python script would
only mean that it recorded the result; the checker result is the value above.

## Failed jobs and useful compilation evidence

| Failed module | Lake's reported job duration |
| --- | ---: |
| `Applications.FRP.Spec` | 189s |
| `SquareKit.Internal.Cubical.IdentityEliminationSubstitution` | 180s |
| `Examples.CubicalSourceContraction` | 142s |
| `Examples.DependentFunctionConversionSemantics` | 300s |
| `SquareKit.Internal.DependentJudgments.ReferenceApd` | 96s |
| `SquareKit.SmoothQuotientGeneratedBaseMatching` | 126s |
| `Examples.FFTScalarCosts` | 273s |
| `Examples.TwoFamilyModelRooted` | 190s |

For each of these eight files, the actual candidate blob, pinned-upstream blob
and final live file are byte-identical. Their hashes are in the compact summary.
This does not establish that an independent upstream-baseline build would have
the same outcome: the overall graph, scheduling and execution conditions matter.
Failed prerequisites also leave downstream modules unvalidated.

All four public integration clients compiled on this exact candidate:

| Client | Recorded completion |
| --- | ---: |
| `Examples.MappedPotentialAccounting` | 77s |
| `Examples.TextbookMaps` | 2.7s |
| `Examples.TextbookSequences` | 3.0s |
| `Examples.TextbookSorting` | 2.4s |

These are current compilation observations for the central coherence work.
They do not replace the exhaustive audit, both final approvals, immediate
candidate verification or snapshot comparison. They add no new chapter-coverage
claim; `COVERAGE.md` continues to distinguish active code and preserved drafts.

## Actual settings and limits of diagnosis

The child observation, taken after the native launcher and immediately before
exec of the original checker, records the selected thread-control variables as
absent, affinity over all nine visible CPUs, normal priority, and unlimited
CPU-time, address-space and data-size RLIMITs. No agent resource cap or full-run
deadline was supplied. The native receipt's `lean_threads: 1` records its
pre-child environment; the child removed that variable. Both records remain
unchanged. The native result's `timed_out: false` describes that launcher only;
it cannot rule out an external supervisor policy.

The compiler CLI's no-`-j` default was already hardware-based. Independent source
inspection confirmed this at exact compiler commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`: `Lean/Shell.lean` initializes its
thread option from hardware concurrency, `src/util/shell.cpp` passes that option
to its scoped task manager, and `src/runtime/object.cpp` uses the supplied count.
The separate ordinary-runtime initialization reads `LEAN_NUM_THREADS`, which
affects Lake. This is a statement about configured defaults, not measured active
worker counts or CPU use. Removing the environment variable does not establish
a speedup or a particular change in each compiler's active worker count.

Conventionally, exit 137 is `128 + 9`, indicating SIGKILL. The exit status does
not identify its sender or reason. Kernel OOM killing, a resource supervisor,
watchdog or process-lifetime enforcement remain possible explanations. The
available cgroup memory/OOM counters and pressure telemetry were unavailable;
an inspector's post-failure memory reading is not the failed process's peak.
The first bounded observation and its limitations are retained separately.

The outer build stayed alive while individual jobs failed. A successful job also
reported 497 seconds, while the failed jobs reported 96–300 seconds. There is no
simple common cutoff visible in these job durations. They are not matched
supervisor-event timestamps or per-process CPU measurements, so they do not
exclude every timeout or resource policy.

The user relayed a conaled agent's November 13 report from the user's own PC:
validation was interrupted repeatedly, no OOM kill or crash dump appeared in the
available logs, and a user service outside the tool shell progressed further.
That is an attributed, independently uninspected clue about tool/session
lifetime. It is not evidence of a cloud supervisor on that PC, an exact exit-137
precedent, or the cause of this run. Its referenced local session file is context
only and is not a required checkpoint recovery input. No service, supervisor
workaround or host-control change was attempted here.

Primary background references:

- [Bash exit-status convention](https://www.gnu.org/software/bash/manual/html_node/Exit-Status.html).
- [Linux cgroup v2 memory events](https://docs.kernel.org/admin-guide/cgroup-v2.html): `oom_kill` counts processes killed by an OOM killer; before/after evidence would help attribution, but was unavailable here.

## One unchanged incremental retry

After this result and the current instructions are durably saved, make at most
one unchanged, uncapped normal incremental retry. Keep the same candidate,
compiler, dependencies and gate. Do not select fresh mode or `--jobs 1` merely to
alter this experiment. Reused outputs must pass the actual guard.

Read-only inspection of this candidate's `scripts/lake_integrity.py` confirms
that `expected_artifacts` reads each module's own trace and `inspect_outputs`
checks the artifact bytes against it. `guard_outputs(repair=True)` removes only
the per-module bad set. It does not require `.lake/verification.json`.
`scripts/check.py` removes the old global success receipt when starting a check;
a failed Lake subprocess does not trigger wholesale project-output cleanup.
`scripts/lake-output-hashes.lean` computes hashes through pinned Lake code rather
than trusting hash sidecars. Thus completed outputs are eligible for reuse,
although the exact count and downstream rebuild requirements remain unknown
until the next guard runs. Reuse does not reuse an old audit success.

This first-attempt report is historical; `STATUS.md` and `REVIEW.json` own the
current retry and acceptance state. A repeated failure or interruption leaves
the receiving validation assignment open. Keep the current coherent patch's
scope fixed, preserve all unfinished mathematics, and use the proposed bounded
follow-ups in `consolidation-next-20261114.md` after consolidation.

## Retained evidence

The exact start, effective environment, terminal wrapper result, native result,
complete log and compact derived summary are in `../evidence/`. The common
README maps their original workspace paths to retained names. The summary binds
all eight failed-source comparisons and four client completion lines to the
complete log. Preparation reviews and the packable instruction correction are
under `../evidence/reviews/`; no final approval is inferred from preparation.
