# ConnectionAssessment validation diagnostic

Read-only inspection on 2026-11-02 by `/root/chapter02_shared`.
Candidate: `226ebaef53b9eba97bef4b3b6ca364fdea488c69`.
Isolated checkout: `validation-imports`.

## Result: the suspected stuck module completed

The requested compiler identity was PID417137, start_ticks6917141, working
directory exactly `/workspace/scratch/ca9a61d0bf30/validation-imports`.
At the first inspection that PID no longer existed, so no process-memory
contents were read for that identity and no new per-process counters can be
attributed to it. A narrow inventory checked cwd before reading only this
checkout's current Lean process metadata; the then-current compiler was
PID432356/start_ticks7027170 for `Examples/AbstractFIFO.lean`.

The authoritative full-check log
`active-validation/import-footprint-226ebae-full.log` explicitly records:

`Built Applications.Orbifold.ConnectionAssessment (820s)`

It is followed only by the existing module-import/style warnings concerning
`<;>`. There is no source error for this module. Its Lake trace exists, contains
saved output hashes, and has modification time2026-11-02T16:14:29.955954UTC.
The full log then advances through timing, sequences and other modules. Thus
this module is no longer a remaining blocker, and the missing PID is consistent
with its successful completion, not evidence of a vanished unfinished job.

The reported820seconds is not an uninterrupted execution benchmark. The
coordinator's `validation/import-footprint-pause.json` records this exact PID
paused at16:05:24.879943UTC and resumed at16:13:27.858509UTC:482.978566seconds.
That pause occurred during this compiler's lifetime. Do not attribute the whole
reported duration to tactic work or compare it directly to an unpaused run.

The full candidate check was still running and `.lake/verification.json` was
absent at inspection. A successful module is not full build/audit acceptance.

## Source and proof demands

`ConnectionAssessment.lean` is a small coordinate calculation development:
three definitions and seven theorems using real-pair/complex algebra, ring
normalization, field simplification, linear/nonlinear arithmetic, and one
polynomial derivative. Source inspection finds no open-ended recursive tactic
program or heartbeat override. This does not profile any particular tactic or
prove that all its tactic steps are cheap.

The source and `Pose.lean` are unchanged between prior candidate70a1477 and the
current226ebae (empty scoped Git diff). The direct imports are Pose and
`Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv`. The source invokes no
sine/cosine/tangent derivative theorem. Its derivative calculation uses
`hasDerivAt_const`, `HasDerivAt.sub`, `HasDerivAt.pow` and
`HasDerivAt.smul_const`. The pinned primary declarations of the last two are in
`Mathlib/Analysis/Calculus/Deriv/Pow.lean` and `Deriv/Mul.lean`; both are already
reachable through Pose's import closure.

## Import inventory and its limits

A read-only source inventory reused the existing `scripts/check.py`
`executable_source` function to mask strings and nested comments, then recognized
ordinary/public/meta imports and the `import all` modifier. Compiler-library
imports were terminal because their transitive sources were not inventoried.
This is an import-source inventory, not a Lean metadata certificate or a
resident-memory measurement. The final counts are:

| Root | Reachable module names, including terminal compiler imports |
| --- | ---: |
| Pose | 3592 |
| Trigonometric.Deriv | 2386 |
| Their union | 3614 |
| Added by the direct trigonometric import beyond Pose | 22 |

There were212 terminal compiler-library imports and no unresolved noncompiler
imports. No actual `import Mathlib` umbrella directive was found in this
closure. A preliminary unmasked regex mistakenly matched documentation examples
in Mathlib's Exponential and Rify modules; that result was discarded and is not
used for any conclusion.

Static available compiled files over the inspected closure sum to
860082216bytes of `.olean` and1539357464bytes of `.olean.private`, plus
52514376bytes of server data and201442104bytes of IR. The22 extra modules
contribute2868616bytes of `.olean`,7868544bytes of `.olean.private`,297528bytes
of server data and73584bytes of IR. These totals exclude terminal compiler
modules and do not establish that any particular process maps or touches all
these bytes. They are not an RSS estimate and do not explain the previous
9.18GB virtual-size observation by themselves.

The direct trigonometric import is therefore a plausible small cleanup, not a
large-footprint culprit: it adds about10.2MiB of main/private olean data against
about2.23GiB in the inspected main/private closure. Actual memory or speed
improvement has not been measured. Import removal still needs compilation; no
such change or experimental compiler invocation was made in this diagnostic.

## Resource evidence and interpretation

Prior task-owned measurements, retained in
`validation/serial-progress-observation.json` and
`validation/two-worker-reclaim-observation.json`, sampled the same unchanged
source on earlier runs. One serial sample had118877major faults and34.35CPU
seconds over118.38seconds elapsed, with about415MB RSS and9.18GB virtual size.
The two-worker sample had250915major faults and80.92CPU seconds over300.76seconds
for ConnectionAssessment. These are prior-run observations, not new samples of
PID417137. They support substantial page-reclaim/I/O pressure as a plausible
explanation for slow progress under the shared8GiB limit. They neither locate a
particular tactic nor establish that imports are the sole cause. Virtual size
must not be substituted for resident working set.

Successful completion in the unchanged exact candidate rules out a continuing
hang at this module. The existing evidence does not justify weakening gates,
changing proof bodies, raising limits, or blaming a specific tactic.

## Actionable handoff

1. Keep the current isolated full check running, preserve its completed Lake
   outputs, and monitor new actual terminal results. Do not restart merely to
   recheck this completed module.
2. Continue serializing focused development compilers; prior reclaim counters
   justify avoiding gratuitous additional heavy compilers. This is workload
   hygiene, not a measured optimal concurrency claim.
3. If the same unchanged module becomes a reproducible bottleneck on a future
   necessary fresh build, isolate profiling outside a candidate acceptance run
   before changing its proofs. The current log alone cannot identify a
   pathological tactic. A separately validated direct-import cleanup is possible
   but its statically small incremental footprint makes it a low-priority fix.
4. Retain the full exact-candidate build, exhaustive audit, matching success
   record, final verify and independent review requirements unchanged.

No source, check output, dependency checkout, tooling, process signal, or resource
limit was modified. Only this diagnostic record was written. No new review loop
or benchmark was started.
