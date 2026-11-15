# Local 1029 — validation outcome recorder

## Problem and boundary

Fresh1's execution handles became unavailable, its original run record retained
`running`/null, no success record exists, and the known process group was absent
from two scoped native observations. Its actual return and disappearance cause
remain unknown. See `validation/1002-fresh1-interruption-assessment.json`.

Provide the smallest local recorder around the unchanged validation command.
This is operational durability work, not Lean formalization or a replacement gate.
Do not modify conaled, its checker, toolchain, dependency pins, accepted cache
utility, or checkpoint generator. Use a separate local Git repository at
`work-state/validation-recorder`, with an immutable review base/candidate and
independent Standards/Spec assessment. Track locally; no GitHub writes.

## Required behavior

1. Accept an explicit argument-vector command, absolute working directory,
   attempt-output directory, candidate/mode labels and only explicitly supplied
   environment changes. Never invoke a shell or dump the inherited environment.
   Record the exact requested command/configuration and actual recorder/Python
   identity. Labels are not candidate or compiler verification.
2. Refuse pre-existing attempt output locations. Keep outputs in a newly created
   private attempt directory. Preserve earlier attempts unchanged.
3. Run one owned child using the ordinary documented ongoing `exec_command`
   lifecycle. Child stdout/stderr go directly to a regular log file and stdin is
   closed. Record driver and child identities, including the child's own process
   group. Do not depend on a long-lived functions cell or stdout-forwarding loop.
   No daemon, detached-survival claim, service/permission/OS change, auto-retry,
   or automatic downstream formal operation.
4. Record a heartbeat about every30 seconds containing time, sequence, elapsed
   monotonic time and the actual child poll result. It observes recorder/child
   state, not elaboration progress. Use a small append-only JSON-lines
   `heartbeat.log`, so active snapshots follow the existing growing-log checkpoint
   policy without changing that policy. Readers use complete valid records and
   treat an incomplete tail or stale heartbeat honestly. No mutable heartbeat
   JSON file may silently interfere with the existing workflow-stability check.
5. Atomically replace small run-state JSON records at launch/state transitions
   and completion; flush/synchronise critical launch/completion records. Preserve
   the actual raw child return from `wait()`, including negative signal returns,
   separately from the recorder's own outcome. Exit0 is not formal acceptance.
6. Record recorder exceptions and recording failures. Unknown child status stays
   unknown. A recording failure must not appear as successful recording. Handle
   interruption/failure only through the still-owned child/group, with explicit
   bounded cleanup and accurate limits; never signal an unverified PID/group or
   leave a false terminal record. Never infer universal quiescence from child exit.
7. Keep the implementation small and standard-library-only. Include focused,
   meaningful real-process tests for direct stdout/stderr retention, nonzero and
   negative raw returns, heartbeat/state interpretation and a recording-failure
   cleanup boundary. Do not run Lean or the project validation as a recorder test.
   Run the necessary tests in a clean isolated recorder checkout and retain exact
   commands/outcomes. No redundant broad tests or implementation-mirroring assertions.
8. Document short launch/monitor calls, stale-heartbeat recovery, uncertainty if
   the recorder/workspace disappears, and the distinction between local files
   and uploaded recovery checkpoints. Existing process ownership must be assessed
   before retry; stale status never authorises an automatic retry.

## Intended first real retry

Keep `LEAN_NUM_THREADS=1` and `--fresh --jobs 1` for this recording-only change.
The earlier four-worker run was intentionally interrupted for paging, and no
controlled comparison established an optimum. Fresh1's disappearance does not
establish a concurrency cause. Do not present this choice or recorder as a proven
performance or process-survival fix.

The child command remains the pinned Nix invocation of:

```sh
./check.sh --fresh --jobs 1 --candidate HEAD
```

Use isolated `vfa-validation`, unchanged candidate
`3279bacaec4087cc0d6b7e6b8ae862109cb2dfec`, the recorded Nix environment,
and new fresh2 paths. Root alone starts that formal retry after recorder review,
required checks and an uploaded complete checkpoint. No partial fresh1 outputs
are installed or used to claim resumed full verification.

All fresh/guarded/audit/regression/reviewer/final-verification requirements stay
unchanged. The accepted pre-guard preservation plan remains prospective. No
chapter receives credit from this recorder or its tests.
