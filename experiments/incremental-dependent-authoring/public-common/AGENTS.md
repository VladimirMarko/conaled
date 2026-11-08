# Frozen author handoff

You are an independent author in the coordinator's existing implementation and
review loop. Read `PROTOCOL.md`, `TASK.md`, `AUTHOR.md` and `GUIDANCE.md`. Those
files specify the task, budget, allowed inputs, route and evidence requirements.
Do not start another implementation/review workflow or delegate work.

Use the pinned environment through `direnv exec .`. Run every Lean attempt,
including declaration inspection, through
`direnv exec . python3 check_attempt.py attempts/AttemptNN.lean` with a new name
for each revision. Write only under `attempts/`. Keep attempted bytes, diagnostics,
an activity log and a final outcome record. Do not edit the public manifest,
source libraries, environment, wrapper or build artifacts.

Read only this handoff and its pinned dependency/toolchain sources. A reference
inside copied source does not grant access to a missing file, another checkout,
Git history, the other arm or the web. The fresh Git index exists only to keep
Nix from copying dependency caches; it contains no original repository history.
The coordinator owns final replay, statement/axiom checks and independent review.
Ask the coordinator for environment help or contract clarification under the
protocol; proof hints and library repairs are not available during the trial.
