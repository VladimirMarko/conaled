# Incremental dependent authoring protocol (#357)

## Chronology and question

Task design began at 2026-11-08 07:47:23 UTC, after both required interfaces passed
independent Standards and Spec review: #355 at 1ff031ca983d02906c26b57af2424c694b6e5a58
and #356 at 7b5c27c6c607201928d14975611b2e26d450293d. Those exact commits fix the
starting interfaces. The integration branch had incorporated both before setup.
No author has been exposed at this protocol's drafting stage.

The trial measures incremental work for a new arbitrary-schedule client family,
using native interfaces versus #356's compositional route. It does not benchmark
all of #355 or every dependent theory. `tasks/common.md` and the independent
Spec module freeze the common outcome. No complete route solution is prepared.
The mathematical feasibility assessment is by inspection of existing typing,
translation, executable and substitution operations; authors may still encounter
unanticipated interface gaps. A failed attempt cannot change the task after
exposure. Public old trials are calibration/history, not new observations.

## Public inputs and author separation

Setup builds separate minimal source closures. Baseline inputs come from 1ff031c;
candidate inputs come from 7b5c27c. Both contain the same independent Spec and task.
Full hashes, entry modules, compiler/dependency identities and handoff manifests
are saved under setup/freeze. Only the candidate receives #356's new helpers.
This difference includes both generic laws and client-specific support; results
cannot attribute effort differences solely to the generic theorem.

Each handoff has independent project outputs, private dependency copies, no
original Git history, no other-arm submission and no private task solution.
Authors are fresh agents with fork_turns=none and no model/reasoning overrides.
The protocol designers/setup helper are not measured authors. Authors may read
only their public handoff and its dependency/toolchain sources. No subagents,
external searches, other machine project paths, Git object searches, other-arm
communication or inspection of submissions are allowed. These are instruction
and inventory controls, not operating-system isolation.

## Budget, assistance and stopping

Each author has 30 minutes from dispatch or 30 archived wrapper attempts, whichever
comes first. Reading, editing, diagnostics and writing the outcome count toward
the wall-clock budget. No token budget is inferred. Stop earlier at a complete
submission or a documented obstruction after attempted remedies. The coordinator
sends time notices and stops work at the deadline. The last pre-deadline snapshot
is the measured submission; late work, if any, is separately attributed and
cannot convert a measured failure into success. Do not weaken requirements to
finish within the cap.

Every Lean command, including inspection with #check, goes through the unchanged
`check_attempt.py` under a fresh attempts/AttemptNN.lean filename. A final
submission is another named snapshot within the same cap. The wrapper records
source bytes, hashes, timestamps, commands, raw diagnostics and exits; it does
not itself decide mathematical acceptance. Authors maintain activity/outcome
records under attempts/, including consulted public files, every failed approach,
assistance, interruptions and stopping reason. No direct Lean/Lake proof checks
outside the wrapper are permitted during measured work.

Environment-only assistance and contract clarifications may be requested from
root. Shared clarifications go to both authors and are archived with timestamps.
No proof hints, missing lemmas, repaired implementations or interface changes are
provided during measured work. A frozen-interface defect is an observed outcome.
For an external outage, suspend both arms, record interruption intervals and
resume only the remaining budget; disclose imperfect matching. Final coordinator
replay and full build/audit are outside author time and recorded separately.

## Metrics and acceptance

Primary: correctness/coverage of each common requirement, retained selected
values, and exact replay of the submitted artifact. Compare effort only after
these outcomes. Secondary: dispatch-to-stop wall time, archived check count,
failed checks and diagnostic classes, local boundary/typing/semantic/quotation
obligations, repairs and assistance. Archive every submitted attempt and final
artifact byte-for-byte. Report source size only as a supplementary count.
Do not invent unavailable token, backend-model or sampling telemetry.

Record preparation separately: protocol and Spec work, handoff/cache creation,
wrapper smoke checks, review/repair, and post-submission evaluation. The earlier
#351–#356 framework-development effort was not instrumented by this trial; it is
not counted as zero or folded into author speed. State this limitation alongside
interface/support source counts. The same host and concurrent checks introduce
resource contention; this is a two-author bounded observation, not a controlled
causal estimate or a human-productivity result.

Before dispatch, freeze the exact task, protocol, Spec, route inputs, wrapper,
prompts and manifests. Independent Standards/Spec assessment must confirm that
freeze and matching acceptance; root records approval of the concrete snapshot.
After authors stop, independently replay submissions and review their elaborated
statements against every item, preserving failures. Successful submitted sources
are integrated unchanged with normal examples and exhaustive audit; failed or
partial files remain clearly labeled experiment evidence outside public imports.
No coordinator repair is credited to an author. Final issue review covers the
full evidence and assessment in addition to the pre-dispatch protocol review.

#107 remains paused, #108 unselected and unprepared, #260 inactive. No master
merge, push, broad migration, reflection claim or general productivity advantage
follows from this trial.
