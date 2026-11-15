# Dependent operation scaling trial protocol

This is the proposed freeze for #358. **No author may start until independent
Standards and Spec review approve the exact candidate and the coordinator
records both approvals, public input hashes and successful setup checks.**
Preparation is not a completed author trial.

## Question and arms

Can named local-contract helpers reduce the marginal work of adding dependent
operations, realizations and interactions, compared with reusable native proofs?
The mathematical outcomes are identical. The bounded language has genuinely
indexed terms and typed substitution, but is not the full reference dependent
calculus or the missing quantified Myers source interpretation from #366.

The native arm receives the transitive source closure of
`Examples.DependentOperationTrialSpec` and
`SquareKit.DependentOperation.SelectorBase`. It may reuse, generalize or replace
native helpers, and use the underlying indexed rule library already imported
by Syntax. It is not required to repeat induction for each concrete program.
The shared arm additionally receives the closure of
`SquareKit.DependentOperation.Lowering`, including the local-contract helpers.
Neither receives a solution to the held-out task. Differences in prepared
support are treatment differences and must be counted, not attributed entirely
to the generic theorem. Both may choose a different representation if they
preserve every required outcome; record that choice and its setup cost.

Use two fresh agents, one per arm, with no conversation fork. Neither may have
prepared these fixtures, reviewed the held-out tasks, or seen another submission.
Record prior project exposure, model/reasoning settings actually available, and
unavailable telemetry explicitly. Prior conaled experience is not automatically
exclusionary, but task/solution exposure is. Fixture authors and freeze reviewers
are not eligible. If eligible agents cannot be allocated, retain the freeze and
report the blocked trial rather than substituting designers.

## Frozen cumulative workload

Both authors receive the full task initially. Stages are sequential and
submissions are cumulative; anticipation of later stages is possible and must
be disclosed when interpreting marginal costs. Do not change tasks after
exposure. The independent Spec fixes the arithmetic oracles.

| Stage | Maximum displayed client depth | New primitive count | Executable realizations required | Interaction work |
|---|---:|---:|---:|---|
| A | 1 | 1: rotation | 1: total/position | Identity/empty term and rotation wraparound |
| B | 4 | 2: rotation, halving | 2: add left/right distances | Rotation versus halving, with a rejected commuting claim |
| C | 9 | 3: add bound compression | 3: add unary left/right lists | Mix new operations with old insertion, reflection and padding; two typed substitutions and selected dependent tail |

Each stage requires universal preservation for its admitted operations, not
only the displayed depth. Thus finite size measurements exercise checking and
specialization costs; they do not prove an asymptotic authoring advantage.
Primitive admission, realization count and interactions change together in
this cumulative design. This trial cannot estimate separate causal effects
for those dimensions. Record each count and obligation category rather than
claiming a depth-only comparison.

After C, perform the fixed repair: replace clockwise rotation by counterclockwise
rotation in the specification and every admitted realization. Keep the same
source constructor and update the necessary local law, observations and failed
interaction control. Preserve the original submissions and their acceptance
results. The stage A selected answer changes from 4 to 2. Do not demand a false
old answer or silently reinterpret the repair as a code optimization.

## Budgets, checkpoints and stopping

Per arm: A has 20 active minutes or 15 archived Lean attempts; B has 20 minutes
or 15 attempts; C has 35 minutes or 25 attempts; repair has 15 minutes or
10 attempts. Stop each stage at its first cap, retaining all incomplete work.
A correct checkpoint may proceed early. A failed stage may proceed using its
own incomplete submission, but receives no coordinator proof repair. Total
maximum is 90 active minutes and 65 archived checks per arm. Reading, editing,
proof inspection, diagnostics and reporting count. Explicit build-lock waiting
and externally imposed thermal suspension are recorded separately and excluded
from active time for both arms; wall time remains recorded.

Use a fresh `attempts/AttemptNN.lean` for every check, including inspection and
final submission, through the existing
`experiments/dependent-author-trial/check_attempt.py`. Every attempt is a
self-contained cumulative source snapshot; preserve exact bytes and diagnostics.
Authors report stage boundary, completed declarations, pending obligations,
assistance and stop reason. Do not credit a later-stage repair to an earlier
checkpoint. Coordinator replay and independent statement review determine
correctness; passing Lean alone does not.

Environment help is allowed and logged. A substantive clarification must be
sent identically to both arms and recorded; a change to mathematical scope
invalidates the run and requires a new freeze/new unexposed authors. No proof
hints, library repairs, task tuning, internet research, external agents or
inspection outside the frozen handoff during measured work. Local Mathlib and
Lean are available through the copied pinned dependencies.

## Isolation, measurement and evidence

Reuse the existing incremental-authoring preparation, freeze, environment-index
and smoke utilities with the entrypoints above. Export only the allowed closure,
private project outputs and private pinned dependency files. Do not copy project
Git history, integration reports or coordinator solutions. Add this protocol,
`task.md`, the arm-specific access note and the independent Spec before final
public manifest freezing. Run both success and deliberate-failure wrapper smoke
checks on both handoffs before exposure; retain their receipts as setup costs.
The access contract is not an operating-system security sandbox.

Record candidate SHA, all public hashes, dependencies/compiler, dispatch and
checkpoint timestamps, available author configuration, exact attempts, commands,
exit codes, diagnostics, replay and independent statement findings. Record
wrapper checking time and observed peak memory when a host process-resource
wrapper is available. Otherwise mark memory unavailable. Never infer zero cost
from unavailable telemetry. Thermal or load contention, retries and assistance
must remain visible. Serialize Lean processes with the orchestration build lock.

Account separately for fixture/framework design, previous library work,
closure preparation, setup validation, review fixes, author stage work and
post-trial replay/integration. Setup effort predating instrumented clocks is
unknown, with commands/changes still preserved. Per stage report new or changed
local laws, structural/global proofs, quotation/typing/substitution adapters,
interaction laws, representations, source bytes, diagnostics, checking time and
active/wall time. Count changed old declarations in the repair. Do not use line
count as a proxy for mathematical quality.

A run with zero shared advantage, incomplete arms, or an alternative winning is
a valid empirical result. Three cumulative points and one author per arm cannot
establish asymptotic growth, broad agent productivity, or human productivity.
#107 remains paused, #108 unselected, and #260 inactive.
