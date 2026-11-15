# FDSA-XW01 accumulated-work draft: author-side preflight

Recorded 2026-11-02. **Read-only author-side semantic preflight of the
specified source snapshots; no final Standards/Spec approval, finding
closure, compiler validation, or acceptance.**

## Scope and exact inspected snapshots

Root held the assigned main example, research document and core stable
for this pass. The hashes below were independently read at the beginning
and end and match root's final snapshot message.

| File | SHA-256 |
|---|---|
| conaled-accumulated-work/Examples/AccumulatedWork.lean | 7ef773d2ce87ce1b119838e083ee4a4cff072f5d96f4a8887f8494a80d04c20c |
| conaled-accumulated-work/docs/research/fdsa-accumulated-work.md | 191a7c449f936b84c17f3f5d33a935dd4440a199fc7287e576dfd38f4fbaca8e |
| conaled-accumulated-work/Applications/Probability/AccumulatedWork.lean | 7731f8a6c5222810ba11a056fc620c68a152dce0024ff3e2544d17fff70a80ba |
| fdsa-control/reviews/accumulated-work-requirements.md | 85c651891cf8c8ee016706bf8baad7711dbd9965eb20ad5c6e96d2ab112728e1 |

Supporting preparation was read at these pins:

| Record | SHA-256 |
|---|---|
| probability-source-preflight.md | 4efb4e40a06be65705a5b9a020a24faff04f9acef313f630fed261e39182158c |
| probability-api-preflight.md | eacc4181f3cb9e49598521be8149c65fab306a5c288ddd04e5bfeff6cccfe396 |
| probability-work-calculations.json | 5eae4c4c905978d1866d9a950971cd0591c54471ad5e67282aabf2f725e4a600 |

The existing Resources.Measured and Resources.Workload definitions were
read to confirm the actual sequencing/value/observation boundary.
AGENTS.md and architectural-quality guidance were read. This is an
assigned preparation step within the parent's retained workflow, not a
new implementation or independent-review loop.

**Excluded:** Examples/AccumulatedWorkBoundary.lean, including its source
contents and hash. Although the main example imports it and root later
reported it complete, root explicitly retained that exclusion. The
documentation's boundary descriptions were compared with the frozen
requirements; their implementation was not inspected in this pass.
This record therefore does not cover the full import closure.

No compiler, project hash helper, integrity checker, Git, cache mutation,
or source edit was performed. Ordinary read-only file digests identify
the inspected bytes. This requested research record is the only file
created by this task.

## Result

**No source-level semantic or scope finding was identified within this
bounded pass.** The examples have the intended actual measured-program
connections, independent expected values, positive-shift and nonempty-tail
uses, and explicit shared randomness. Their principal upper bounds
invoke the public generic results.

This conclusion is not evidence that the proof scripts elaborate. It
does not close any existing finding, approve the core independently, or
replace the pinned-environment focused/full checks, proof audit, retained
review axes or final candidate verification.

## 1. Actual measured computation and returned value

Resources.run executes the head transition through Resources.bind, then
passes its returned state to the remaining transitions. Measured.bind
adds the first observation to the second, while pure contributes zero.
The example uses this existing executor on stages [0,1,2,3].

At a stage whose charge is1, step prepends that stage index and charges1.
Otherwise it returns the unchanged state through pure. The separate
charge_le_one fact ensures the inactive branch's charge really is0;
step_cost records the actual branch observation.

The intended outputs and costs are consistent with that execution:

| Environment | Returned value | Actual cost |
|---|---|---:|
| 0 | [3,2,1,0] | 4 |
| 1 | [2,1,0] | 3 |
| 2,3 | [1,0] | 2 |
| 4,5,6,7 | [0] | 1 |

program_value specifies the complete ordered list independently of a
cost bound. The reverse index order is correct because stages execute
in increasing order and prepend their indices.

observation casts the per-stage natural charge to ENNReal and gives
zero after the fourth stage. accumulated_eq_cost first reduces the
actual countable sum to that finite support, then connects it to
the measured program's cost. This is a source-level execution/observation
bridge, not a definition that assigns a desired sum to an unrelated
extensional program.

The model deliberately leaves condition tests and environment selection
uncharged. Both source comments and the research document identify
that boundary. No physical runtime or algorithm-specific source tariff
is inferred from this example.

## 2. Fin8 law, exact means and public theorem connections

The example uses one standard uniform measure on Fin8 and has a local
probability-measure instance. All four observations are functions of
that same environment. Their means are:

\[
1,\quad 1/2,\quad 1/4,\quad 1/8,
\]

with zero thereafter. Thus the actual initial mean is1 and integrated
drift holds with q=1/2. The stage cap is1 at every environment.
No independent-stage law is assumed.

The direct arithmetic agrees with the saved independent calculations:

\[
\mathbb E W=(4+3+2+2+1+1+1+1)/8=15/8.
\]

The example does not stop at this exact enumeration:

| Example declaration | Public generic result used | Operational connection |
|---|---|---|
| expected_cost_le | lintegral_tsum_le | accumulated_eq_cost transfers the generic total-sum bound to program's measured cost, yielding at most2. |
| expected_cost_finite | lintegral_tsum_lt_top | The same actual-cost bridge, q<1 and finite N yield a finite integral. |
| expected_remaining_le | lintegral_tsum_shift_le at w=1 | Directly bounds the positive-shift sum by1. |
| tail_le | measure_tsum_ge_le_of_stage_le at w=1 | The actual total-cost equality and stage cap identify the threshold3 event and bound its mass by1/2. |

The main example uses the stage-cap corollary rather than the weaker
single-prefix theorem directly. The stable core retains that weaker
public theorem, and its stage-cap corollary invokes it. No unnecessary
all-times cap has been inserted into the weaker public contract.

The private finite-uniform calculation helpers do not establish a
probability law on Fin0. They are finite measure identities; the
normalized example is locally fixed to nonempty Fin8. They introduce
no global inhabitance or finite-payload assumption.

## 3. Shift, natural subtraction and tail event

The first stage always costs1. Removing it leaves per-environment
residual costs

\[
3,2,1,1,0,0,0,0,
\]

whose mean is7/8. remaining_eq_cost connects the shifted countable
sum to natural-number subtraction of1 from the actual cost.
This does not conceal an underflow case: every actual program cost
is at least1, as the first stage and explicit case equation show.
The proof script establishes the equality over all eight environments.

The generic positive-shift bound is

\[
(1/2)^1\cdot1/(1-1/2)=1,
\]

so expected_remaining_le exercises the intended shifted result rather
than merely weakening the separately computed 7/8.

The non-strict threshold3 event is exactly the two environments0 and1,
with mass1/4. At w=1, q=1/2, N=1, the core threshold is

\[
wN+N/(1-q)=1+2=3,
\]

and its right side is1/2. The tail client supplies positivity and
finiteness of N, strict contraction, measurability and the actual
stage cap. The event is nonempty, so this is not a vacuous use.

The documentation preserves the non-strict comparator and the
positive-N requirement. The zero-N counterexample belongs to the
separately owned boundary file; this pass does not claim to verify it.

## 4. Shared randomness is visible

Let A be the event that the environment is below4, and B the event
that it is below2. Then B is contained in A. The example retains:

\[
\mu(A)=1/2,\qquad \mu(B)=1/4,\qquad
\mu(A\cap B)=1/4\ne1/8=\mu(A)\mu(B).
\]

shared_stage_masses and shared_stages_not_independent express this
joint-law distinction directly. The generic accumulated-work theorems
are applied under this same measure. Neither the examples nor the
document replace the shared environment with fresh draws.

Integrated drift here is established from actual finite-law observations.
It is not presented as a proof of a randomized selector's conditional
pivot law or a treap's conditional priority law.

## 5. Affine reweighting and sequencing

affineProgram uses the existing reweight operation to multiply the
completed program observation by2, then bind to an explicit final
charge3 while retaining the returned list. Its source equations give:

\[
\operatorname{value}(affineProgram)=\operatorname{value}(program),
\qquad
\operatorname{cost}(affineProgram)=2W+3.
\]

The exact mean is \(2(15/8)+3=27/4\). The upper-bound proof uses
lower-integral linearity and the generic-derived expected_cost_le,
giving \(2\cdot2+3=7\). It does not obtain the bound solely from
the independent exact arithmetic. The local probability normalization
correctly makes the integral of the final constant equal to3.

The threshold9 event is exactly the original threshold3 event:
\(9\le2W+3\) iff \(3\le W\) for these actual natural costs.
The exact mass1/4 and generic-derived bound1/2 therefore transfer
through an explicit event equality. No new generic expectation or
resource framework is introduced by the affine example.

## 6. Public-statement and source-scope limits

The stable core statements, as used by these examples, match the frozen
scope:

- One common arbitrary measure and ordinary ENNReal-valued observations.
- Geometric mean induction from integrated one-step drift, without
  unnecessary measurability or finiteness hypotheses for that induction.
- Almost-everywhere measurability for interchange with the actual
  countable sum.
- Strict contraction and finite initial bound for finite integral,
  retaining zero q and zero N where appropriate.
- A single almost-everywhere prefix cap, positive finite N and q<1
  for the non-strict tail, with a separate stage-cap corollary.

The source-level tail proof retains finite-prefix cancellation and
positive finite Markov threshold hypotheses. The core and document
do not normalize an arbitrary measure or import finite sample-space,
independence, Countable or Inhabited assumptions into these statements.

The research document correctly distinguishes a nonnegative integral
from a normalized probability expectation, and finite accumulated
work from finite-step termination. It avoids converting infinite
work through a totalized real observation.

The source obligations remain separate:

- Selection still needs its actual uniform occurrence law conditional
  on history, duplicate-aware rank dispatch, size drift, observed-work
  bridge and any affine tariff conversion.
- Quicksort still needs both branches, its distinct-key distribution
  hypotheses and actual cost/harmonic correspondence.
- Treaps still need the common priority ranking and the conditional
  cluster/weighted-charging proof.

The current record does not certify any of those algorithms. The
documentation labels this implementation uncompiled and retains all
validation/independent-review gates. Its descriptions of the excluded
boundary clients are consistent with the frozen requested statements,
but their code remains outside this preflight.

## Handoff

No requested change is raised by this bounded source inspection.
All three assigned source hashes match the parent's declared final
snapshots. Root retains review of the completed boundary file and
the eventual immutable-candidate integration/validation process.
This record supplies no acceptance or finding-closure credit.
