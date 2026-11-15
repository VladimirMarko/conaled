# Chapter 2 direct random-pivot implementation handoff

Prepared 2026-11-04. **Original pre-code preparation, retained below.** See the
implementation update at the end for the now-committed, uncompiled source.
During the original preparation, no candidate source was
edited, no Lean/Lake/check/audit process was started, and no Git reference or
dependency cache was changed by this preparation. The accompanying
[identity note](../provenance/chapter02-random-pivot-plan-20261104/identity.json)
records exact source objects and locally inspected dependency files.

## Authority, exact base, and scope

The accepted book/review base remains
07e480f6ec9958d4975bb90151005b84f2907614. The foundation candidate
f17cc6b1a2bf44215b16202ed0fcee2b5c130761 remains pending its full gate; its
presence in a development ancestry supplies source access, not acceptance.
The complete frozen Chapter 2 requirements and all **112** current obligations
remain in force. This work implements the fresh-pivot half of C02-024 and its
execution/resource prerequisites. The distinct uniform-input first-pivot
mean, the rest of Chapter 2, and subsequent chapters are still required.

The inspected deterministic source object was
e4c152e62271725abe6e71ac52e4756316208b24, whose parent is
fdd4d4796fe8201cecfa8a53930a391b6e50f401. Its resource file accidentally ended
with two consecutive namespace terminators. Root subsequently supplied
6122dd02c0a5b7ab4435e442e27d641e763f58f5, changing exactly that one redundant
line and no other source. The exact diff and
[repair record](../provenance/chapter02-quicksort-cost-namespace-repair-20261104/result.json)
were read. The corrected deterministic source is **still uncompiled** at this
handoff; this preparation does not certify its proofs.

Root created the clean author worktree conaled-ch02-random-pivot on
work/fdsa-ch02-random-pivot at that corrected object. Its
[start identity](../provenance/chapter02-random-pivot-start-20261104/identity.json)
is separate from this preparation. **Wait for root's saved/exposed pre-code
checkpoint and explicit code release before editing it.** Any later dependency
correction must receive a new exact identity; do not silently follow a moving
branch or incorporate unrelated shared drafts.

This handoff applies the repository implementation, implementation-spec,
example-driven, architectural, proof-boundary, and review-loop instructions
within the already assigned Chapter 2 loop. It creates no new ticket or review
round. See the [frozen requirements](chapter02-requirements.md),
[112-obligation ledger](../research/chapter02-obligations.md),
[average proof plan](../research/quicksort-average-proof-plan.md),
[API preflight](../research/random-pivot-api-preflight.md), and the
[probability dependency handoff](../research/chapter02-probability-dependency-handoff-20261104.md).

## Minimum files and dependencies

The first implementation slice needs exactly two new Lean files:

| File | Responsibility |
| --- | --- |
| Applications/Resources/RandomQuickSort.lean | Positive uniform occurrence index, actual recursive measured PMF, public unfolding/support/value laws, occurrence and cost-support bounds, observed natural cost laws. |
| Examples/RandomQuickSort.lean | Independent finite mass calculations and polymorphic correctness/cost clients, including duplicates, empty payload carrier, and append association. |

No change to an existing algorithm, the probability kernel, or the cost
framework is necessary. The project dependency is
Applications.Resources.QuickSort, reusing its exact actual append assembly and
partition-length law and, transitively, the pending foundation's ListCalls.
Use Mathlib.Probability.ProbabilityMassFunction.Constructions for PMF
operations, with direct List/ENNReal/finite-sum imports only where needed.
Avoid a broad Mathlib import. No XW01 or XU01–06 dependency is needed by this
direct random program. Uniform-input work retains its separately documented
XU01 historical acceptance chain and XU02/XU03 mathematical dependencies.

The operation should retain the deterministic source's pair observation:

    run : (α → α → Bool) → List α →
      PMF (Resources.Measured (List α) (Nat × Nat))

The first coordinate is Exercise 2.4; the second is the additional count of
both source appends. This specializes the earlier preflight's scalar proposal
by projecting the first coordinate; it neither changes that tariff nor imposes
a new payload assumption. Define the actually needed public projected laws
as PMF.map of the exercise coordinate and the sum of the two coordinates,
both landing in Nat. Other projections can be written directly by clients.
There is no need for a new probability abstraction, record hierarchy, trace
language, or global sampler.

The complete-candidate integration step must add both new modules to the
existing SquareApplications.lean import closure, together with all other
source modules present in that candidate. Focused source preparation does not
meet this gate. Preserve exact Lean/Lake 4.35.0, the nine dependency pins, and
the qualified native launcher profile. Nix alone is waived.

## Exact locally inspected APIs

The source tree inspected is conaled-ch02-top-down/.lake/packages/mathlib at
56a005855ea17e0b0958f73ec801ae140b0a1679. The official Lean source is the
qualified lean-4.35.0-linux tree. These are source observations, not fresh
elaborated-type checks. Proposed declarations below remain proof targets.

| Pinned API | Consequence for implementation |
| --- | --- |
| PMF.ofFintype (f : ι → ENNReal) (h : ∑ i, f i = 1), Constructions.lean | Construct a uniform PMF on Fin (m+1) explicitly. Only that finite index type needs Fintype. |
| PMF.ofFintype_apply (h) (i); PMF.mem_support_ofFintype_iff (h) (i) | The weight function is implicit in these lemmas. Uniform positive weights give support equal to all valid indices. |
| ENNReal.mul_inv_cancel (h0) (ht), Basic/ENNReal/Inv.lean; ENNReal.natCast_ne_top, Basic/ENNReal/Basic.lean | Normalize the constant inverse positive natural weight. These canonical module paths replace deprecated Data/ENNReal shims. |
| PMF.bind; bind_apply; mem_support_bind_iff, Monad.lean | Explicit heterogeneous binds support an index in Type and a payload in Type u. Branch support is an existential over actual supported children. |
| PMF.map (f) (p); mem_support_map_iff; map_bind; bind_map; map_comp; pure_map, Constructions.lean | Project the actual run; avoid a hidden homogeneous-monad universe restriction. |
| PMF.map_ofFintype | Requires finite source and finite target. Suitable for a Bool or Fin rank event, not arbitrary list/payload output. |
| List.length_eraseIdx_add_one (h), Mathlib/Data/List/Basic.lean | Exact one-occurrence deletion supplies strict decrease. |
| List.getElem_cons_eraseIdx_perm (h), Mathlib/Data/List/Perm/Basic.lean | The selected occurrence cons the indexed remainder is a permutation of the original list, without payload equality. |
| List.eraseIdx_sublist, Init/Data/List/Erase.lean | Child membership and inherited hypotheses follow from the actual remainder. |
| List.length_filter_le (p) (xs), Init/Data/List/Lemmas.lean | Each filtered remainder is strictly shorter than the original nonempty input. |
| Resources.ListCalls.filterRun_value and filterRun_cost_of_constant | The real unit-callback filter run returns the filter and has count 2m+1. The deterministic private unit_filter_exact is not importable; use these public laws directly. |
| Resources.QuickSort.appendPivotRun_exact | The two measured right-associated appends return left ++ ([pivot] ++ right) with additional count length(left)+3. |
| Resources.QuickSort.partition_lengths | Complementary filters preserve the total occurrence length for any Bool predicate, including duplicates. |

The misleading name PMF.uniformOfFintype is, at this exact pin, a deprecated
alias for MeasureTheory.Measure.uniformOfFinset. Its old-looking name does
not make it a PMF constructor; do not use it here. The operation is a
noncomputable probability denotation. It is not an implemented random-bit
generator.

## Actual operation and source unfolding

Define uniformIndex (m : Nat) : PMF (Fin (m+1)) with constant mass
((m+1 : ENNReal)⁻¹). Prove normalization, its point mass, full support, and
the Bool-event counting law for a supplied predicate on indices. Keep any
auxiliary normalization proof private. There is no distribution on Fin 0
and no default pivot.

The empty run is exactly PMF.pure ([], (1,0)), even for α = Empty. At a
nonempty input ys = head :: tail, bind uniformIndex tail.length. For the
chosen valid index i, read ys[i.val] and form ys.eraseIdx i.val. These are
occurrence operations. Do not use equality-based List.erase, deduplicate the
input, choose from its key set, or reduce the pivot law to the original head.

Within that branch, retain the deterministic source's execution order and
operations:

1. Execute the first actual ListCalls.filterRun on the indexed remainder,
   with callback x ↦ (lt x pivot, 1).
2. PMF.bind the recursive random run on that filter's returned list.
3. Execute the second actual filterRun on the same remainder, with callback
   x ↦ (!(lt x pivot), 1).
4. PMF.bind the recursive random run on that returned list.
5. Execute appendPivotRun on the two recursively returned values and pivot,
   then return that value and the sum of the observations using PMF.pure.

The returned pair is exactly the deterministic source's assembly rule:

    (assembled.1,
      (leftInput.2 + left.2.1 + rightInput.2 + right.2.1 + 1,
       left.2.2 + right.2.2 + assembled.2))

The recursive occurrence-index choice is inside run, so every nonempty child
call makes a fresh conditional uniform choice on its actual current input.
Do not reuse one root index or silently resample a shuffled input. Explicit
PMF.bind separates probability sequencing from Resources.bind used by the
actual measured append helper.

Use input length as the well-founded measure. For each branch, the indexed
remainder has length one less than the original, and both returned filter
lists have at most that length. Establish these inequalities from the public
filter value and indexed-removal lemmas. No fuel bound, partial definition,
unsafe implementation, nontermination assumption, or payload instance is
needed. Address any Lean attachment/unattachment elaboration detail with an
ordinary proof; do not change the algorithm to satisfy a termination tactic.

Export an unfolding equality for this actual PMF. After the actual filter and
append equalities, a branch with remainder length m returns:

    (left.1 ++ ([pivot] ++ right.1),
      (left.2.1 + right.2.1 + 4*m + 3,
       left.2.2 + right.2.2 + left.1.length + 3))

This is a consequence of the operation, not a separate recurrence used as the
definition of random cost. The key specialization must identify the Bool
complement with pivotKey ≤ xKey under LinearOrder κ and retain strict left
and nonstrict right. A separate three-way sort does not discharge this work.

## First slice: proof contracts and order

Use explicit universes u and v for payload and key types. Keep arbitrary α
without Fintype, DecidableEq, BEq, Inhabited, order, or MeasurableSpace instances.
The following are declaration shapes, not assertions of existing theorems.

**Occurrence law and support decomposition.** Prove the chosen index has
mass 1/(m+1), and prove a supported nonempty result exists exactly when some
valid index and supported left/right recursive results assemble to it by the
preceding equation. All valid indices are in support. The child distributions
in this theorem are the actual recursive calls on the selected indexed
remainder; an arbitrary supplied PMF or assumed coupling would be circular.

**Permutation and length.** For every comparator and actual supported result:

    r ∈ (run lt xs).support → r.1.Perm xs
    r ∈ (run lt xs).support → r.1.length = xs.length

Prove permutation by support decomposition, child induction, complementary
filter partition, and getElem_cons_eraseIdx_perm. Derive length from that
permutation. Do not replace random output by the deterministic head-pivot
output: equal-key tagged values can appear in different orders.

**Raw correctness at the necessary assumptions.** Mirror the existing value
API: a transitive key relation and comparator compatibility only on members
of this input suffice for sortedness of each supported output. Export the
LinearOrder key specialization as sortedness and permutation on support:

    r ∈ (run (fun a b => decide (key a < key b)) xs).support →
      KeySorted key r.1 ∧ r.1.Perm xs

Use eraseIdx_sublist and filter membership to inherit input-local assumptions
and the child permutation laws to establish the cross-pivot inequalities.
Do not promise stability. This proof is about raw supported values, with no
measurability restriction on α.

**Deterministic bounds for every random branch.** Let n = xs.length,
T = r.2.1, A = r.2.2, and F = T+A. Prove, for every r in actual run support:

    T ≤ 2*n^2 + 2*n + 1
    3*n ≤ A
    2*A ≤ n^2 + 5*n
    A ≤ T
    T ≤ F ∧ F ≤ 2*T
    2*F ≤ 5*n^2 + 9*n + 2

These are support inductions for the actual random program. The existing
deterministic first-pivot inequalities cannot simply be applied to random
branches; an execution-preserving transport theorem would first be needed.
Direct induction is smaller here. At an actual nonempty branch set a and b
to the child lengths, so a+b=m=n−1. The exercise bound's polynomial slack is
4ab. The append upper bound's slack is 2b(a+1), and its lower bound follows
from the extra a in the local charge a+3. The local inequality a+3≤4m+3
and child hypotheses give A≤T; the empty branch has T=1,A=0. The other two
bridges follow by addition. These bounds require no order law or distinctness.

Prove cost-law support is contained in the corresponding finite interval
after mapping the actual run to Nat. This is sufficient for the next
expectation step; finite payload types or a separate global enumeration of
all payload-valued executions are unnecessary.

**Duplicate boundary on the actual random execution.** If all keys in xs
equal one key c, every pivot sends the entire remainder right. Prove the
joint cost projection is the point mass at
(2*n^2+2*n+1, 3*n), even when the payload records are different. Its value
projection need not be a point mass. The replicate family is a useful
specialization. This supplies a genuine all-size counterboundary to any
unqualified distinct-key mean claim.

The first slice is complete only after these source-connected laws and the
examples below are checked. It still does not prove C02-024's expectation or
its asymptotic claim.

## Independent consequential cases fixed before code

The examples must apply public operation/support theorems and compute masses
of the actual PMF. Do not define a separate small numerical distribution and
merely prove its arithmetic.

| Case | Required independently fixed observation |
| --- | --- |
| Empty input with α = Empty | The run is pure ([],(1,0)); no Inhabited assumption can be hidden in pivot access. |
| Singleton with arbitrary α : Type u | The run is pure ([x],(5,3)); append-inclusive body count is 8. |
| Uniform pivot occurrence in [a,a,b] with distinguishable a/b tags | The Bool event “selected occurrence is an a” has mass 2/3, not 1/2. Use index/event mapping, not a deduplicated value sampler. |
| Two distinct natural keys | Exercise count is always 13. Append cost is 6 or 7 with mass 1/2 each; this checks actual random pivot and association. |
| Three distinct natural keys [0,1,2] | Exercise-law mass is 1/3 at 21 and 2/3 at 25, zero elsewhere; exact mean target is 71/3. |
| The same three-key joint law | Mass 1/3 at (21,10); mass 1/6 at each of (25,9), (25,10), (25,11), (25,12); no other cost pair. This is an optional stronger finite client if it materially simplifies the projected-law proof. |
| Three equal keys | Exercise/append counts are always (25,9), so append-inclusive body count is 34. |
| Arbitrary many equal keys, possibly tagged payloads | Joint cost is always (2*n^2+2*n+1,3*n). This is a universal theorem, not only the size-three example. |
| Two distinct tags with equal key | Selecting the second occurrence first produces the reversed tag order with mass 1/2. State a concrete key/tag instance; the general algorithm must not acquire payload equality. |
| Arbitrary-universe key/payload client | Supported values are sorted by key and permute the actual input without an order, equality or measurable-space instance on payloads. |

The three-key masses follow independently by splitting on pivot rank. A
middle pivot gives two singleton children and T=21. Either extreme gives a
size-two child and T=25. Each root rank has mass 1/3. For the joint refinement,
the two child pivot ranks have masses 1/2 and give the four listed append
counts. The pre-existing handoff fixes these exercise results; they are not
adjustable to make an implementation pass.

Keep the actual append witness too: left=[0,1], pivot=2, right=[3] costs 5 in
appendPivotRun. Left-associating the two equal-valued appends costs 7. Value
associativity proves no observation equality.

## Next mandatory slice: actual expectation, rank, harmonic bound

The following work is explicitly pending after the first slice. It is not
optional merely because the run and its support bounds compile.

1. **Define an actual finite mean.** Map run to its exercise-cost PMF on Nat
   and use that law's toMeasure. On Nat all relevant sets/functions are
   measurable. Derive the almost-everywhere polynomial support bound, a
   finite lower integral, and real integrability. Do not install a
   measurable-space structure on payloads. Keep both the standard integral
   and any computational weighted-sum presentation connected by a theorem.

2. **Prove the bind expectation bridge.** For nonnegative ENNReal weights,
   expand bind_apply and use ENNReal.tsum_comm and tsum multiplication laws:

       ∑' b, (PMF.bind p f) b * g b =
         ∑' a, p a * (∑' b, f a b * g b)

   This lemma may remain private in the client until a second real use
   warrants moving it. The map version follows through bind/pure. Apply it
   to the actual nested children and their additive observations.
   Normalization and linearity suffice; an unproved independence or global
   priority coupling must not appear as an extra premise.

3. **Prove occurrence rank correspondence.** Under (xs.map key).Nodup,
   map each valid pivot occurrence to the number of strictly smaller keys.
   Prove this is a bijection on Fin n, identify the actual left length with
   that rank and right length with n−1−rank, and prove inherited distinctness
   of both child key lists. Existing Selection.Rank interfaces may help with
   an ordered-list witness, but they do not already establish this bijection
   or the random pivot law. A direct finite-index counting proof is equally
   acceptable. Key distinctness, not payload distinctness, is essential.

4. **Derive the mean from actual execution.** First prove the occurrence
   average over the actual child means and local toll. Then use strong
   induction on input length and the rank bijection to obtain a size-only
   sequence A and the source recurrence:

       A₀ = 1
       Aₙ = (2/n) * ∑ (k < n), Aₖ + 4*n − 1    (n > 0)

   The theorem must identify meanExercise key xs with A(xs.length) for
   every actual distinct-key input. A separately defined recurrence with no
   execution-to-mean identity does not discharge C02-024.

5. **Solve the recurrence and export the actual bound.** Reuse Mathlib's
   rational harmonic and its cast to Real. The exact target for all n is:

       Aₙ = 8*(n+1)*harmonic n − 12*n + 1

   For positive n the consecutive identity
   n*Aₙ = (n+1)*Aₙ₋₁ + 8*n − 5 supports a short induction; treat the base
   and divisions explicitly. Verify A₀=1,A₁=5,A₂=13,A₃=71/3 before the
   general algebra. The pinned harmonic_le_one_add_log yields, for n≥1,
   Aₙ≤16*n*(1+Real.log n). For n≥2, an explicit constant
   16*(1+1/Real.log 2) then gives an n*Real.log n upper bound. Prove
   nonnegativity and the corresponding standard Asymptotics.IsBigO claim,
   and export its uniform consequence for actual distinct-key inputs.
   The existing Growth helpers take natural-valued counts, so they do not
   directly accept a rational/real expected value; use the same standard
   asymptotic interface directly. Do not replace Real.log by Nat.clog or
   assume the mean is natural. A separate base-change proof supplies log₂
   if desired. Share the numerical algebra with uniform-input work once
   both actual mean clients exist; do not build a general framework first.

6. **Transport only through proved observation bounds.** The pathwise
   append-inclusive body bound F≤2T yields its finite mean and O(n log n)
   upper bound for the same random execution. It does not give the exact
   exercise harmonic formula for F. Selection, occurrence lookup/removal,
   and random-bit work remain outside both recorded coordinates. If an
   explicitly measured selection/removal implementation is claimed, prove
   its linear per-call bound and its whole-run comparison before extending
   the asymptotic claim. Physical runtime or random-bit complexity requires
   its own model; none follows merely from the PMF denotation.

Relevant next-slice pinned APIs were inspected: PMF.toMeasure_apply_singleton,
toMeasure_apply_eq_zero_iff and toMeasure_apply_eq_one_iff;
MeasureTheory.lintegral_countable'; integrable_toReal_of_lintegral_ne_top;
PMF.integral_eq_tsum (which requires integrability);
PMF.integral_eq_sum (finite carrier only); harmonic_zero, harmonic_succ,
log_add_one_le_harmonic and harmonic_le_one_add_log. In particular,
integral_toReal by itself does not establish integrability. Do not exploit
the totalized value of a nonintegrable real integral.

## Release, validation, and review boundary

Source release belongs to root after the promised durability checkpoint.
The new worktree has no writable compiler outputs to share. Root owns the
single focused development builder and the separate foundation full check;
do not start another builder, move caches, or poll another agent's execution
session. Compiler failures require proof/API corrections under the same
mathematical scope, never relaxed statements or tariffs.

Save source identities and independent examples before code, then each exact
implementation successor, focused terminal logs, explicit universe-aware
statement readback, and complete-candidate terminal evidence as they become
available. Keep the accepted review base fixed and preserve all findings.
Ordinary full acceptance must build the complete import closure and run the
exhaustive audit; a focused build is not that result. The preserved native
fresh baseline remains valid; repeat fresh checking only under the actual
README trigger rules. Only the permitted axiom union is allowed.

Independent Standards and Spec assessments must cover the full immutable
candidate and terminal evidence. Immediately verify the exact approved
candidate through the qualified environment before any accepted local
fast-forward. No GitHub mutation or push is authorized. Root updates local
tickets/coverage and checkpoints only to the status actually demonstrated.
This handoff closes no obligation, review finding, or acceptance gate.

## Implementation update: source candidate 080e2f6

After checkpoint 0085 was saved and exposed, root released the initial
two-file implementation. The exact committed source is now
**080e2f63ad4ef56dd18a5889d14dcf8c9100f049**, parent
6122dd02c0a5b7ab4435e442e27d641e763f58f5, on
work/fdsa-ch02-random-pivot. The author worktree is clean. Exactly the two
planned Lean files were added: 503 library lines and 202 example lines.
The [candidate identity](../provenance/chapter02-random-pivot-draft-20261104/candidate.json),
[source statement inventory](../provenance/chapter02-random-pivot-draft-20261104/source-readback.json),
and [static statement assessment](../provenance/chapter02-random-pivot-draft-20261104/statement-assessment.md)
record this boundary. A Statements.lean file is prepared for root's later
explicit universe-aware elaborated readback; it has not been executed.

The source defines the actual pair-valued recursive PMF described above,
including uniform valid occurrence indices, indexed removal, both actual
filterRun operations, recursive PMF binds and appendPivotRun. Its public
unfolding and support decomposition connect the operation to raw permutation,
input-local sortedness, all planned support cost bounds, finite natural cost
support, and the equal-key joint cost law. An additional exerciseLaw_cons
is derived by mapping that same run through the actual cost projection; it
is a distributional equation, not an expectation theorem.

The examples include the mandatory empty/one/two/three-key and duplicate
cases, actual 21/25 masses, actual 6/7 append masses, the 2/3 repeated-occurrence
pivot event, arbitrary payload universes, and a supported equal-key output
that violates stability. The optional three-key full joint-law refinement
was not needed to derive the required exercise law and was not added.
Expected constants and mathematical statements were retained unchanged.

The dependency resource module with SHA-256
e98024f6b741e1aba1fb1e38b419eee2e1acad76a8a40e669752f54775783263
was successfully built in root's focused candidate
8ec1d9cb93e4c38168dc357e8b6f254f8fe83668. This exact resource source is already
in the author base. The closed aggregate attempt had **exit 1** because other
requested modules failed; the source-specific resource pass is not a claim
that the complete attempt passed. Its closed log and result are in
chapter02-measured-sorting-focused-20261104-attempt1. The separate deterministic
example proof-name repair df67f1cc was not merged into this author worktree,
because it is not an API dependency of these two files. Foundation f17 is
still unaccepted by this work.

At that initial handoff, the random-pivot candidate had **not been compiled or audited**. Only
source/statement inspection, source-policy text inspection, unchanged-pin
identity checks, clean committed state, and Git whitespace checks have been
performed here. There is no elaborated type-readback result, full-candidate
verification record, independent final review, or acceptance result.

All finite-mean/integrability, actual bind-expectation, distinct-key rank,
execution-derived mean recurrence, harmonic formula and Big-O obligations
remain mandatory next work. The uniform-input mean and selection/removal
qualifications remain exactly as recorded above; no C02-024 closure is claimed.
No ticket or coverage status was changed. Per root's checkpoint 0086 hold,
the author will make no source, ref, or control writes after this handoff
and identity are complete until root saves/exposes the capture and releases
the next action. Root remains the sole focused compiler coordinator.

## First closed compiler outcome and bounded proof correction

Root's extended focused attempt on immutable central candidate
5d7a479549f5acd64a9e5adb418ab48780c238ef closed with **exit 1** after
290.051 seconds, with the same final HEAD and a clean status. Its complete
17,330-byte log has SHA-256
6ff459c43eade60da3fc4a15edd26da81c71ae5767be9b1a73253f0a29faad76;
the log and native/outer terminal results are preserved under
chapter02-extended-sorting-focused-20261104-attempt1. Both random-pivot
source files there exactly matched source candidate 080e2f6. This attempt
failed to build Applications.Resources.RandomQuickSort. The downstream
Examples.RandomQuickSort entry marked "Ran" is **not** a checked example
module pass.

The complete closed log was read. Root released bounded proof elaboration
corrections, now committed as **254a4162fa6aeeb7ab2a1ceea5139e5772a5865b**,
parent 080e2f63ad4ef56dd18a5889d14dcf8c9100f049. The exact changes are confined
to three existing proof bodies:

- uniformIndex_zero uses Fin extensionality and the valid index bound instead
  of asking typeclass search for Subsingleton (Fin (0+1)).
- uniformIndex_event simplifies the two Boolean cases rather than requiring
  definitional equality between their proposition deciders.
- costs_of_all_false explicitly presents child support in terms of its local
  pivot/remainder definitions before rewriting the empty/full filters, and
  reduces the empty-list length before the existing arithmetic proof.

The recursive call, termination measure and decrease proof remain in place.
The prior unused-termination diagnostic followed the failed recursive proof
elaboration; it was not silenced by removing termination checking. No
definition, theorem statement, hypothesis, example, expected constant, import,
option, or pin was changed. The examples remain byte-for-byte identical.
The corrected resource file has 509 lines; the commit contains only that
file, with eight inserted and two removed proof lines.

The [correction identity](../provenance/chapter02-random-pivot-correction1-20261104/result.json)
and its source.diff/header comparison preserve the actual failed outcome,
source identities, and proof-only boundary. The author worktree is clean.
The successor has not been compiled locally; root owns the next central
attempt. No acceptance or coverage status changed. All expectation, rank,
harmonic/asymptotic, uniform-input and overhead obligations remain pending.
The author is again holding source/ref/control writes for central diagnostics.

## Core focused pass and bounded example correction

After checkpoint 0087 was saved and exposed, root supplied the complete
closed six-target attempt at central candidate
4ac0e7eed2fa41a8844fff8d213b6298e9ad5cf9. The attempt ended with **exit 1**
after 149.949 seconds, preserving its HEAD and clean status. The complete
19,446-byte log, SHA-256
bd000490148fe78ad1f67dfd0f1eb38c05aa9ecd3212ea58ac038e15622947fa,
and terminal records are under chapter02-variants-xd01-focused-20261104-attempt1.

This log establishes an individual focused **pass** for
Applications.Resources.RandomQuickSort (68 seconds), with source SHA-256
c2fcc81b6bd7a4de8b7a9dc476dad62322701609a53b4ea58772f1d9a81307a2.
Examples.RandomQuickSort failed (52 seconds). Its concrete diagnostics were
unused simp arguments and the remaining ENNReal equality
3⁻¹+3⁻¹=2/3. The aggregate also had an unrelated difference-list target
failure; an aggregate pass is not claimed.

The example-only successor is now
**bb4fb243bb7b16ae8bef921fec479a86f2b01c90**, parent
254a4162fa6aeeb7ab2a1ceea5139e5772a5865b. It removes exactly the reported
unused simp arguments and closes the fixed mass equality by rewriting
3⁻¹+3⁻¹ to 2*3⁻¹ with two_mul and 2/3 to the same expression with
div_eq_mul_inv. The applicable pinned algebra source was inspected. No
linter, warning, proof restriction or other option was disabled.

The passing 509-line core is byte-for-byte unchanged. All example statements,
hypotheses, distributions, expected probabilities and constants remain
unchanged; only five example proof bodies differ. The example file now has
203 lines. The exact diff and header/identity comparison are preserved with
the [correction result](../provenance/chapter02-random-pivot-correction2-20261104/result.json).
The author worktree is clean, and no local build or cache write was performed.

The revised examples still require central validation. Neither this focused
core pass nor the correction constitutes a complete candidate check, audit,
independent final review or acceptance. No ticket/coverage status changed.
The complete finite-expectation, actual mean bridge, rank, recurrence,
harmonic/asymptotic, uniform-input and overhead continuation remains mandatory
after the initial pair passes. The author again holds source/ref/control
writes pending the next central result and release.


## Closed initial-pair focused pass and complete author type readback

The exact corrected author source at
**bb4fb243bb7b16ae8bef921fec479a86f2b01c90** was merged into central candidate
**dfaf68114d1dda4e15628c94c3d988c3f5457c49**. Central focused attempt3 retained
**exit 1**: it built the random examples successfully and replayed the resource,
but requested the nonexistent `Applications.Sorting.RandomQuickSort` target.
The complete log/result preserve that command error and its actual outcome.

The corrected four-target attempt4 then closed **exit 0** in 9.201865451
seconds at that same clean, unchanged candidate. Its 4,186-byte log SHA-256 is
514c8e71be97d10be7bb0c181e2dc3605423186b0adbfc085c122f63bee0896a.
Both `Applications.Resources.RandomQuickSort` and `Examples.RandomQuickSort`
now have a complete focused pass. The source hashes remain c2fcc81b6bd7a4de8b7a9dc476dad62322701609a53b4ea58772f1d9a81307a2
and 4f5a21d1656423ac1307b1ca8fe651cd794d70da576ecd14f65d68cc290c424d,
respectively, identical to the author blobs and central working copies.

The joint 134-declaration explicit type inspection closed **exit 0** at the
same candidate in 13.325960255 seconds. This author read all 62 random-pivot
declarations (the complete 1,188-line/87,257-byte section), and every line and
proof of the 509-line resource plus 203-line examples, against that output.
No concrete source/statement mismatch was found. See the complete
[author source/type readback](../provenance/chapter02-xd01-random-types-20261104/random-author-readback.md)
for identities, actual terminal results, full assessment, and preserved prior
failures. This is an author readback, not either independent review axis.

No expectation, real integrability, rank, recurrence, harmonic, asymptotic,
uniform-input or pivot-overhead obligation is closed by this initial pass.
Complete-candidate validation/audit, independent reviews and immediate
verification remain required. The foundation is not accepted by this work.
The bounded expectation preparation remains source-only and is not yet a saved
implementation plan at this update. No source/ref/cache/ticket/coverage write
was made here. The author now holds all source/ref/control writes for root's
checkpoint 0088 capture; read-only preparation may continue.


## Bounded actual-mean source candidate 7b1851c

After the complete initial-pair source/type readback was saved in checkpoint
0088, root read the complete finite-expectation plan with zero design findings
and released exactly the planned two-file implementation. The clean author
branch at bb4fb243 was verified as an ancestor of exact central candidate
0ec9954479b081664bd4504c90fb66fba5fd22c8, then fast-forwarded to that object
without following a moving branch or forcing history. The new
[start identity](../provenance/chapter02-random-expectation-draft-20261104/start.json)
preserves the operation and unchanged source/pin identities.

The coherent new source is committed as
**7b1851cee7fe580a4fe235740b0c07e4ddd8fc58**, parent
0ec9954479b081664bd4504c90fb66fba5fd22c8. Only
Applications/Resources/RandomQuickSortMean.lean (334 lines) and
Examples/RandomQuickSortMean.lean (118 lines) are added. Existing random
execution, laws and examples are byte-for-byte unchanged. The author worktree
is clean and has no `.lake` directory.

The new source defines ordinary real means of the actual Nat laws. Actual
support bounds supply finite lower expectations and genuine real Integrable
contracts. A private ENNReal weighted-bind/map calculation derives the actual
occurrence-average equation, with the selected index, indexed remainder,
actual child filters and local toll 4*tail.length+3 explicit. Finite child
means and finite sums are proved before real transport. No distinct-key,
independence, uniform child-input order or numerical recurrence premise is
introduced. The append-inclusive mean comparison uses weighted maps of the
same run, preserving its coupling.

Connected examples retain actual exercise means 1, 5, 13 and 71/3, actual
literal means 1, 8 and 39/2 for the displayed base/two-distinct-key cases,
and the quadratic constant-key formulas. Distinct equal-key tags have means
13 and 19; three equal keys have means 25 and 34. Both integrability and
mean-comparison clients retain arbitrary payload universes.

Every new source line and proof was read back, and all **32** public
source-level declarations were assessed, along with 15 private helpers. The
[candidate identity](../provenance/chapter02-random-expectation-draft-20261104/candidate.json),
[complete per-claim assessment](../provenance/chapter02-random-expectation-draft-20261104/statement-assessment.md),
and adjacent inventory/diff preserve this boundary. Resource SHA-256 is
41d81697ef917d32f6946b05b7381882838e67e8f4be9408a1b218633cea04d2;
example SHA-256 is
a00248d8ecb10c425c1376e39ceccd77b6a1c468b952ef838f0494624bc26670.
Git whitespace checking passed, but **these new files remain uncompiled**.
There is no new elaborated-type, complete-candidate, audit, independent-review
or acceptance result. The earlier initial-pair passes and prior failures
retain exactly their recorded statuses.

No source/ref/cache/ticket/coverage outside the released scope was changed.
The rank bijection, inherited key distinctness, actual length recurrence,
harmonic/logarithmic/Big-O proofs, separate uniform-input mean and pivot-work
qualifications remain mandatory. All full-candidate and acceptance gates
remain in force. The author now holds all source/ref/control writes for
checkpoint 0089 and root's exclusive subsequent focused validation; no new
source slice starts during capture.


## First actual-mean compiler findings and proof-only successor

The first central focused attempt at
**fff993ec1d041c0a86e7e79a94d13f5be6b92a94** closed **exit 1** after
101.64727630000016 recorder seconds (101.54561406799985 native seconds),
with unchanged clean HEAD. Its two mean source blobs equal the author
7b1851c blobs. The complete 17,412-byte log SHA-256 is
48063b4acf544e1cd977f2ffc039a37024bd01e30bfd42357041d4704de22d84.
The author read the complete closed log and result. RandomQuickSortMean
failed; its downstream example job labelled `Ran` is not a module pass.
Independent PermutationOrder diagnostics are preserved and remain outside
this author's source scope.

Root released bounded proof corrections. The coherent successor is
**19879f244a81b03b7ccaabbcf53fc0b355e9985b**, parent
7b1851cee7fe580a4fe235740b0c07e4ddd8fc58. Exactly five proof lines in the
resource changed: use the pinned `mul_le_mul_right`, parenthesize all three
reported finite-sum bodies, and simplify the observed Nat-cast multiplier
with `ENNReal.toReal_natCast`. All 32 public and 15 private source contracts,
all definitions/hypotheses/imports/options and all example bytes are unchanged.
The actual-source body and genuine integrability requirements are retained.

The resource is 334 lines/16,488 bytes with SHA-256
135af328490993bc48ff9c8a0ccfd847768fca22329292bd2ee0ff4db21662c0.
The unchanged mean-example SHA-256 is
a00248d8ecb10c425c1376e39ceccd77b6a1c468b952ef838f0494624bc26670.
The [complete findings and source assessment](../provenance/chapter02-random-expectation-proof-repair-20261104/findings.md),
[exact identity](../provenance/chapter02-random-expectation-proof-repair-20261104/identity.json),
source diff and contract comparison preserve the full boundary. Git
whitespace checking passed. The author worktree is clean and has no `.lake`.

This successor remains **uncompiled**, with no new focused, elaborated-type,
full-candidate, audit, independent-review or acceptance result. Earlier passes
and failures retain their actual statuses. No builder/cache or other-worktree
write occurred. The actual rank/child-size and size-only recurrence work,
harmonic/logarithmic/Big-O proofs, separate uniform-input claim and pivot-work
qualifications remain mandatory. Source/ref writes are held for root's sole
central check; the authorized rank plan remains preparation only.


## Priority real-cast repair during the next live central check

The mean module in central attempt3 at
b3ccd6617c9a0bd033ab181a77d0e07d4b72100a reported one remaining cast mismatch:
its real upper bound retained the Nat cast of 2. At the supplied observation
the aggregate was still running, so no terminal exit is asserted here. The
complete owned block and the partial-log identity are preserved in
[the cast-repair observation](../provenance/chapter02-random-expectation-cast-repair-20261104/partial-observation.json).
The downstream mean example labelled `Ran` remains unvalidated.

Root's priority correction was committed separately as
**1f315fdbb40288d99921164bb3fd8afcbd756e58**, parent19879f2. The proof now
performs the ENNReal.toReal rewrites first, then applies pinned
Nat.cast_ofNat to the real numeral cast. Only that proof site changed;
all 32 public and 15 private contracts and all example bytes remain unchanged.
The new resource SHA-256 is
2c7976bf52a2dbed2eb6eb959055acc7ae0df8319c167f0128b63e5c482bd5d3
(16,517 bytes, 335 lines). The [repair findings](../provenance/chapter02-random-expectation-cast-repair-20261104/findings.md)
and adjacent identity/diff preserve the exact boundary. This successor is
uncompiled. The worktree is clean and has no .lake; no author build/cache
write occurred. The released rank work paused before any rank source existed
and can resume from this explicitly authorized successor. All mathematical
continuations and acceptance gates remain unchanged.


The cast-repair observation now has appended closed attempt3 evidence:
unchanged clean b3ccd661, exit1,329.7488038879983 recorder seconds. The complete
15,382-byte log SHA-256 is
27fffd453a4650aa56976d4cfac2b482fccaae82a8f1ba53bfe38fb5780108ca.
See [closed-attempt3.json](../provenance/chapter02-random-expectation-cast-repair-20261104/closed-attempt3.json).
The earlier partial observation remains byte-for-byte intact. The only owned
error was the corrected real cast; the mean example is not validated, and
successor1f315fdb remains uncompiled at this update.


## Checkpoint 0090 author hold

At root's durability request, the author is clean at
**1f315fdbb40288d99921164bb3fd8afcbd756e58**. The priority cast-repair
terminal evidence is closed and preserved, and the new source successor
remains uncompiled by this author. The reviewed rank plan, zero-finding root
assessment, implementation start and priority-interruption identity are
saved. Neither new rank Lean file has yet been created; the concrete proof
route is preserved under chapter02-random-rank-draft-20261104/proof-route.md.
All source/ref/provenance writes now HOLD for checkpoint0090. No build/cache
or other-worktree write was performed, and no acceptance status changed.


## Actual rank and size-mean source candidate c19a85f

After checkpoint 0090 was exposed, root released the already reviewed two-file
rank slice. The coherent source candidate is
**c19a85f8f5e256e87b0001f3e98afb2c7c1b08cc**, parent
1f315fdbb40288d99921164bb3fd8afcbd756e58. Exactly two new files are added:
Applications/Resources/RandomQuickSortRank.lean (393 lines) and
Examples/RandomQuickSortRank.lean (151 lines). All existing source and pins,
including the separate mean cast correction, remain byte-for-byte unchanged.
The author worktree is clean and has no .lake.

The source defines the actual occurrence-rank permutation, proves the actual
eraseIdx/complementary-filter child sizes and inherited mapped-key Nodup,
and transports the unchanged uniform occurrence sampler to the left-length
law. A four-universe strong induction pairs actual equal-rank pivots and
smaller executed child inputs to prove equal-length actual means. Only then
is sizeMean defined as the actual mean on List.range n and its successor and
positive range-sum recurrence derived from the actual bind-mean equation.
No harmonic module, assumed numerical execution recurrence, conditional
child-input resampling or priority coupling is introduced.

Consequential examples include nonidentity rank permutations on [2,0,1]
and [3,1,0,2], the actual unsorted left child [1,0], the means 71/3 and 109/3,
and distinct tags whose repeated keys give tie position 1 but strict-left
length 0. The existing actual equal-key quadratic mean remains outside the
distinct-key theorem's domain. Generic clients retain unrelated key types
and unrestricted tag universes.

Every source line and proof was read back. All **30 public declarations and
seven private helpers** have a [complete per-claim source assessment](../provenance/chapter02-random-rank-draft-20261104/statement-assessment.md).
The [candidate identity](../provenance/chapter02-random-rank-draft-20261104/candidate.json),
adjacent source inventory and full diff preserve the boundary. The resource
SHA-256 is 22960885c968620b957e7e2381baa8b887d9dc80a54fb72fe9644c3ace2890b4;
example SHA-256 is
a0f5fbd6b3d41cad08193a371228bede1b869a773608b21906e85f2848d747bf.
The staged whitespace check passed. These new files remain **uncompiled**,
with no elaborated-type, full-candidate/audit or independent review result.
No source mathematical finding was observed; compiler/linter/type output
remains required, and no acceptance or coverage closure is claimed.

Root has separately reported individual actual-mean core and example build
milestones at unchanged source 1f315fdb in the still-live central nine-target
attempt 4. No terminal aggregate or complete mean-type pass has been supplied
at this handoff. All previous failures and the truthful partial-to-terminal
cast-repair records retain their actual statuses.

The harmonic/logarithmic/Big-O connection, separate uniform-input mean and
pivot-work qualifications remain mandatory, together with all full immutable
candidate/audit/review/immediate-verification gates. No author build/cache,
other worktree, ticket or global control change occurred. The author now
holds all source/ref/control/provenance writes for root's central validation
and upcoming checkpoint 0091 capture.
