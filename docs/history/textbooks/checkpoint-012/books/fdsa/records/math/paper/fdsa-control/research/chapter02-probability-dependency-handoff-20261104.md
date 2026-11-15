# Chapter 2 probability: exact dependency and execution handoff

Date: 2026-11-04. Preparation only; no implementation, compilation, candidate
check, audit, or new review round was performed for this note.

This note supplements, rather than replaces, the complete
[average proof plan](quicksort-average-proof-plan.md),
[conditional-mean preflight](quicksort-conditional-mean-preflight.md),
[conditional-mean source assessment](../reviews/quicksort-conditional-mean-source-preflight.md),
and [random-pivot API preflight](random-pivot-api-preflight.md).
Its new information is the exact source-import versus historical-acceptance
dependency distinction, the checked quicksort value candidate now available,
and the boundary with the deterministic resource implementation currently
assigned to another agent. The frozen
[Chapter 2 requirements](../reviews/chapter02-requirements.md), including
C02-024 and its resource qualifications, remain authoritative.

## Identities and status at preparation

The accepted Chapter 1/book tip remains
`07e480f6ec9958d4975bb90151005b84f2907614`. The separate foundation candidate
`f17cc6b1a2bf44215b16202ed0fcee2b5c130761` remains pending its newly running full
ordinary gate. Neither historical interrupted output nor current progress is
a terminal result. This preparation closes no foundation acceptance gate.

The immutable focused-checked quicksort value candidate is
`840252e63026bba5eab109f2b16468deef7670ec`. Its
`Applications/Sorting/QuickSort.lean` and `Examples/QuickSort.lean` establish
the actual head-pivot, strict-left/complement-right value definition and the
actual append-free accumulator simulation for every suffix. They contain no
resource observation, random algorithm, expectation theorem, or execution-cost
transport under payload relabeling. The complete-candidate gates remain
separate from those focused results; see the
[value implementation handoff](../reviews/chapter02-quicksort-implementation.md).

The current deterministic resource assignee is preparing
`Applications/Resources/QuickSort.lean` and `Examples/QuickSortCosts.lean`;
its live scope is recorded separately in the
[cost implementation handoff](../reviews/chapter02-quicksort-cost-implementation.md).
The communicated scope includes the two actual measured filters, actual
right-associated append assembly, the pair of exercise and append observations,
the suffix-worker cost relation, exact extremal cases, the quadratic upper
bound, and the same-execution pivot statistic/pointwise bridge. No probability
implementation is assigned to that work. A development merge of the exact
pending foundation for `ListCalls` does not imply acceptance of either unit.

The probability drafts below were inspected at their exact Git objects. Their
tickets still record uncompiled/unaccepted drafts with full checks, audits,
and final independent reviews pending.

| Unit | Exact draft | Actual probability source relationship |
| --- | --- | --- |
| XW01 | `7c6bc92c276d39e84351324c442869b8ffa6758c` | `AccumulatedWork` imports Mathlib; its integrated-drift assumptions must be supplied by a later client. |
| XU01 | `ff3dd88082c6283df40bcd86a4363841a0360b12` | `PermutationMinimum` imports Mathlib; fixed-subset minimum law under an injective priority assignment. |
| XU02 | `4bb13e44a6c7e3277b69cbac9fd9dd37cd7780f8` | `PermutationOrder` imports Mathlib, **not** `PermutationMinimum`; whole restricted-order law. |
| XU03 | `a0597381f02eddd074ee96cabaa974f2062285f8` | `PermutationTail` imports `PermutationOrder`; actual conditional tail and remaining-subset marginal laws. |
| XU04 | `11923e9ffd17246b6f22c5594002a1ba0434e43c` | `PermutationExpectation` imports `PermutationMinimum`; aggregate preceding-count and first-position means. |
| XU05 | `a5341221bd3e28d76e3b8ad2bc1683a74621ad5e` | Extends `PermutationOrder` with the disjoint-pair law and a filter-pair `HasLaw`; it does not import `PermutationExpectation`. |
| XU06 | `49d6d4700b41f2837ae4cc5e74d23fc1eff8afbe` | `PermutationPlacement` imports `PermutationExpectation` and `PermutationOrder`; also extends those files with relabeling/invariant-event laws. |

These are source relationships, not permission to omit inherited candidates
from acceptance. XW01 and XU01 branch from the old Chapter 1 repair
`a14977b9e316cc484ffad8a470d26b15615956c0`. The historical Git and ticket chain
then runs XU01, XU02, XU03, XU04, XU05, XU06 in that order. Any integration must
reconcile that history with the accepted Chapter 1 state, preserve unit scopes,
and satisfy their recorded gates. Importing the XU06 tip would also import
unaccepted predecessors; it is not a shortcut to the smaller Chapter 2 proof.

## Minimum dependencies for the two claims

### Uniform-input first-pivot mean

The mathematical/source dependency is the actual deterministic measured
quicksort plus **XU02 then XU03**, followed by the source-specific bridges below.
The existing historical acceptance chain additionally includes XU01. Nothing
in the selected mean argument requires XW01 or XU04–06.

Use a finite set of occurrence labels with a complete nodup `positions` list;
map labels to the fixed input payloads. This keeps the payload type arbitrary.
The selected observation is the original sample's
`restrictedOrder positions S π`, not a newly resampled subproblem. XU02's
`map_restrictedOrder_uniformOn` supplies its whole-order law. XU03 supplies
`head_mass_of_hasLaw`, `hasLaw_tail_cond_first`,
`hasLaw_filter_tail_cond_first`, and the original-sample specialization
`map_restrictedOrder_cond_first`.

For a fixed selected head `a`, define the actual child sets inside `S.erase a`:
the strict-lower keys and the complementary greater-or-equal keys. Prove that
the source's comparator filters of the actual tail are the corresponding
membership filters, then use `filter_tail_restrictedOrder_eq` and the
conditional law. The same conditioned full permutation environment is not
uniform again. Only the required child observations have the stated laws.

The existing XU03 examples make this limitation consequential:
`Examples/PermutationTail.lean` proves `environment_changed` and reuses a
tail `HasLaw` after a second conditioning. Its boundary example conditions the
order of `{0,1}` on head `0`, then observes `{1,2}`: the conditional masses are
`1/3` and `2/3`, not `1/2`. Merely excluding the exposed pivot does not replace
the required containment in the selected remainder.

The mean proof can use these marginal laws and linearity. It does not need
independence of the left and right orderings. If a stronger full distribution
identity is chosen instead, XU05's `hasLaw_filter_pair`, applied to the proved
conditional tail law with fixed disjoint child sets, is an additional useful
dependency; actual execution/sampler correspondence would still be required.

### Fixed-input, fresh randomized-pivot mean

The direct route uses the measured-list infrastructure and Mathlib PMF APIs,
with an actual recursive random program. It has no mathematical dependence on
XW01 or XU01–06. Retain the existing random-pivot preflight's construction:
at every nonempty recursive call sample a uniform valid **occurrence index**,
read that occurrence, remove it by index, execute the two actual measured
filters, bind the recursive left and right computations, and assemble the
source result with the declared observation. This is an implementation plan,
not a claim that such a program already exists.

Fresh pivot choices are conditional on the actual current input. Sampling a
deduplicated key set, choosing one pivot only at the root, or assuming an
unproved global-priority coupling does not instantiate this route. For
`[a,a,b]`, a uniform occurrence chooses an `a` with mass `2/3`.

The preflight's projected PMF on natural-number cost avoids imposing a
measurable-space or finiteness instance on arbitrary payloads. Its support
bound, finite lower expectation, and real integrability obligations precede
the real mean recurrence. The explicit heterogeneous `PMF.bind`/`PMF.map`
construction remains relevant for different label/payload universes; there is
no reason to introduce a new generic probability framework for this client.

XW01 assumes an integrated drift inequality for supplied observations. XU04
concerns fixed global placement statistics. XU06 assumes the corresponding
global permutation law for fixed-subset count/order independence. None of
them constructs this random quicksort execution or proves its adaptive pivot
law. They cannot fill that missing bridge merely by being available as drafts.

## Remaining execution bridges and ownership boundary

The following work remains after the currently assigned deterministic cost
unit. Proposed contracts below describe obligations, not existing theorem
names or checked Lean results.

1. **Finite-label/payload transport.** Connect the measured deterministic
   program on occurrence labels with the same program on mapped payloads,
   preserving the value and the selected cost. Comparator agreement must be
   explicit. A transport lemma specialized to the chosen finite labeling is
   sufficient; a generic relabeling framework is not required. The current
   value candidate's permutation and length laws do not supply cost transport.

2. **Actual conditional child identification.** For each exposed head, prove
   the comparator-filter/membership-filter correspondence above, child support,
   positive finite head mass, and the conditional integral transport for the
   measured cost. Use public `HasLaw` records or public map laws; convenience
   constructors private to the draft cannot be imported as public clients.

3. **Key-rank correspondence.** Under distinct keys, identify the child sizes
   as `k` and `n-1-k`, with the actual selected pivot uniformly ranging over
   `k < n`. Prove inherited distinctness in both children. This requirement
   concerns keys: distinct payload records with equal keys are insufficient.

4. **Uniform-input expectation.** Apply the conditional marginal laws, actual
   cost recurrence, and finite head-event partition. The retained plan's
   induction over `S.card`, directly proving the closed-form target for every
   selected subset, avoids inventing unavailable subsets of every size inside
   one fixed finite environment. Measurability, integrability, and nonzero
   finite conditioning masses remain explicit obligations.

5. **Actual random execution and its expectation.** Define the recursive PMF,
   prove support/value correctness and the same measured recurrence for each
   actual branch, and bound its cost support. Derive the bind expectation and
   use the same rank counting. The deterministic pointwise bridge to a pivot
   statistic does not by itself supply a probability law for that statistic.

6. **Solve and export the mean bound.** Share the finite-sum/harmonic algebra
   between the two mean proofs only after both have their actual recurrences.
   Prove the asymptotic bound using the pinned growth interfaces. A purely
   numerical recurrence or the saved rational calculations is not evidence
   about either algorithm's random work.

## Concrete implementation order

Complete and check the assigned deterministic measured unit first, keeping
its immutable boundary and the foundation dependency explicit. In parallel
with source-only preparation, the recorded XU01–XU03 candidates can be
reconciled and validated in their own scopes; no concurrent builder may share
writable outputs. This note authorizes no build or integration action.

Next add the small occurrence-label/partition/rank bridges, then implement the
uniform-input mean using the already documented XU02/XU03 route. Define the
direct randomized-pivot PMF as a separate source-preserving client and prove
its support and bind-mean obligations. Reuse the harmonic recurrence algebra
between the two completed clients. Finally lift each result to any separately
claimed append or selection/removal observation through the proved metric
bounds. Retain the existing full-candidate, audit, dual-review, immediate
verification, and integration gates throughout.

This order avoids starting XW01 or XU04–06 merely to obtain the two C02-024
expectations. Their later book obligations and acceptance status remain intact.

## Qualifications and first consequential examples

The source rule remains head/selected pivot, strict-left `<`, nonstrict-right
`≥`, with both filters operating on the tail or on the list after removing
exactly the selected occurrence. Distinct-key probability theorems should use
the chosen formulation of `(xs.map key).Nodup`; no finiteness assumption on all
payload values is warranted.

For Exercise 2.4 the base call count is `T([]) = 1`. A nonempty input with tail
length `m` makes two filter calls, each costing `2m+1` under unit callback
cost, in addition to the quicksort entry. Its local toll is therefore `4m+3`.
The target pointwise bridge is `T = 4Q + 4n + 1`, where `Q` uses those same
pivots and partitions and counts the tail length once per nonempty node. The
literal source traverses the two filters separately: `Q` must not be described
as its complete predicate-evaluation count.

The retained exact mean target is
`A_n = 8*(n+1)*H_n - 12*n + 1`, with `A_0 = 1` and, for positive `n`,
`A_n = (2/n) * (sum_{k<n} A_k) + 4*n - 1`. It remains a proof target. Saved
independent arithmetic gives `A_1 = 5`, `A_2 = 13`, and `A_3 = 71/3`;
the three-key cost distribution should expose masses `1/3` at `21` and `2/3`
at `25`. These cases distinguish the actual tariff from a comparison-only
formula. See [the saved exact calculations](quicksort-average-calculations.json).

All-equal keys keep the right child of size `n-1` at every call, for every
shuffle and pivot choice, and have the quadratic target
`2*n^2 + 2*n + 1`. Tagged equal-key payloads should retain this limitation;
random pivot output order need not be stable.

The exact exercise count excludes append traversal. The checked value source
uses `left ++ ([pivot] ++ right)`. With append-call observation `len(left)+1`
per call, those two actual append calls contribute `k+3` locally when the
sorted left child has length `k`. Reassociating values to
`(left ++ [pivot]) ++ right` would instead contribute `2k+3`; value
associativity cannot identify these measured executions. Preserve the actual
association and prove the separate whole-run bound, as assigned to the
deterministic resource unit.

Uniform-pivot selection, index lookup/removal, and random-bit costs are not
silently included in the exercise count. An explicitly measured linear
selection/removal overhead can be carried through a separate bound; physical
runtime or random-bit complexity would need their own stated models and proofs.

## Preparation outcome

No new specification contradiction was identified. The minimal mean routes
are already mathematically outlined in the retained plans. The concrete
remaining gap is implementation and proof of the algorithm-to-random-work
correspondence, including finite-label cost transport and the direct random
program. No obligation, ticket, coverage row, source finding, or acceptance
status is changed by this note. No source, dependency, candidate, or Git ref
was modified, and no execution session was polled.
