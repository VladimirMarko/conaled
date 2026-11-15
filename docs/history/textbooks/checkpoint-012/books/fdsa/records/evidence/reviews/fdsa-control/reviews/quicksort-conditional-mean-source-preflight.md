# Conditional-mean proof plan: separate bounded source check

Recorded 2026-11-02. Contributor: `/root/tail_examples_preflight`.
Inspected root's `../research/quicksort-conditional-mean-preflight.md`,
10,877 bytes, SHA-256
`464af5974d485823b7ecb76b7546ad793ed860fbf947afdb03ef11d91b25b66c`,
against the saved XU02/XU03 declarations and the cited Mathlib pin.
The report is transcribed by root from the contributor's completed response.

## Result

No concrete mathematical, source-interface or pinned-API mistake was found
in this bounded reading. No correction was requested. This is a check of a
future proof plan, not a formal theorem, final review or acceptance result.

The contributor inspected these material boundaries:

- The on-event `filter_tail_restrictedOrder_eq` requires the actual head
  event and a fixed child contained in `S.erase a`. The note correctly
  retains the additional source-comparator versus membership-filter bridge
  on the actual tail, without asserting an off-event equality.
- `map_restrictedOrder_cond_first` gives the original child projection's
  law under the specified conditional measure with that containment premise.
  Together with `map_restrictedOrder_uniformOn`, it supports the two public
  HasLaw constructions. The proposed client does not use a private helper or
  reset the whole environment to its original distribution.
- `HasLaw.integral_comp` takes `AEStronglyMeasurable` under the target law.
  `AEStronglyMeasurable.of_discrete` has the stated countability and
  measurable-singleton requirements. `Integrable.of_finite` also requires
  a finite domain, measurable singletons and finite measure; the permutation
  functions fit once the unconditional/conditional probability instances
  are supplied. Integrability remains separate from integral transport and
  is retained for addition.
- `integral_biUnion_finset` takes the measurable events, their pairwise
  disjointness on the indexing finset and integrability on each event.
  Optional-head coverage requires positive subset cardinality.
  `integral_smul_measure` uses the scalar's `toReal`. Positive finite head
  mass permits multiplying the conditional integral by the event mass to
  recover the restricted integral; no null/infinite cancellation is used.
- The finite membership subtype and attached enumeration do not require a
  globally finite payload type. The value/cost transport and actual-input
  distinct-key premise remain necessary future proofs, not consequences
  claimed from constructing the subtype.
- `Finset.orderIsoOfFin S rfl` and `orderEmbOfFin` have the stated types.
  Under the lawful linear order, the children correspond to embedded
  `Finset.Iio k` and `Finset.Ioi k`, whose inspected cardinalities are k and
  n-1-k. The additive theorem generated as `Finset.sum_range_reflect`
  supplies the stated reflected-range formula. The plan does not assume
  one fixed finite environment contains subsets of every natural size.
- Empty-input mean is 1 without conditioning. At size one, two empty child
  costs and the nonrecursive toll give 1+1+3=5. The harmonic expression has
  those same boundary values. The positive-size recurrence and conversion
  from the natural toll to `4*n-1` retain positive cardinality.

## Limits

The actual sorter, comparator-filter, payload-map, rank-image,
cost-recurrence and harmonic-solution proofs remain future Chapter 2 work.
This assessment gives no elaboration or acceptance evidence for the plan's
underlying source drafts. It did not cover the separate randomized-execution
preparation.

The contributor edited no file and ran no compiler, Git/ref, cache, project
hash helper, gate or implementation operation. The active old Chapter 1
validation continued unchanged.
