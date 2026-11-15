# Whole orders induced by a shared random ranking

Historical checkpoint and local-ticket references in this account resolve through
the [preserved FDSA records](../history/textbooks/checkpoint-012/books/fdsa/README.md).
Current coverage and follow-up belong to [#558](https://github.com/VladimirMarko/conaled/issues/558);
old process and tracking instructions describe the producing session.

This bounded shared unit
continues the [minimum-law work](fdsa-permutation-minimum.md). It supplies no
chapter acceptance, recursive sampling theorem or algorithm cost bound.
The exact frozen requirements, source/API preflights, candidate identity and
eventual gate results are retained in the local FDSA-XU02 checkpoint record.

**Development validation — 4 November 2026.** The whole-order core and both
example modules had individual compilation successes in development checks
that failed overall. All 53 explicit public declarations from the corrected
source were subsequently included in the successful 815-declaration type
inspection at `4b5dbfa07288acc73f25c27838d3fb2f78e77d71`; both independent
reviewers assessed their complete printed types. These are historical results
for that development candidate. Reuse requires matching integration-candidate
evidence. The full acceptance gates below remain required.

## Actual list observation

`Applications.Probability.PermutationOrder.restrictedOrder positions S π`
is the ordinary expression

```lean
(positions.map π.symm).filter (fun a => decide (a ∈ S))
```

The permutation π assigns a key index to a priority-label index. The list
`positions` enumerates the labels in a chosen order. Therefore the key
belonging at a label is obtained through the inverse permutation. Filtering
retains the same relative order for the members of the fixed finset S.

This operation needs only decidable equality on the index type. Completeness,
absence of duplicates, finiteness, a key order, inhabitance and measurability
are not part of its definition. The finite target `orders positions S` is
the existing finset of all list permutations of
`positions.filter (fun a => decide (a ∈ S))`.

The value contracts expose the assumptions at the point where they matter:

| Contract | Hypotheses beyond the operation |
|---|---|
| Output membership iff the key's label occurs in positions and the key is in S | None |
| Output membership iff membership in S; output `toFinset` equals S | Every index occurs in positions |
| The output has no duplicates | Positions has no duplicates |
| Output length is S.card; output is a permutation of the filtered base list | Completeness and no duplicates |
| Mapping output keys back through π gives a sublist of positions | None |
| Filtering again to T equals restriction to S∩T | None |
| Filtering again to T equals restriction to T | T⊆S |

The mapped-sublist theorem checks the actual order correspondence. A law
about output membership alone would not distinguish different orderings.
The nested-filter theorem is a deterministic composition statement about
one sampled π; it does not condition the random experiment.

## Complete output distribution

For complete, Nodup positions, `uniformOn_restrictedOrder_eq` gives the mass
of every output list xs under the original uniform global permutation:

- If xs is in `orders positions S`, its mass is the ENNReal reciprocal of
  `S.card!`.
- Otherwise its mass is zero, including lists with repeated members, the
  wrong support or the wrong length.

The proof's local enumeration comes from the complete list. There is no
additional public Finite/Fintype I or nonempty-I premise, and no order or
measurable structure on I. The discrete fiber theorem requires only the
permutation sample space's existing measurable structure and measurable
singletons. It does not require an output measurable space.

With an existing measurable space and measurable singletons on List I,
`map_restrictedOrder_uniformOn` states the actual semantic equality

```lean
(uniformOn Set.univ).map (restrictedOrder positions S) =
  uniformOn (orders positions S : Set (List I))
```

The output support is finite. List I itself is countable when I is finite,
and is generally infinite when I is inhabited. The proof must not replace
that distinction by a false finite-list-space assumption. No new global
measurable-space instance is installed.

### Connection to the supplied random experiment

Two supported lists have the same finite support and length, with no
duplicates. Existing permutation-extension machinery maps corresponding
positions in one list to those in the other. The resulting permutation σ
preserves S because both lists have support S.

Right composition sends π to `π * σ.symm`. Its inverse list is the previous
inverse list mapped by σ; preservation of S makes filtering commute with
that map. Thus this bijection on the global permutation sample space
transports one entire output fiber to the other. Their uniform masses are
equal. The finite output fibers are disjoint and cover every sample, so
normalization gives reciprocal target cardinality. Existing list-permutation
cardinality results identify that cardinality with S.card factorial.

The Measure.map result follows from these actual fiber masses and the
existing finite/countable measure interfaces. It does not substitute a fresh
uniform subset draw without proving its connection. No new probability
carrier, ranking record, action hierarchy, selector or executor is introduced.
The Table, kernel and measured-execution interfaces keep their semantics.

## Connected examples and boundaries

`Examples.PermutationOrder` uses positions `[0,1,2,3]` on Fin 4 and subset
`{0,2,3}`. The selected output is Nodup, has exactly that support and length
three, and maps back to a sublist of the original labels. Its six whole
orders each have mass one-sixth.

`order_023_mass` derives the mass of `[0,2,3]` through the generic fiber
formula. `order_032_mass_via_map` derives the mass of `[0,3,2]` through the
mapped-measure theorem and the finite target measure. These lists share
their first key but differ as complete outputs. The repeated list `[0,0,2]`
has mass zero through the generic off-support formula.

`nestedObservation` filters the actual three-key result again to `{0,3}`.
Its pointwise equality with the direct two-key projection uses the public
composition law. The mass of the ordered result `[3,0]` is then one-half
through the new generic probability law. A singleton has its sole list
with mass one; a full Fin 4 order has mass one-twenty-fourth.

`Examples.PermutationOrderBoundary` records these consequential cases:

- Empty S has the singleton target `{[]}` and mass one at `[]`. The new
  generic theorem also applies to an empty index type with positions `[]`;
  the permutation space still contains its identity.
- For the cycle sending keys 0,1,2 to labels 1,2,0, the inverse global list
  is `[2,0,1]`. Restricting to `{0,1}` gives `[0,1]`; directly mapping the
  cycle instead gives `[1,0]`. This checks the pointwise orientation.
- Reusing the earlier integer priorities `-7,100,4`, enumeration `[0,2,1]`
  gives the strictly increasing priority list `[-7,4,100]` at the identity
  sample. Ordinary label enumeration has a different numeric order that is
  not strictly increasing. An arbitrary label order is not automatically a
  numeric-priority order.
- Incomplete positions `[0]` on Fin 2, under the swap and subset `{0}`,
  produce `[]`, outside the base list's permutation support. This example
  retains Nodup, isolating the missing completeness condition.
- Repeated but complete positions `[0,0,1]`, under the swap and full subset,
  produce `[1,1,0]`, outside the base list's support. This isolates the
  missing distinctness condition.

The inverse-orientation check cannot be replaced by marginal distribution
checks: inversion permutes the uniform sample space, so both orientations
can have the same distribution despite different pointwise meanings.
The independent finite calculations and source statement assessments are
preparation evidence.

## Source use and remaining obligations

The source edition, primary treap paper and exact pins are retained in the
[minimum-law source record](fdsa-permutation-minimum.md#source-use-and-remaining-chapter-work)
and the checkpoint's probability preflights. This unit supports the fixed
filtered-order component of Chapter 2's average/randomized quicksort and
Chapter 10's shared-priority treaps. It does not change those source models.

For Chapter 2, a revealed pivot or comparison history introduces a particular
conditioning event. Its normalized subproblem law needs its own proof.
Equivalence to fresh occurrence choices, duplicate payloads, both recursive
branches and the source tariff also remain. The recovered AFP quicksort
development has additional partition and joint-law results beyond this
single fixed-subset projection.

For Chapter 10, all operands continue to observe the same global ranking.
The separate minimum-law examples already retain a shared-law dependence
case. This unit asserts no independence of overlapping restrictions and no
joint law for disjoint restrictions. Canonical treap/root/ancestor semantics,
conditional depth, weighted charging and actual work remain later obligations.

Adaptive subsets, arbitrary conditional histories, expected preceding counts
and first-position means are separate scope. Completeness of this shared
unit requires its immutable-candidate compilation, guarded full check,
exhaustive axiom audit, both independent final axes and immediate candidate
verification. Its source and checkpoint presence alone close no such gate.
