# Three-key successful-search expectation

## Source and mathematical statement

FDSA, 27 July 2026, printed p.67, compares two trees containing the keys
3, 6 and 9: a root 6 with leaves 3 and 9, and the increasing right chain
3, 6, 9. The illustration and surrounding discussion give a qualitative
comparison for equally likely keys. The exact finite distribution, tariff
and numeric targets used here are specified by canonical
[FDSA-5-94](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md).
The numbers 5/3 and 2 are derived from those conventions; they are not quoted
as formulas printed next to the illustration.

The implementation is in
[`SearchTreeVisits.lean`](../../Applications/Resources/SearchTreeVisits.lean),
with the complete finite example in
[`ThreeKeySearchMean.lean`](../../Examples/ThreeKeySearchMean.lean).

## The actual lookup and its observation

The pre-existing `Resources.SearchTree.lookupRun` returns an optional payload
and the pair `(nonempty node visits, binary strict-comparison calls)`.
`lookupVisitsRun` is exactly `Resources.reweight Prod.fst` of this executed
lookup. Its returned value equals `Search.OrderedMap.lookup`; the projection
retains the actual payload and selects the first work coordinate.

`lookupVisitsRun_node` derives the raw-tree recurrence from the existing
lookup recurrence. Reaching nil returns `none` and costs zero. A reached node
costs one plus the cost of the selected child; equality succeeds at that node
with cost one. Unchosen subtrees do not contribute. These theorems use the
linear order already required by `lookupRun`, with arbitrary payload types
and no payload equality or ordering, and they do not assume that the raw tree
satisfies a search-tree invariant. Orderedness is proved separately for the
displayed inputs.

The example defines the two displayed key trees literally. Their independent
inorder lists are both `[3, 6, 9]`; `Contains` is exactly membership in those
three keys, and both trees are ordered. `withUnit` supplies the fixed payload
`()` without changing any key or tree shape. Its key projection is proved
equal to the original raw key tree, and orderedness transfers through the
existing `OrderedBy` interface. All sample lookups succeed with `some ()`.

## Finite uniform sample and derived costs

The sample space is `Fin 3`, with `query i = 3 * (i.val + 1)`. The query map
is injective and its range is exactly `{3, 6, 9}`. Each sample has rational
weight 1/3; the weights are nonnegative and sum to one. `uniformMean` is the
finite weighted sum of a natural-valued observation. The search theorems
apply it to the actual executed lookup costs.

| Query | Balanced visits | Chain visits | Balanced binary tests | Chain binary tests |
| --- | ---: | ---: | ---: | ---: |
| 3 | 2 | 1 | 3 | 2 |
| 6 | 1 | 2 | 2 | 4 |
| 9 | 2 | 3 | 4 | 6 |
| Uniform expectation | 5/3 | 2 | 3 | 4 |

The six `*_run_*` theorems derive actual optional results and both work
coordinates from the public `lookupRun_node` recurrence. `balanced_run` and
`chain_run` collect those results over the finite sample. The projected
`*_visits_run` theorems derive the visit vectors `[2, 1, 2]` and `[1, 2, 3]`.
`balanced_visit_mean`, `chain_visit_mean`, and `uniform_visits_strict` prove
the expectations and their strict ordering. The binary-test expectations
are proved separately and retain their distinct tariff.

## Separating cases and limits

The balanced root hit at key 6 takes one visit but two binary strict tests:
the first test `6 < 6` fails, and the reverse strict test also fails. Thus
the visit expectation is not a relabeling of the comparator expectation.

`lookupInspections_eq_visits_of_success` proves that successful lookup has
no terminal nil inspection, and the example applies it to every present
sample for both trees. Missing key 0 takes two visits and three inspections
in the balanced tree, but one visit and two inspections in the chain. The
empty-tree result is `none`, with zero visits and one inspection for every
query. These cases prevent extending the successful-query bridge to failures.

`concentratedWeight` is another explicitly normalized nonnegative finite
distribution, putting all mass on sample 0, hence key 3. Its visit expectations
are 2 for the balanced tree and 1 for the chain. This reverses the uniform
preference, so the result depends on the stated query distribution as well
as the tariff.

The observations are abstract source-level counts. They do not charge tree
construction or sample selection, and assert no compiled runtime, physical
allocation or sharing, or bit complexity for natural-number comparisons.
No uniform distribution on an infinite key type is assumed. The result is
the prescribed finite example, without a general optimality claim for every
query population or search tree.
