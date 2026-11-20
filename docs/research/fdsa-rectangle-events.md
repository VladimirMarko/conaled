# Closed rectangles and occurrence-preserving events

This development supplies the geometry, event generation and ordering required
by FDSA Chapter 5 obligations C05-086–087. It uses the July 27, 2026 edition,
printed page 76, and the canonical
[Chapter 5 ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md).
The implementation is in [Rectangle](../../Applications/Search/Rectangle.lean)
and [Events](../../Applications/Search/RectangleSweep/Events.lean), with connected
[examples and counterexamples](../../Examples/RectangleEvents.lean).

## Geometry and occurrences

`Search.Rectangle α β` carries existing `IntervalKey` values for x and y, with
independent coordinate universes. Under preorders, `toSet` is the Cartesian
product of the two closed intervals, and `Intersects` means that the two regions
have a common point. The closed boundaries are included; a point rectangle and
a zero-height rectangle are legitimate inputs.

`Overlap` is the conjunction of the two coordinate overlap tests.
`overlap_iff_intersects` reuses both existing
`IntervalKey.overlap_iff_nonempty_inter` theorems and the product/intersection
laws. Its hypotheses are linear orders on the two coordinates. Neither the
geometry nor the event sort needs a bottom element.

The finite input is a list of occurrences. `HasIntersection rs` quantifies two
distinct `Fin rs.length` indices whose rectangles intersect. Equal rectangle
values at distinct indices are retained as distinct objects. A singleton has
no such pair, although its rectangle intersects itself. `hasIntersection_pair_iff`
connects a two-element input to ordinary geometric intersection; the general
`hasIntersection_iff_overlap` exposes the coordinate test without changing the
occurrence interpretation.

| Layer | Required structure | Preserved observation |
| --- | --- | --- |
| Rectangle endpoint carrier and `Overlap` | LE on each coordinate | Valid endpoint pairs and the cross-endpoint comparisons. |
| Region, nonemptiness and common-point intersection | Preorder on each coordinate | Actual closed regions and common points. |
| Overlap/common-point equivalence | LinearOrder on each coordinate | The endpoint test exactly characterizes geometric intersection. |
| Raw event | LE on x only | Arbitrary y value, complete x interval, kind and occurrence ID. |
| Event generation | The rectangle's LE assumptions | Exactly the canonical lower/upper-y events with source payloads. |
| Sorting and position order | LE on x, LinearOrder on y | Actual sorted sequence, occurrences and insertion-first ties. |

The weak carrier does not by itself establish geometric nonemptiness for an
arbitrary LE relation. The `RawX` example has an inhabited valid endpoint pair
and no point between those endpoints. Its event contracts still apply. The
`liftedPoint` example uses `Rectangle Int (ULift.{1} Int)` and connects geometry,
counts and positions at genuinely different coordinate universes.

## Actual event generation and sorting

`eventFor r kind id` copies `r.x`, the kind and identifier, choosing `r.y.low`
for insertion and `r.y.high` for deletion. The executable `rawEvents` binds
`rs.zipIdx` once, maps all insertions, maps all deletions, and appends those
lists. It does not implement generation by repeatedly looking up an input
index. `eventAt rs kind i` is a separate total specification lookup used in proofs.

`mem_rawEvents_iff` and `mem_events_iff` recover an entire canonical event.
`eq_eventAt_of_mem_rawEvents` and `eq_eventAt_of_mem_events` expose that recovery
using the event's actual kind and bounded ID. These laws constrain y and the
whole x interval as well as the identity. Forged events with a correct identity
but a different y or x payload are excluded in the examples.

The event key has the type `β ×ₗ (Nat ×ₗ Nat)` and value
`(y, (kind.rank, id))`, with insertion rank 0 and deletion rank 1. The actual
sort is the existing `SourceMergeSort.sortOn Event.key`. `events` generates and
sorts once, returning the list for a later scan. The sorter compares no x
endpoint and requires no equality or ordering of the entire event.

`sortEvents_sorted` and `sortEvents_perm` reuse the shared sorter's actual
contract. `events_sorted` and `events_perm` specialize it to generated inputs.
No stability claim is made: the shared sorter uses alternating halves and can
reorder records with equal keys. Encoding event kind before ID supplies the
required boundary rule directly.

Raw key equality recovers `(kind,id)`, but not x. Two raw insertions with the
same y and ID can carry different x intervals. Their sort still satisfies
sortedness and permutation, while their identity list is not duplicate-free.
For members generated from one input, identity consistency recovers the full
event; `eq_of_key_eq_of_mem_events` establishes that stronger restricted fact.

## Counts, uniqueness and actual positions

The identity projection of raw generation is the insertion-tagged range
followed by the deletion-tagged range. The ID projection is two copies of the
input-index range. These equations establish all of the following without
decidable equality on coordinate values:

- `length_rawEvents` and `length_events`: exactly `2 * rs.length` events.
- `count_identity_rawEvents` and `count_identity_events`: exactly one of each
  kind for an in-range occurrence ID, and zero for an out-of-range ID.
- `count_id_rawEvents` and `count_id_events`: exactly two events for an
  in-range ID, and zero otherwise.
- Duplicate-free identity projections and duplicate-free full event lists.

The corresponding sorted facts are transported through the actual sort
permutation. `existsUnique_position` gives the unique bounded output position
whose element is the canonical event. This is a mathematical existence and
uniqueness result, not a runtime position-search implementation.

`Event.insert_key_lt_delete` proves the stronger comparison needed at closed
boundaries: if an insertion's y is at most a deletion's y, the insertion's key
is strictly smaller, independently of both IDs. `position_lt_of_key_lt` turns
strict key comparison into strict order of actual positions in a key-sorted
list. Equal positions would contradict strictness; reversed positions would
contradict sortedness.

`insert_position_lt_delete` combines those results. The endpoint bound then
gives `own_insert_position_lt_delete`, including zero height. The public
`InsertionsFirst` predicate quantifies every pair of insertion/deletion positions
at equal y, and `events_insertionsFirst` proves it for the actual output. This
is stronger than each rectangle's insertion preceding its own deletion.

## Connected cases and rejected weaker contracts

The examples establish common-point witnesses for a point, a shared edge, a
shared corner, two overlapping flat rectangles, and negative endpoints. Two
further fixtures separate x overlap from y overlap. Every geometry conclusion
uses the public region or overlap/intersection API. Duplicate rectangle values
are tested as distinct occurrences, with distinct insertion events.

The exact finite schedules below are proved for the actual source sorter. The
proofs specialize its public recurrence on two and four events; they do not
replace the sort by an unrelated list with the right properties. Here `Ik`
and `Dk` mean insertion/deletion of input occurrence k.

| Input | Actual `(y, identity)` schedule |
| --- | --- |
| Point [2,2] × [3,3] | (3,I0), (3,D0) |
| Two copies of [0,1] × [0,1] | (0,I0), (0,I1), (1,D0), (1,D1) |
| Edge contact | (0,I0), (1,I1), (1,D0), (2,D1) |
| Corner contact | (0,I0), (1,I1), (1,D0), (2,D1) |
| Two overlapping flat rectangles at y=1 | (1,I0), (1,I1), (1,D0), (1,D1) |
| x-separated, nested y ranges | (0,I0), (1,I1), (2,D1), (3,D0) |
| y-separated, equal x ranges | (0,I0), (1,D0), (2,I1), (3,D1) |
| Negative-endpoint contact | (-3,I0), (-1,I1), (-1,D0), (2,D1) |

The point and weak/higher-universe fixtures obtain actual positions through
`existsUnique_position` and the own-order theorem. `flat_cross_positions`
checks all four cross-occurrence insertion/deletion pairs at equal height.
`edge_cross_positions` checks the essential insertion1-before-deletion0 boundary.

The deliberately incomplete `yOnly` and deliberately wrong `idBeforeKind`
algorithms also execute the shared source sorter. On the flat fixture they
produce I0,D0,I1,D1. The y-only edge fixture has the same identity order.
Their `InsertionsFirst` rejection uses actual positions 2 and 1. The flat
y-only schedule nevertheless has unique identities, correct counts and each
occurrence's own insertion before its deletion. These facts therefore cannot
replace the cross-occurrence tie requirement. No claim about an unimplemented
scan's returned Boolean is inferred from this scheduling counterexample.

## Presentation and integration assessment

This slice uses checked shared constructions for geometry and sorting. The
rectangle region is an ordinary product of existing interval regions; the
endpoint presentation is connected to common-point semantics by the two
interval equivalences. Event sorting retains the shared sorter's ordering and
permutation contract without adding stability. These uses need no new general
sort algebra or order instance on raw events.

The occurrence-sensitive list presentation intentionally retains information
lost by a set of rectangle values or by projecting active keys to x intervals.
Canonical event recovery connects that presentation to the original rectangle
payload. Its restricted key-injectivity theorem and raw-payload counterexample
state precisely where information can and cannot be recovered. A later active
state should use the complete interval/ID key; deleting through the noninjective
interval projection would need an additional multiplicity or collision argument.

No prior shared API or assumption is changed. The new example module is added
to the public aggregate while preserving every previous import. Actual receiving
integration must preserve both branch deltas and all receiving imports, assess
the combined candidate, and run its full build/audit. Focused donor checks and
textual merge compatibility do not establish that acceptance.

## Continuing obligations

C05-088–089 require an actual terminating early-exit scan, its active-set
invariant and the equivalence between its Boolean result and `HasIntersection`.
The existing `AbstractSet.DeleteOps`, `DeleteLaws` and `IntervalSet.Laws` provide
reusable state-update and observation contracts. Prove the finite prefix's active
IDs and their complete-key image first; then connect those sets to state through
the existing execution laws. Query the pre-insertion state. Distinguish the
mathematical full-prefix fold from prefixes actually visited after early return.

C05-085 still requires a concrete balanced interval representation with real
cache-aware updates and deletion. C05-090 additionally needs the cost of the
selected event generation, sort, queries, updates and early termination, with
active size bounded by the input length. The current correctness results alone
supply neither balanced updates nor an O(n log n) runtime claim. C05-091–094,
later FDSA chapters and appendices, all remaining PFDS work and receiving union
acceptance remain separately required by the continuing book formalization task.
