# Rectangle sweep, exact activity and closed-region correctness

This is the scan and correctness layer for FDSA Chapter 5, C05-088–089, following
the rectangle-intersection algorithm on printed page 76 of the July 27, 2026
edition. The [canonical Chapter 5 ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md)
states the full obligations. The earlier [rectangle and event account](fdsa-rectangle-events.md)
supplies the geometry, actual event generator, source merge sort, occurrence
recovery and insertion-before-deletion tie laws used here. This layer reuses
those definitions without changing their assumptions or identifying equal input
values with equal occurrences.

| Source | Responsibility |
| --- | --- |
| [Scan](../../Applications/Search/RectangleSweep/Scan.lean) | Carried complete keys, exact updates, terminating early return, arbitrary-list scan characterization and continuing-prefix equations. |
| [Active](../../Applications/Search/RectangleSweep/Active.lean) | Canonical positions, independent occurrence activity, exact update-fold observation and overlap-query bridge. |
| [Correctness](../../Applications/Search/RectangleSweep/Correctness.lean) | Distinct overlapping occurrences, soundness/completeness and geometric correctness. |
| [OrderedList interval search](../../Applications/Search/IntervalSet/OrderedList.lean) | Executable finite overlap search combined with the existing strict-list set laws. |
| [Connected clients](../../Examples/RectangleSweep.lean) | Concrete results, boundary cases, independent universes and separating incorrect algorithms. |
| [Measured generation, scan and active cardinality](fdsa-measured-rectangle-scan.md) | C05-090 progress: shared indexed generation and exact tariffs, actual pipeline binding, early-return observations, executed counts, primitive-cost envelope and strict balanced prefix node bound; full complexity qualification remains open. |

## Executable program and its semantic requirements

The complete active key is `Key α = IntervalKey α ×ₗ Nat`. Its first component
is the carried x interval; its second component is the occurrence ID. The scan
never recovers the rectangle by indexing the original input. `Event.completeKey`
copies the two payload fields already supplied by the canonical event generator.
`keyInterval` deliberately forgets the ID when answering an overlap query.

`scan ops query s es` recurses structurally on the event-list suffix. It returns
false on the empty list. At an insertion it queries the old state: a true query
returns immediately, and a false query inserts the complete key and continues.
At a deletion it removes that complete key and continues without a query. The
successful insertion is not executed after the hit. `sweep` binds `events rs`
once and scans that list from `ops.empty`; the proof-only position function is
absent from this computation. Structural recursion supplies termination without
an unproved measure or a bound on the state representation.

Operations and their laws remain separate. `AbstractSet.DeleteOps` supplies
empty, insertion, deletion and membership operations. Its existing `DeleteLaws`
states validity and exact complete-key set observations. `IntervalSet.Laws` adds
the independently specified overlap-query equivalence. None of those law fields
asserts a sweep invariant, sorted schedule, occurrence distinctness or final
rectangle correctness. Those are consequences proved by this development.

| Layer | Assumptions |
| --- | --- |
| Raw carried updates and scan | An LE relation on x, arbitrary y type and arbitrary state type, with supplied operations/query. |
| Generated activity and exact state observations | LE on x, LinearOrder on y, and the existing complete-key deletion laws for the state. |
| Sweep iff distinct endpoint-overlapping occurrences | The preceding coordinate assumptions and full interval-set laws. |
| Sweep iff distinct closed regions have a common point | LinearOrder on both coordinates and the same interval-set laws. |
| Executable strict-list realization | LinearOrder on x for ordering complete keys and deciding endpoint overlap; LinearOrder on y for the actual event sort. |
| Existing interval-tree realization | Its local LinearOrder and OrderBot requirements on x, plus the proved compatibility of complete-key order with low endpoints. |

The coordinate and state universes are independent. No generic correctness
theorem requires an x bottom, nonnegative endpoints, positive rectangle height,
distinct rectangle values, distinct x intervals, a `Nodup` input list or an
inhabited state type. The supplied empty state and laws already provide the
starting state and its validity. The raw scan theorem permits an arbitrary
initial state; the rectangle correctness theorem intentionally starts at empty.

## Activity comes from event prefixes

For input `rs`, let `E = events rs`, let `Iᵢ` and `Dᵢ` be the actual unique
positions of occurrence i's insertion and deletion, and let `K(i)` be its
complete key. For every natural prefix length k, `Active rs k i` means that the
insertion belongs to `E.take k` and the deletion does not. The checked position
equivalence is

\[
  \operatorname{Active}(k,i) \quad\Longleftrightarrow\quad I_i<k\ \land\ k\le D_i.
\]

The weak inequality at deletion is intentional: immediately before its deletion
event, an occurrence is still active. Both empty activity initially and empty
activity at or beyond exhaustion follow from this definition. Prefix lengths
beyond the schedule are allowed; `take` clamps them to the complete list.

Canonical recovery of the next event gives an insertion transition adding its
occurrence ID or a deletion transition removing precisely that ID. The map
`occurrenceKey rs` is injective because its natural-number component retains
the `Fin` index. Consequently its image transports exact deletion, even when
two x intervals coincide. No corresponding injectivity is asserted for
`keyInterval`.

Define the mathematical state `State(k)` by executing every update in
`E.take k` from empty. Reuse of `DeleteLaws.execute_valid` gives validity, and
the exact activity transitions and primitive step observation give

\[
  \operatorname{observe}(\operatorname{State}(k))
    = \{K(i)\mid\operatorname{Active}(k,i)\}.
\]

Here the right side is the set image under K. `stateAfter_take_observe` proves
this for every natural k, including empty input and exhaustion. Applying the
full query law and the existing image-overlap observation yields
`query_stateAfter_take_iff`: for every query interval q, the query in `State(k)`
is true exactly when some active occurrence has an x interval overlapping q.
Validity and observation are proved independently of whether any earlier query
succeeded.

Activity is finer than geometric coverage of the current ordinate. For two
zero-height rectangles at y=1, both cover that ordinate throughout the tie
group, but only the first occurrence is active after the first insertion.
After its hypothetical deletion, only the second is active. Replacing exact
prefix activity by all rectangles covering y would lose the insertion and
deletion boundaries that the proof needs.

## Mathematical prefix folds and actual continuation

`scan_eq_true_iff` applies to every raw event list and every initial state. It
characterizes a true result by the existence of an insertion position whose
query is true in the full mathematical update fold of its preceding prefix.
The witness need not be the first successful query. If an earlier insertion
already returned true, a later witnessing query is not visited by the program.

`ReachedMisses` supplies the missing continuation condition: recursively, every
insertion in the prefix must query false at its successive pre-update state.
Deletion contributes its state update and no query. `scan_eq_false_iff_reachedMisses`
connects this condition to the raw scan result. More specifically,
`scan_append_of_reachedMisses` proves that scanning a prefix followed by a suffix
continues at exactly the prefix's update-fold state when the condition holds.
`sweep_eq_suffix_of_reachedMisses` applies that equation to the actual generated
schedule, with the documented clamping of an excessive prefix length.

This condition is essential to an execution claim. An equality between two
Boolean results alone does not show that the later state was reached: both
results could be true despite an earlier return. The independent recursive
misses condition follows the actual control flow. In particular, after the
second insertion of two duplicate rectangles has hit, the fold may still be
used to describe later complete-key deletions, but those states are not
reported as continuing scan states.

## Soundness and completeness

`event_y_le_of_position_le` transports the actual sorted-key relation to weak
ordinate order. Suppose occurrence i is active just before occurrence j's
insertion. Then `Iᵢ < Iⱼ`, so the indices differ, and sortedness gives
`i.lowY ≤ j.lowY`. Activity also gives `Iⱼ ≤ Dᵢ`, hence
`j.lowY ≤ i.highY`. The valid endpoint bound for j completes y overlap.
`active_at_insert` packages this distinctness and y conclusion. A query hit
supplies x overlap through the independent interval-set law. Thus any successful
query gives two distinct endpoint-overlapping input occurrences.

Conversely, two distinct occurrences have distinct insertion positions. Choose
the later insertion j and the earlier occurrence i. Their y-overlap inequality
is `j.lowY ≤ i.highY`. The existing strong
`insert_position_lt_delete` theorem gives `Iⱼ < Dᵢ`: at equality of ordinates,
the sort compares insertion rank before deletion rank, irrespective of IDs.
Together with `Iᵢ < Iⱼ`, this makes i active for j's query.
`active_at_later_insert` states that implication using only the required cross
inequality. The query law supplies a true full-prefix witness, and the raw scan
theorem supplies the true result. No claim that this chosen witness was reached
is needed; an earlier hit already produces the same true result.

`sweep_eq_true_iff_overlap` therefore characterizes two distinct endpoint-
overlapping occurrences under bare LE on x. Under LinearOrder on x as well,
the existing `Rectangle.hasIntersection_iff_overlap` converts exactly that
predicate to closed common-point geometry. The resulting
`sweep_eq_true_iff_hasIntersection` is the soundness and completeness theorem
for the actual generated and sorted program. Closed boundaries, point
rectangles, zero height and repeated values remain included.

The separation of the two results matters. With an arbitrary LE relation, a
valid endpoint pair can lack any point between its endpoints. The endpoint
result remains meaningful in that setting; geometric equivalence is available
only under the stated order hypotheses.

## Concrete realizations and separating cases

The executable reference query uses `List.any` to decide overlap with a projected
complete key. Its observation theorem holds for any list. Strictness belongs
to the existing `OrderedList` update laws, so `orderedListLaws` combines these
independent facts without adding a sweep-specific invariant. Int coordinates
work directly, without adjoining a bottom element. This reference uses linear
list operations and makes no logarithmic complexity claim.

`keyInterval_low_le_of_lt` derives weak low-endpoint order from the actual
lexicographic complete-key order. In the strict first-component case it reuses
`IntervalKey.low_le_of_le`; in the equal-interval case the lows are equal even
though the IDs differ. This discharges the existing
`IntervalTree.intervalSetLaws` compatibility premise. The concrete tree's
OrderBot assumption remains local to that realization, as does its current
unbalanced implementation. Projected intervals need not be injective.

The companion clients connect the generic results to empty and singleton
inputs, duplicate occurrences, edge/corner/flat contact, separated x or y
intervals, and negative coordinates. They also distinguish full-fold states
from continuing states, use actual wrong-sort event lists, and exhibit the
query-after-insertion singleton false positive. Complete-key deletion preserves
another occurrence with the same x interval; deleting that interval from the
projected set would erase both and does not satisfy the same update observation.
That latter fold counterexample is not described as an invented later
false-negative run after an earlier hit.

## Correspondence and remaining obligations

The canonical ledger records the AFP proof route under `apply_ops_k`, `xints_of`,
the next-step/activity lemmas, `has_overlap_at_k_equiv`, `has_overlap_equiv` and
`rect_inter_correct`. Here the common update fold, complete-key image and
explicit continuation condition connect those proof roles to existing local
set and interval interfaces. Carried payloads preserve the chapter's interval
data, and distinct finite IDs preserve occurrence-sensitive deletion. This is
a fresh local derivation; it does not claim that an Isabelle session was run or
that lost source code was reconstructed exactly.

C05-085 now has a concrete balanced interval representation with cache-aware
updates and deletion, described in [its paper](fdsa-balanced-interval-tree.md);
C05-085 is now qualified after receiving validation and independent review
under [issue #659](https://github.com/VladimirMarko/conaled/issues/659).
C05-090 still requires the selected
implementation's conditional O(n log n) bound, including event generation,
sorting, all queries/updates, active-size bounds and early termination. Shared
semantic meaning does not transfer an operation-cost or physical-sharing
theorem. C05-091 and C05-094 are already qualified under their existing owners;
C05-092–093, later FDSA chapters and appendices, remaining PFDS work and
receiving integration remain separate obligations. Source compilation and
focused proof audits also do not substitute for the independent reviews or the
receiving whole-library acceptance of the combined branch contents.

## Unqualified preparation for the measured sweep

The conditional theorem remains unfinished even though generic cached-height
foundations are now present. It can be developed before the interval instance is
finished, using primitive measured operations and their value/validity/size/cost
contracts. Its assumptions must concern those independent operations and the
sorter; a field asserting the desired whole-sweep bound would be circular.
Whole-book completion still needs the concrete balanced instance to discharge
the premises.

First define measured event construction following the actual shared indexed
list, both maps and the append. Prove its returned value is exactly `rawEvents`
and give a linear bound under explicitly declared unit operations. Charge any
ID increment/list construction being included. The current implementation avoids
repeated indexed rectangle lookup; preserve that property.

Use `Resources.SourceMergeSort.run` on the actual event comparator and prove the
returned schedule equals `events`. Its existing two observations already give
`2*(2*n)*clog 2 (2*n)` as an upper bound for splitting plus comparisons. For a
broader source-work model, include and bound the omitted comparator execution,
recursive entries, list construction and length tests as appropriate. In
particular, `run` tests `xs.length<=1`; its current `work` explicitly excludes
that traversal cost. A new measured recurrence may charge it and prove its sum
is bounded by the same split recurrence plus base overhead. Do not call the
existing two-coordinate theorem a bound on costs it expressly excludes.

The [measured development](fdsa-measured-rectangle-scan.md) now proves the exact
linear tariff for shared occurrence indexing, both constructor maps and append.
Its generation-sort-scan composition binds each actual stage result once. The
sorter remains a supplied measured callback until its complete tariff is proved.
The measured scan binds actual
query/update results in the same order as `scan`: query then conditional
insertion, deletion without query, and no suffix execution after a hit. It proves
value erasure, additive reweighting, exact operation counts and constant tariffs,
and a cumulative scan bound from primitive bounds and invariant closure.
Nonnegative projected charges permit a full-schedule envelope without asserting
that skipped suffix operations executed. These bounded components have receiving
source acceptance; the complete C05-090 row remains open.

`ActiveCardinality` now proves the finite cardinality bound of at most n from
the subset of `Fin n`, injective complete-key map and existing exact prefix
observation. These are full mathematical prefix states; actual continuation
still needs the earlier miss condition. The concrete balanced prefix now has a
checked node-count/complete-key-cardinality equality from strict inorder, and
therefore at most n nodes. The primitive envelope still needs its admitted
support invariant. The equality is false on raw trees containing repeated keys.

Instrument concrete AVL updates, predecessor extraction, smart reconstruction,
rotations and overlap search. One-branch query cost is linear in height; updates
visit a search path and deletion may additionally traverse a predecessor path,
with bounded local reconstruction per returned level. Derive these bounds from
the actual measured recurrences, then use the checked AVL logarithmic height.
State the tariff for key/endpoint comparisons and cached-height arithmetic.
An abstract unit-cost model does not establish bit complexity of unbounded Nat
IDs, arbitrary comparator execution, machine runtime or allocation.

There are at most n insertion queries, n insertions and n deletions, with some
omitted after early termination; there are 2n scheduled events. Combine generation,
sorting, scan overhead and those operation costs, rather than charging only
overlap queries. A safe intermediate all-input envelope is of the form
`C0 + C1*n + C2*n*clog 2 (n+1)` under the declared model. Handle n=0 separately
when stating a bound without the additive constant. An operation on an empty
state can have positive cost while `clog 2 (0+1)=0`; use a justified
`1+clog 2 (m+1)` operation bound or restrict the global n>=1 phase before absorbing
constants. The final real-log/Big-O conversion and n=0/1 cases still need proofs.

### Attribution and scope of this preparation

The original cost decomposition and following separators originate in
`/root/balanced_interval_preparation`'s 18 November 2026 paper. The new measured
generation/scan/cardinality work is distinguished above and in its own maintained paper.
The remaining sorting, support and concrete-operation preparation is still
unqualified; moving it here supplied no theorem, runtime result or acceptance. The corresponding
[balanced interval paper](fdsa-balanced-interval-tree.md) owns the concrete
augmentation design. CTB-24 retains the open canonical row and
[CTB-78](../textbooks/CTB.json) owns current receiving acceptance.

### Cost and execution separators

6. **Asymptotic boundary.** A fully rebuilt n-node balanced state may have
   logarithmic query height while its next whole-tree rebuilding update costs
   linear work. Separately, positive empty-state operation cost refutes a
   literal all-m cost bound `K*clog 2 (m+1)` at m=0. Keep both qualifications.
7. **Early termination and generation.** Empty rectangles generate no events;
   a singleton has exactly two events; duplicate intersecting occurrences halt
   on their second insertion query. The measured execution must not charge an
   insertion or deletion that its branch skipped, even when a larger nonnegative
   upper envelope includes potential suffix work.

### An unbalanced no-hit family with quadratic query visits

The same 18 November preparation gives a concrete separator for C05-090. For
n occurrences take `R_i=[2*i,2*i]×[0,1]`, with indices `0,…,n−1`, and the actual
`(y,kind,id)` event order. All insertions occur first in increasing i. Every pair
has disjoint x intervals, so no query returns true and the scan does not stop
early. Instantiating with the existing unbalanced interval tree produces a
right chain. Before inserting occurrence i, both its overlap query and its
insertion traverse i existing nodes. Query visits alone therefore sum to
`n*(n−1)/2`.

For n=4 the insertion query-visit vector is `[0,1,2,3]`, totaling 6; insertion
visits have the same vector. All four insertions precede the four deletions,
the Boolean result is false, the caches are valid, and the full final state is
empty. These are unqualified paper expectations, not a new measured Lean result.
They show why semantic correctness, exact maxima and one-branch search cannot
supply the intended logarithmic-operation premise.

The full-exhaustion scan has exactly n queries, n insertions and n deletions.
On an early hit there is exactly one more performed query than insertion;
creating and sorting the schedule has already occurred. One useful conditional
paper envelope, under explicit generation/control and operation tariffs, is

`W(n) ≤ c0 + cE*(2*n) + S(2*n)
       + n*(CQ+CI+CD)*(1+Nat.log2(n+1))`.

The existing sort's two counted components give
`S(2*n) ≤ 4*n*Nat.clog 2 (2*n)` for exactly those components. Comparator work,
length tests, other control charges and the actual balanced operations still
need their own bounds. Empty-input overhead and the n=1 nonzero-event case
prevent treating a pure `n*log n` expression as an all-input pointwise bound.

### Exact AFP correspondence boundaries

A later 18 November 2026 preparation by the receiving integration agent reported
complete reading of the pinned AFP archive and both functional theories. Its
recorded identities were:

| Primary object | Bytes | SHA256 |
| --- | ---: | --- |
| [Dated AFP archive](https://isa-afp.org/release/afp-Auto2_Imperative_HOL-2026-10-26.tar.gz) | 61,323 | `fb60c5d0b1ad9864f0ff0aa615e1522d4ace0be1a56db6c7bf5ae0fdd3f8b6bb` |
| `Functional/Interval.thy` | 2,973 | `8beda04266632402d535a18130ea083ac64fd43d735e377c926f67ad7e272813` |
| `Functional/Rect_Intersect.thy` | 15,217 | `10fd8b006de4d7b64c48825998e0aa415a3d3e92d4a266a20836d97f612318e0` |

That attribution resolves the earlier paper's then-unread AFP dependency; it
is not a new primary reading or Isabelle execution by this curation. The AFP
entry is Bohua Zhan's *Verifying Imperative Programs using Auto2*. Its raw
interval representation requires a separate validity predicate. The Lean
`IntervalKey` already carries that condition, while the common-point geometry
has its own explicit bridge.

The AFP geometry/event results are polymorphic, but its final `rect_inter`
function is specialized to Nat rectangles and an abstract set of indexed Nat
intervals. It does not instantiate a balanced executable interval tree. Its
arbitrary event order additionally compares interval payload after y, kind and
ID; the Lean key-based sorter instead uses generated-event consistency, without
asserting an antisymmetric order on every raw event by an incomplete key.

There is also a literal execution difference. On the last unsuccessful event,
AFP returns false without applying that final update. The structural Lean scan
applies each unsuccessful event, then returns false on the empty suffix. Their
returned Boolean can express the same specification; their literal update
traces and final states must not be identified by that fact alone.

Finally, AFP's recursive equation and its update helper mention `all_ops rects`
inside their bodies. Its decreasing-index termination measure establishes no
sort-cost theorem and no compiler hoisting or repeated-evaluation result. The
Lean driver binds its actual sorted schedule once. The source's semantic proof
route therefore does not by itself certify the measured bound proposed here.
