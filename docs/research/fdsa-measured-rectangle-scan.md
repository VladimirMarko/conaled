# Measured rectangle generation, scan and active keys

This paper records bounded progress on **CTB-24 / C05-090**, the conditional
rectangle-intersection complexity obligation in the
[canonical Chapter 5 ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md).
It continues the [functional sweep proof](fdsa-rectangle-sweep.md) for the
algorithm on printed page 76 of the July 27, 2026 FDSA edition. The exact source
and its reading limits remain recorded in the existing textbook owners. This is
a fresh local cost derivation, not an assertion that an AFP session was run.

The development implements measured event generation and an early-return scan,
proves their erasure and exact cost/count laws, derives a scan envelope from
primitive bounds, and proves the active complete-key cardinality bound. One
measured pipeline binds the returned generation and sorting results into the
scan. **It does not complete C05-090.** The complete sorting tariff, concrete
balanced-operation costs and the final asymptotic composition remain obligations. The current
balanced interval-tree implementation is separately described in
[its paper](fdsa-balanced-interval-tree.md); C05-085 qualification does not
supply measured operation costs.

## Owners and reused interfaces

| Owner | Responsibility |
| --- | --- |
| [Measured indexing](../../Applications/Resources/ListIndex.lean) | Actual occurrence indexing, arbitrary starting index, exact pair/successor and invocation tariffs. |
| [Measured events](../../Applications/Search/RectangleSweep/MeasuredEvents.lean) | One shared indexed list, both actual constructor maps and append, exact generation costs and once-bound generation/sort/scan composition. |
| [Measured scan](../../Applications/Search/RectangleSweep/Measured.lean) | The actual measured executor, value erasure, additive reweighting, exact counts and primitive-cost envelope. |
| [Active cardinality](../../Applications/Search/RectangleSweep/ActiveCardinality.lean) | Finiteness, occurrence/cardinality equality, input-length bound, lawful prefix-state transports and the strict balanced node-count bridge. |
| [Connected cases](../../Examples/MeasuredRectangleSweep.lean) | Existing rectangle schedules, positive empty cost, early return, deletion, returned-state sequencing, ordered observations and duplicate cardinalities. |
| [Generation cases](../../Examples/MeasuredRectangleEvents.lean) | Occurrence indexing, raw/sorted order, exact input-dependent generation costs, callback-result controls and pipeline clients. |
| [Ordinary measured pairs](../../Applications/Resources/Measured.lean) | Existing value/observation pairs and binding; no new resource framework is introduced. |
| [Scan](../../Applications/Search/RectangleSweep/Scan.lean) and [activity](../../Applications/Search/RectangleSweep/Active.lean) | Existing raw scan, full update folds, continuation conditions and occurrence-sensitive observations. |
| [Events](../../Applications/Search/RectangleSweep/Events.lean) | Carried complete keys, indexed generation, sorted permutation and two events per occurrence. |

The existing whole-list measured folds execute every item. Reusing them as this
executor would erase the early-return distinction. The new definition instead
uses the existing measured-pair binding directly and recurses structurally on
the remaining event list. Ordinary state and observation universes remain
independent of both coordinate universes.

## Occurrence indexing and event generation

`Resources.ListIndex.run p c xs start` pairs each element with the current
natural-number index, computes its successor, and passes that returned index to
the recursive tail. The returned pair and tail supply the result list. The
algorithm pays one invocation charge, including at the empty suffix, pair
tariff `p` and successor tariff `c` at each nonempty invocation. Thus

\[
\operatorname{value}=\operatorname{zipIdx}(xs,start),\qquad
\operatorname{cost}=(p+c+1)|xs|+1.
\]

The last cons still computes its successor before the empty call. The initial
index can be arbitrary and does not change the cost. No equality or ordering on
the payload type is required, and its universe is independent of the Nat
observation. This is a measured realization of the recursive source operation;
it makes no cost claim about Lean's compiled `List.zipIdx`, unbounded-integer
arithmetic, physical allocation or sharing.

`rawEventsRun p c makeRun rs` binds this indexer at start zero once, passes the
same returned list to both existing `Resources.ListCalls.mapRun` calls, then
passes their returned lists to `Resources.ListReversal.appendRun`. The first
map constructs insertions and the second deletions. No repeated positional
lookup, sorting or scan is part of this generator. Raw generation requires
only the LE structures already used by the rectangle type.

Let `n = rs.length`, and let `CI` and `CD` be the sums of the supplied insertion
and deletion constructor observations over the actual indexed occurrences.
The exact generation observation is

\[
G=CI+CD+(p+c+4)n+4.
\]

The four terminal charges come from indexing, the two maps and append. Append
traverses only its left list, of length `n`. There is no additional outer-entry
charge. Constructor costs can depend on the rectangle and occurrence ID. The
cost and length theorems remain true even for callbacks returning noncanonical
events: maps preserve length independently of the callback values.

Value erasure is a separate contract: each callback must return
`eventFor r kind id`. Under that premise, `rawEventsRun_value` identifies the
result with the existing `rawEvents`, retaining the full x interval, original
ID and low/high y endpoint. Existing event-identity and occurrence laws then
apply. The two LE structures need no extra equality or ordering laws here.

For constant constructor tariffs `i,d`, `rawEventsRun_cost_of_constant` gives
`G=(p+c+i+d+4)n+4`; its hypotheses are needed only for occurrences in this
input. `rawEventsRunConst_exact` supplies canonical values at those tariffs.
Empty generation costs four; a point rectangle generates both an insertion
and a deletion. Duplicate values remain distinct occurrences and are charged
separately. With `p=2,c=3,i=5,d=7`, sizes zero through three cost 4,25,46,67.

### Composition retains actual intermediate results

`sweepRun` binds the actual generated events into a measured sorter and its
returned events into `scanRun`. Its unconditional cost equation retains those
actual intermediate arguments. `sweepRun_cost_of_values` uses generation and
sorter erasure to identify them with `rawEvents rs` and `events rs`, without
discarding their observations. Primitive erasure then gives `sweepRun_value`,
the existing functional sweep result. No set law is needed merely for this
value equation; geometric correctness uses the existing lawful sweep theorem.

Generation and sorting finish before scanning. An early hit therefore removes
neither earlier generation nor earlier sorting work. For example, two duplicate
rectangles have generation cost46 under the displayed tariffs even though the
scan executes only two queries and one insertion. Callback controls deliberately
return forged events or an empty sorter result to distinguish actual binding
from recomputation of a specification. Those controls do not satisfy the
canonical value contracts and are not geometric correctness instances.

## Actual execution and the observation convention

`scanRun insertRun deleteRun queryRun entry terminal s es` returns a Boolean
paired with an observation. Each primitive is itself measured: its returned
value controls the next computation. The observation convention is explicit:

1. On an empty suffix return false with `terminal`, without calling a primitive.
2. At every visited nonempty suffix first charge `entry`.
3. For insertion, query the old state and carried x interval. A hit returns true
   immediately. A miss inserts the complete key and continues from the actual
   returned insertion state.
4. For deletion, delete the complete key and continue from the actual returned
   deletion state, without querying.

A hit pays neither insertion, suffix, nor terminal charges. An exhausted run
still performs the final event's update before reaching the empty suffix. The
existing source discussion distinguishes this final-update convention from the
AFP Boolean algorithm; equal answers do not identify different operation traces.
Event generation and sorting occur before this executor and are not charged by
its observation.

The definition needs only zero and addition. The hit equation needs the zero
laws, and additive reweighting needs monoids. Commutativity is never required
for the observation carrier. In particular, a finite word of callback tokens
retains execution order. Natural-number bounds use an additive projection
`h : C →+ Nat`; this is where nonnegative scalar comparison enters.

### Branch and value laws

`scanRun_nil`, `scanRun_insert_hit`, `scanRun_insert_miss` and `scanRun_delete`
state the branch equations. The hit observation is exactly `entry + queryCost`.
The miss and deletion equations retain the actual primitive result in the next
state, including when costs depend on the input state.

`scanRun_value` assumes primitive value erasure to the chosen insertion,
deletion and query functions at every primitive input. It concludes that the
measured result's Boolean is the existing `scan` result. This raw theorem needs
no valid event schedule, set law, coordinate linear order, geometric theorem,
or validity invariant. The existing geometric correctness theorem can then be
used by a lawful concrete client, as `measuredSweep_correct` demonstrates.

`scanRun_reweight` proves that applying an additive homomorphism to the final
observation agrees with running the same executor with reweighted primitives
and control charges. The proof preserves both returned values and the order of
addition. It does not identify distinct observation models or give machine-time
meaning to a chosen tariff.

## Executed operation counts

`scanCounts` instantiates this same executor with `Nat × Nat × Nat`, ordered
as query, insertion and deletion counts. The primitive charges are respectively
`(1,0,0)`, `(0,1,0)` and `(0,0,1)`; both control charges are zero. Write its
result as `(b,(Q,I,D))`.

The public count branch equations follow the measured branches. A hit gives
`(true,(1,0,0))`. A missed insertion adds one query and one insertion to the
continuing result. A deletion adds only one deletion. Therefore

\[
Q=I+\begin{cases}1&b=\mathrm{true},\\0&b=\mathrm{false}.\end{cases}
\]

This is `scanCounts_queries_eq`: the successful query is exactly the query not
followed by insertion. It applies to arbitrary raw event lists and initial
states. Repeated insertion of an already-present complete key still counts as
an executed insertion; cardinality changes are a different observation.

`kindCount` counts scheduled events of a selected kind. Then
`scanCounts_le_scheduled` proves `Q,I ≤ kindCount insert es` and
`D ≤ kindCount delete es`. If the result is false, `scanCounts_of_false` proves
the exact scheduled triple. It uses actual exhaustion, rather than assuming
that a full-prefix mathematical witness was reached.

For `n` input occurrences, `kindCount_rawEvents` proves that indexed generation
produces exactly `n` insertions and `n` deletions. `kindCount_events` transfers
these equalities through the existing sorting permutation. Duplicate rectangle
values do not alter either equality. Consequently `scanCounts_events_le` gives
`Q,I,D ≤ n`, and `scanCounts_events_of_false` gives `(Q,I,D)=(n,n,n)` on
exhaustion. No sort-cost claim is needed for this permutation argument.

### Exact scalar tariffs

For constant primitive charges `q`, `i`, `d`, per-event entry charge `e` and
terminal charge `t`, `scanRun_constant_cost` proves

\[
W=Qq+Ii+Dd+(Q+D)e+
\begin{cases}0&b=\mathrm{true},\\t&b=\mathrm{false}.\end{cases}
\]

Every visited insertion queries once and every visited deletion deletes once,
so `Q+D` counts visited events. The terminal term is paid exactly on exhaustion.
This identity includes empty input and early return. Constant charges in a
client fixture are declared observations, not claims that strict-list or AVL
primitives have constant implementation cost.

## A conditional scan bound from primitive bounds

`scanRun_cost_le` uses an allowed-key predicate and a state invariant. The
premises are local: the input events have allowed complete keys; the initial
state satisfies the invariant; actual insertion/deletion results preserve it
for allowed keys; and the projected costs of the three primitives are bounded
on those keys and invariant states. The query premise uses the interval
projection of the same complete key. No premise asserts a whole-scan bound.

For primitive bounds `B_Q`, `B_I`, `B_D`, the theorem concludes

\[
h(W)\le |es|\,h(e)
 +N_I(es)(B_Q+B_I)+N_D(es)B_D+h(t),
\]

where `N_I` and `N_D` are the scheduled kind counts. The proof follows the
actual branches and invokes the induction hypothesis only at a primitive's
returned state. A hit can be bounded by the larger scheduled right side because
all scalar charges are natural numbers. The right side counts potential suffix
work for an envelope; it does not report that work as executed.

`scanRun_events_cost_le` specializes the result to the canonical schedule:

\[
h(W_{\mathrm{scan}})\le 2n\,h(e)+n(B_Q+B_I)+nB_D+h(t).
\]

The caller still supplies primitive bounds and their invariant/allowed-input
contracts. For example, a future concrete client can keep its complete-key
observation within the finite input-key set and combine a valid representation
with that support invariant. Merely postulating a bounded whole scan or a
cardinality invariant not closed by the actual primitives would not discharge
these premises.

Positive empty-state costs matter. At `n=0`, the terminal charge can be positive;
an all-input pointwise bound omitting it is false. A future logarithmic primitive
bound also needs a justified positive term, such as
`1 + Nat.clog 2 (m+1)`, since the logarithm alone is zero at `m=0`. The final
asymptotic theorem must separately handle small inputs and its precise domain.

## Active complete-key cardinality

For any prefix length `k`, `activeKeys rs k` is the image of
`{i : Fin rs.length | Active rs k i}` under `occurrenceKey rs`. The domain is
finite, and the existing occurrence-key map is injective because it retains the
input index. The new results are:

| Result | Conclusion |
| --- | --- |
| `activeKeys_finite` | The active complete-key set is finite. |
| `activeKeys_ncard_eq` | Its cardinality equals the number of active occurrences. |
| `activeKeys_ncard_le` | Its cardinality is at most `rs.length`. |
| `stateAfter_take_observe_finite` | The existing exact prefix observation transfers finiteness through `DeleteLaws`. |
| `stateAfter_take_observe_ncard_eq` | A lawful full-prefix state observes exactly the active-occurrence cardinality. |
| `stateAfter_take_observe_ncard_le` | The observed full-prefix cardinality is bounded by the input length. |

These results need only LE on x and LinearOrder on y, with the state universe
independent. Prefix lengths may exceed exhaustion. The state transport starts
from the lawful empty state and concerns the mathematical full update fold.
It does not assert that a state after an earlier hit was reached by the scan.
The existing `ReachedMisses` condition retains that role.

For two equal rectangles, the full prefix after both insertions has two complete
keys and only one projected interval. Its cardinality is two even though the
actual scan returns at the second query, before the second insertion. The
connected case pairs these facts explicitly. No injectivity of `keyInterval`
is asserted.

### Strict complete keys and balanced node counts

`balanced_observe_ncard_eq_numNodes` identifies the observed complete-key set's
cardinality with the concrete tree's node count under strict inorder. The proof
identifies the set with the finite set of inorder elements, uses strictness to
exclude duplicates, and reuses inorder length and cached-erasure node-count
preservation. Neither cache correctness nor shape balance is needed for this
equality. Omitting strictness is false: a two-node raw tree repeating the same
complete key has observed cardinality one.

For the selected balanced implementation, the existing set laws preserve strict
inorder at every full update prefix. `balanced_stateAfter_take_numNodes_eq`
therefore identifies its node count with the number of active input occurrences;
`balanced_stateAfter_take_numNodes_le` bounds it by `rs.length`. These theorems
retain the existing linear x order and bottom required by the concrete maximum
annotation, and a separate linear y order. They cover arbitrary prefix lengths,
including after exhaustion. For two duplicate rectangles, the full-prefix node
counts are 0,1,2,1,0, while the actual scan stops before the second insertion.

This closes the prefix cardinality bridge. The future primitive-cost envelope
also needs the bound on every admitted invariant state reached by its measured
updates. A support invariant restricting observed keys to the input's finite
occurrence-key range supplies that connection once measured erasure and update
costs are available. Cardinality and logarithmic height alone still do not
establish an operation-cost bound.

## Independent connected cases

The expectations were derived from the existing scan, schedules and geometry
before reading the new implementation. The Lean clients use the public branch,
erasure, count, bound and cardinality theorems as well as the existing concrete
rectangle schedules. With primitive charges `q=2`, `i=3`, `d=5`, entry `e=7`
and terminal `t=11`, they establish:

| Case | Result | `(Q,I,D)` | Scan observation |
| --- | --- | --- | ---: |
| Empty input | false | `(0,0,0)` | 11 |
| Singleton point | false | `(1,1,1)` | 35 |
| Two or three identical squares | true | `(2,1,0)` | 21 |
| Two rectangles separated in x or y | false | `(2,2,2)` | 59 |
| Hit after a completed insertion/deletion pair | true | `(3,2,1)` | 45 |
| Raw deletion with an always-true query supplied | false | `(0,0,1)` | 23 |
| Raw repeated-key insertion, with every query missing | false | `(2,2,1)` | 47 |

A separate state-dependent sentinel starts at 2. Its insertion returns 21,
deletion returns 2101, and the next query succeeds only at the required returned
state. The actual primitive costs are 3, 12, 121 and 2102; three entry charges
give total 2259. The theorem holds for an arbitrary skipped suffix. Reversing
the updates gives 2011, and querying after the first insertion hits too early.
Thus Boolean agreement alone cannot conceal the wrong execution.

The same sentinel is instantiated with `FreeAddMonoid` tokens. Its exact word
records entry, query at 2, insertion returning 21, entry, deletion returning
2101, entry, and the successful query at 2101. There is no terminal, successful
insertion, or suffix token. An explicit noncommutation example prevents an
accidental commutative-observation interpretation. Lifted coordinate/state
clients check that the raw measured theorem does not collapse universe levels.

## Remaining C05-090 work and acceptance boundary

1. Supply the complete selected tariff for the actual source merge sort. Its existing split/comparison
   observations do not charge every length test, comparator implementation,
   recursive entry or constructed list cell. Account for the selected broader
   model explicitly before using it as the sorting cost of the whole pipeline.
2. Measure the chosen balanced interval insertion, predecessor extraction,
   deletion, smart reconstruction, rotations and one-branch overlap query.
   Derive costs from those recurrences and the actual cache/comparison tariff.
3. Combine the established strict node-count/cardinality correspondence with
   admitted support invariants, measured-operation bounds and the existing AVL
   height results. A valid cache or logarithmic height by itself does not bound
   update work.
4. Instantiate the measured pipeline with those actual stage bounds and prove the
   conditional `O(n log n)` conclusion with small-input cases and precise cost
   assumptions. No allocation, physical-sharing, bit-cost or host-runtime
   theorem follows automatically from this source observation model.

These bounded components have receiving source acceptance under
[issue #659](https://github.com/VladimirMarko/conaled/issues/659), with exact
validation and review identities in [CTB](../textbooks/CTB.json). They do not
qualify the complete C05-090 row. C05-085 is separately qualified by its concrete
balanced interval implementation. The earlier author whole-library execution
retains its UNKNOWN outcome; independent receiving validation resolves the
receiving gate without changing that history. Any later local delta and producer
checkpoint remain separately subject to their own acceptance gates.
