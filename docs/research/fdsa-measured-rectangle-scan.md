# Measured rectangle generation, sorting, scan and active keys

This paper records bounded progress on **CTB-24 / FDSA-5-90**, the conditional
rectangle-intersection complexity obligation in the
[canonical Chapter 5 ledger](../history/textbooks/checkpoint-012/books/fdsa/records/research/coverage/fdsa-control/research/chapter05-obligations.md).
It continues the [functional sweep proof](fdsa-rectangle-sweep.md) for the
algorithm on printed page 76 of the July 27, 2026 FDSA edition. The exact source
and its reading limits remain recorded in the existing textbook owners. This is
a fresh local cost derivation, not an assertion that an AFP session was run.

The development implements measured event generation, the actual source sorter
with a complete declared tariff, and an early-return scan. It proves their
erasure and cost/count laws, derives a scan envelope from
primitive bounds, and proves the active complete-key cardinality bound. One
measured pipeline binds the returned generation and sorting results into the
scan. Generic complete-annotation repair/update
costs have since been implemented in the
[height-update owner](fdsa-height-updates.md#implemented-measured-local-repairs-and-updates).
The concrete overlap query, field-counted key comparator and complete balanced
pipeline, closed admitted support/height invariant and final source-work
asymptotic theorem are implemented below. **FDSA-5-90 is qualified under
[receiving issue #660](https://github.com/VladimirMarko/conaled/issues/660).** The current
balanced interval-tree implementation is separately described in
[its paper](fdsa-balanced-interval-tree.md); FDSA-5-85 qualification does not
supply measured operation costs.

## Owners and reused interfaces

| Owner | Responsibility |
| --- | --- |
| [Measured indexing](../../Applications/Resources/ListIndex.lean) | Actual occurrence indexing, arbitrary starting index, exact pair/successor and invocation tariffs. |
| [Measured events](../../Applications/Search/RectangleSweep/MeasuredEvents.lean) | Shared generation, exact costs, reached lexicographic comparisons, actual measured sorting and once-bound generation/sort/scan composition. |
| [Full merge work](../../Applications/Resources/ListMergeWork.lean) | Actual measured comparator, selected recursive branch, cons/invocation charges and exact or bounded comparison tariffs. |
| [Full source-sort work](../../Applications/Resources/SourceMergeSortWork.lean) | Reused length execution, measured alternating split, actual children/merge, complete declared tariff and size/logarithmic bounds. |
| [Measured scan](../../Applications/Search/RectangleSweep/Measured.lean) | The actual measured executor, value erasure, additive reweighting, exact counts and primitive-cost envelope. |
| [Active cardinality](../../Applications/Search/RectangleSweep/ActiveCardinality.lean) | Finiteness, occurrence/cardinality equality, input-length bound, lawful prefix-state transports and the strict balanced node-count bridge. |
| [Connected cases](../../Examples/MeasuredRectangleSweep.lean) | Existing rectangle schedules, positive empty cost, early return, deletion, returned-state sequencing, ordered observations and duplicate cardinalities. |
| [Generation cases](../../Examples/MeasuredRectangleEvents.lean) | Occurrence indexing, raw/sorted order, exact input-dependent generation costs, callback-result controls and pipeline clients. |
| [Sorting-work cases](../../Examples/SourceMergeSortWork.lean) | Small-input costs, actual comparator branches, different costs for equal outputs, asymmetric charges, instability, event traces and the actual pipeline. |
| [Measured interval query](../../Applications/Resources/IntervalTree.lean) | Actual interval projection, short-circuit overlap, cached maximum read, one-child search, raw erasure and structural work. |
| [Concrete balanced pipeline](../../Applications/Search/RectangleSweep/MeasuredBalanced.lean) | Reached complete-key field tests, four-event complete annotation, concrete updates/query and actual generation-sort-scan composition. |
| [Query cases](../../Examples/MeasuredIntervalQueries.lean) | Fixed paths, malformed summaries, callback controls, varying work, weak correctness and independent universes. |
| [Concrete pipeline cases](../../Examples/MeasuredBalancedRectangleSweep.lean) | Complete occurrence updates, rotations/ties, exact actual sort/scan stages, small inputs and geometry. |
| [Complete sweep complexity](../../Applications/Search/RectangleSweep/Complexity.lean) | Finite admitted support, closure under actual updates, node/height and primitive envelopes, full-input work and ordinary asymptotics. |
| [Logarithmic query work](../../Applications/Resources/IntervalTree/Logarithmic.lean) | Actual shape balance and global callback costs give integer and ordinary real logarithmic query work. |
| [Complexity clients](../../Examples/MeasuredBalancedComplexity.lean) | Support and strictness controls, stale-cache shape bounds, ordinary operation specialization, small-input envelopes and complete-family consumers. |
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

## Complete declared sorting tariff

The actual event sorter is the existing order-preserving alternating source
merge sort, whose value and permutation laws already serve the functional
sweep. Its earlier measured owner records split visits and merge comparisons.
Those narrower observations remain unchanged. The new
`Resources.SourceMergeSortWork` prices the missing operations explicitly,
using an actual callback `cmpRun : α → α → Measured Bool Nat`.
No equality or ordering on the payload type is needed for raw execution,
erasure, occurrence preservation or the generic work bound.

The selected source model charges one for a recursive invocation, a constructed
cons, a successor used to compute length, and the sort's Nat comparison with
one. A reached comparator contributes its own measured observation. Pattern
matching, projections, pairing, Boolean branch selection, returning an existing
suffix and observation bookkeeping are uncharged. Cons charges count source
construction events; they do not measure physical allocation, sharing or memory.

| Component | Actual measured execution and exact local work |
| --- | --- |
| Length | Evaluate existing `SymmetricCosts.lengthRun` once, obtaining `(n,n+1)`, then price its invocation count plus returned successor count. The result is `(n,2n+1)`. `lengthRun_cons` proves the returned successor and cost increment of two from the existing recursion. |
| Alternating split | Empty cost one; singleton cost two; a pair binds the returned recursive halves, constructs two cons cells and adds three. Exact work is `n + n/2 + 1`, bounded by `2n+1`. |
| Merge | An empty-side invocation returns the other list for one. Otherwise execute the comparator once, follow its returned Boolean, bind the selected child's actual list and construct one cons. The reached step costs callback work plus child work plus two. |
| Sort | The actual returned measured length determines the base test. The base costs `2n+3`; the recursive branch additionally binds one split, both sorts of its returned halves and the merge of their returned results. |

The merge value is `List.merge` with Boolean comparator
`fun x y => (cmpRun x y).1`. With `m` actual comparisons, a constant callback
tariff `C` gives exactly `(C+2)m+1`. A uniform callback upper bound gives the
corresponding inequality, and the established arbitrary-comparator comparison
bound yields `(C+2)(|xs|+|ys|)+1`. Empty sides retain their terminal charge.
No callback is evaluated for an empty side and no copied-cell charge is added
for the returned surviving suffix. Input-dependent callback observations are
retained by the execution; their global bound is an independent hypothesis.

### Deriving the whole-sort bound

Let `D(n)` be the existing `Resources.SourceMergeSort.splitSizeCost`: it is
zero at zero and one, and satisfies
`D(n)=n+D((n+1)/2)+D(n/2)` for `n>1`. Its existing proof gives
`D(n) ≤ n*Nat.clog 2 n`. This is a reused size recurrence; it is not a second
execution inserted into the new sorter.

Write `W(xs)` for the actual new observation and assume
`∀ x y, (cmpRun x y).2 ≤ C`. Both alternating halves of a recursive input are
nonempty, shorter than the input, and have total length `n`. Their actual
sorted outputs retain those lengths by the unconditional permutation theorem.
The remaining work at that node is bounded by

\[
(2n+3)+(2n+1)+((C+2)n+1)=(C+6)n+5.
\]

The three terms are length/entry/test, split, and merge. Strong induction on
length therefore establishes the nonempty strengthening

\[
n>0\quad\Longrightarrow\quad W(xs)+5\le(C+6)D(n)+10n.
\]

At the singleton, both sides equal ten. At a recursive node, the two child
offsets of five pay the node's five and the outer five; `a+b=n` combines the
linear terms, and the `D` recurrence combines the remaining terms. This
argument derives the operation bound from executed stages; no interface field
assumes a whole-sort bound. The empty input costs three and is excluded from
this strengthened statement, which would otherwise assert `8≤0`.

The all-input consequence is

\[
W(xs)\le(C+6)n\,\operatorname{clog}_2(n)+10n+3.
\]

At `n≥2`, use the stronger nonempty result and `1≤Nat.clog 2 n` to obtain
`W(xs)≤(C+16)*(n*Nat.clog 2 n)`. The existing Growth bridge then gives ordinary
real `O(n log₂ n)` for every input family of length `n` and fixed uniform `C`.
An unbounded Nat-dependent callback tariff does not satisfy this global premise
merely because a finite example happened to reach small arguments.

### Reached event comparisons and the actual event sorter

`eventCompareRun` compares the actual fields in this order: y less-than,
y equality, kind-rank less-than, kind-rank equality, and ID non-strict order.
It stops as soon as the result is determined. One callback invocation and each
reached primitive test cost one; projections and the two-case kind rank are
uncharged. The returned Boolean is exactly `decide(e.key ≤ f.key)` for the
existing lexicographic key. X payloads are never inspected, so only LE on x
and linear order on the independent y carrier are required.

The actual branch costs are two for smaller y, three for greater y, four for
equal-y insertion before deletion, five for the converse, and six when equal
y and kind require the ID test. Equal IDs still pay six. Thus the uniform
callback bound is six, while shorter executions retain their actual costs.
These primitive comparisons use an abstract unit model. They do not establish
bit complexity for unbounded IDs or an arbitrary endpoint implementation.

`sortEventsRun` instantiates the measured source sort with that callback and
proves value equality with existing `sortEvents`. For `m` arbitrary events,
including noncanonical raw lists, its work is at most
`12*m*Nat.clog 2 m + 10*m + 3`. On the actual generated schedule, `m=2n`, giving

\[
S(2n)\le24n\,\operatorname{clog}_2(2n)+20n+3.
\]

The connected examples retain the independent exact traces. Unit-comparator
sorts of `[3,1,2]` and `[3,2,1]` return the same list but cost 48 and 51.
Asymmetric callback costs distinguish the order and actual values passed to
comparisons. Constant zero callback charges still leave structural work.
Tagged equal-key records `[a,b,c]` become `[a,c,b]`, so the result does not
claim stability or idempotence. The generic erasure and bound also support
always-true and always-false comparators without claiming sortedness for them.

Replacing the earlier illustrative constant-17 sorter with the actual event
sorter gives the following pipeline observations under the existing fixture
tariffs `p=2,c=3,i=5,d=7` and scan query/insert/delete/entry/terminal
`2/3/5/7/11`:

| Rectangles | Generation | Actual sorting | Actual scan | Result | Total |
| --- | ---: | ---: | ---: | --- | ---: |
| Empty | 4 | 3 | 11 | false | 18 |
| Point singleton | 25 | 28 | 35 | false | 88 |
| Duplicate squares | 46 | 92 | 21 | true | 159 |
| Triple squares | 67 | 179 | 21 | true | 267 |

The last two scans stop at the same second insertion query, after different
amounts of generation and sorting have already occurred. These fixture
update tariffs still do not establish costs for the concrete AVL operations.

## Actual scan and its observation convention

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

This closes the prefix cardinality bridge. The admitted-state argument below
also proves the bound on every state satisfying a closed finite-support
invariant, independently of whether it equals a mathematical full-prefix state.
The separately implemented actual measured operations supply the work bounds;
cardinality and logarithmic height alone would not establish them.

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

## Actual measured interval queries and concrete balanced sweep

The query and concrete pipeline complete the next bounded FDSA-5-90 implementation
step. They reuse the measured carrier, root reader, generic height-balanced
updates, direct pure query, existing interval-set laws and actual source sorter.
No new resource carrier or alternative sweep executor is introduced. The earlier
primary-source reading attribution is unchanged; this is a local derivation.

### The actual query and its weak assumptions

`Resources.IntervalTree.overlapRun leRun query stored` executes
`stored.low ≤ query.high` first. Only its returned true reaches
`query.low ≤ stored.high`; the returned second Boolean is the answer. The helper
has no entry charge. With endpoint cost bound E, its work is at most2E.
`maxHiRun` binds the actual root reader with empty summary `(0,⊥)` and freely
projects its second coordinate. Its work is exactly1; no height or maximum fold
is executed.

`searchRun` charges one invocation, including nil. A reached nonempty node binds
its interval projection exactly once, then the actual overlap helper. A hit
returns immediately. A miss bypasses an empty left child without a maximum read.
For nonempty left, one maximum read and an actual pruning comparison select one
original child. Failure in that child never retries its sibling. Arbitrary
returned projection and comparison values control this raw program.

For global projection and endpoint bounds P and E, the structural theorem is

`queryWork(t) ≤ (P + 3*E + 2) * height(t) + 1`.

At a nonempty level the envelope includes one projection, at most three endpoint
comparisons, one entry and at most one root read. Only one original child is
visited, so its structural height is below the parent's. Nil supplies the final1.
This proof assumes neither value erasure nor cache validity, order or balance.
It refers to actual shape height, never a possibly forged stored height.

Raw execution needs LE and Bot on endpoints; value erasure additionally needs
DecidableLE and the pointwise callback value equations. Key and endpoint
universes are independent. Through erasure, existing soundness gives an original
stored-key overlap witness without tree invariants. Completeness retains only
valid maxima and weak nondecreasing projected lows, under the existing linear
endpoint order. Stored-height correctness, balancing and strict key order remain
unnecessary for that query theorem. The strict-key adapter separately requires
its low-projection compatibility law.

The connected query cases retain the fixed nil/singleton/RR paths; stale and
underestimated maxima; wrong stored height99; empty-left bypass; bottom-valued
nonempty trees; unbalanced/repeated-key trees; and incompatible low projections.
False first/second comparison answers and an altered projected interval expose
actual returned-value control. The RR right-hit path has exact constant work
`2*p + 5*e + 3`: two projections, five comparisons, one root read and two entries.
A varying example costs24; its projection tariff is unbounded globally, and a
separate theorem rejects a fictitious uniform P. Lifted keys and lifted endpoints
exercise both universe-separation directions.

### Complete-key comparison and concrete update bounds

The complete key is still `(interval, occurrence ID)` with the ordinary
lexicographic order. `keyLtRun` charges entry1 and each reached test in the order
low<, low=, high<, high=, ID<. Its actual answer is `decide (a<b)`. The five
short-circuit cases cost2,3,4,5,6; six is an envelope, not the cost charged to
every comparison. This is distinct from the event comparator, which compares
y/kind/ID and uses a nonstrict final ID test.

The concrete complete combine binds four actual unit operations: height maximum,
successor, child endpoint maximum and maximum with the payload's high endpoint.
The height and interval projections costzero. Thus H=0,K=4,C=6 specialize the
generic update results, while P=0,E=1 specialize the query:

| Actual operation | Raw structural-height bound |
| --- | --- |
| Insertion | `43*h+8` |
| Rightmost extraction | `31*h+1`, strengthened to `31*h` for nonempty input |
| Deletion | `43*h+1` |
| Overlap query | `5*h+1` |

Raw value erasures target the existing balanced operations and direct query.
Full validity preservation follows from those erasures and the existing seven
set laws. No rotations or set algebra are reproved in the specialization.
The earlier atomic-comparison examples retain their separate33h bounds.

The fixed complete-key history costs8,34,14,14,14 (total84), while adding a third
equal-interval occurrence rotates for70 and deleting its root costs27. Distinct
point keys have smaller/larger insertion24/27, absent deletion17/20 and matching
deletion14. The four complete-annotation insertion rotations cost56/50/60/60;
the two deletion ties cost43/40. Full returned trees preserve the independently
specified summaries and occurrence identity.

### One actual complete pipeline and exact stage clients

The concrete `scanRun` supplies these actual operations to the existing scan
with entry1 and terminal1. `sweepRun` supplies pair1, successor1 and actual event
constructor1 to the existing generation/sort/scan driver. Neither composition
adds a wrapper charge. Its value is the existing `balancedSweep`, and the
distinct-occurrence closed-rectangle intersection theorem transfers directly,
including boundary contact and duplicate values at independent coordinate
universes.

For n input rectangles the exact stage law is

`sweepWork = 8*n+4 + sortEventsRun(rawEvents rs).cost
                         + scanRun(nil, events rs).cost`.

Generation and sorting are paid before an early scan return. The finite clients
use the public measured two/four/six-element sorting equations, identify the
actual returned canonical schedule, check the concrete scan on that schedule,
then apply the public value and cost composition laws. The inputs below have
Nat x and Int y; square is[0,1]×[0,1], point is[2,2]×[3,3], xGap is[2,3]×[0,1]
and yGap is[0,1]×[2,3]. These are the specified fixtures, not the older differently
placed Int x-gap pair.

| Input | Generation | Sorting | Scan | Answer / total |
| --- | ---: | ---: | ---: | --- |
| Empty |4|3|1|false,8|
| Square |12|26|26|false,64|
| Point |12|28|26|false,66|
| Two identical squares |20|92|14|true,126|
| Three identical squares |28|179|14|true,221|
| Square, xGap |20|92|73|false,185|
| Square, yGap |20|79|51|false,150|
| yGap, square |20|81|51|false,152|
| Square, yGap, yGap |28|161|39|true,228|

The first insertion costs10; a root-overlap hit adds4 and skips the update and
suffix. One exhausted singleton pair costs10+15+terminal1=26. For xGap the
second event costs1+query4+insertion27=32, so the full scan is
10+32+15+15+1=73. The y-separated pairs each cost25 before the final1. In the
post-deletion hit, the scan is25+10+4=39. All expectations were derived before
implementation. None licenses dropping positive empty/singleton overhead.

## Closed admitted support and logarithmic height

Fix an input list `rs` of length n and put

\[
U=\operatorname{range}(\operatorname{occurrenceKey}(rs)),\qquad
\operatorname{Admitted}(rs,t)\iff
  \operatorname{Balanced.Valid}(t)\ \land
  \operatorname{setTree}(\operatorname{erase}(t))\subseteq U.
\]

`inputKeys` names U in the complexity owner. It is a proof-only set; neither
the executor nor a callback constructs or enumerates it. Occurrence-key
injectivity identifies its finite cardinality with n, even for equal rectangle
values. `mem_events_iff` and `completeKey_eventAt` show that every scheduled
event carries an allowed key. This includes events skipped by an early hit.

The empty set laws give `admitted_nil`. The insertion set law identifies the
actual returned observation with insertion of the supplied complete key into
the old observation. Thus an allowed key and an admitted input imply an admitted
returned state. Deletion only removes an observed key, so its closure theorem
allows an arbitrary deletion key, including a key outside U. Both proofs first
transport through the actual measured operation's erasure; validity comes from
the existing balanced set laws. No prefix theorem or unexecuted state is
substituted for the actual returned state.

Strict complete-key inorder, a component of full validity, supplies

\[
\operatorname{numNodes}(t)
=\#\operatorname{setTree}(\operatorname{erase}(t))
\le\#U=n.
\]

This is the existing `balanced_observe_ncard_eq_numNodes` followed by finite-set
cardinality monotonicity. Weak interval-low ordering alone would not suffice:
repeated complete keys can make distinct-key cardinality smaller than the node
count. Two equal rectangles with IDs0 and1 do supply two distinct complete keys.
Their valid two-node state is admitted for the two-element input and cannot be
admitted for the singleton input. An ID1-only leaf is also admitted for the
duplicate input, regardless of the full-prefix schedule's first ID0 insertion.

The existing ceiling-power proof for every natural balance tolerance d gives

\[
2^{\lceil h/(d+1)\rceil}\le\operatorname{numLeaves}(t).
\]

The new integer corollary in the existing height owner takes the natural floor
logarithm, then uses `Nat.log_le_clog` and the already proved rounding inequality
to obtain

\[
h(t)\le(d+1)\operatorname{clog}_2(\operatorname{numNodes}(t)+1).
\]

It uses only actual shape balance, including d=0, and no payload order or cached
height. Applying it to the erased admitted tree at d=1, using preservation of
height/node count under erasure, and applying monotonicity of the ceiling log
gives, with \(L=\operatorname{clog}_2(n+1)\),

\[
h(t)\le2L.
\]

The maximum and stored-height annotations are never read by this proof. A stale
height on a balanced shape can still satisfy the generic structural cost bound;
full admission additionally needs the complete balanced-set invariant because
it is also used for the finite-set observation and update closure.

## Complete work envelope and ordinary asymptotics

Substituting the admitted height bound into the actual concrete primitive bounds
gives insertion at most86L+8, extraction at most62L+1, deletion at most86L+1 and
query at most10L+1. The query interval may be arbitrary; it need not be projected
from an input occurrence. These are consequences of proved raw work recurrences,
not charges assigned to a whole update or search.

Instantiate the existing scan theorem with allowed set U, invariant Admitted,
entry/terminal costs1, and the closure and primitive bounds just established.
For **every admitted starting state**, the scheduled scan has work at most

\[
2n+n\bigl((10L+1)+(86L+8)\bigr)+n(86L+1)+1
=182nL+12n+1.
\]

The generic scan theorem follows actual returned states and actual early return.
This expression is a nonnegative opportunity envelope, so it need not execute
skipped updates to be an upper bound. The concrete full sweep starts at nil,
whose admission was proved independently.

Adding generation8n+4 and the actual sort bound yields the all-input theorem
`sweepRun_cost_le`:

\[
W(rs)\le F(n):=
24n\operatorname{clog}_2(2n)
+182n\operatorname{clog}_2(n+1)+40n+8.
\]

Generation and sorting remain in this expression even when the scan returns
early. The natural ceiling log at0 is0. Consequently F(0)=8, exactly the proved
empty execution. The first small bounds and their scan components are:

| n | L | Scan envelope | F(n) |
|---:|---:|---:|---:|
|0|0|1|8|
|1|1|195|254|
|2|2|753|912|
|3|2|1129|1436|

The preceding nine exact executions retain their original costs. These envelopes
bound them without altering their fixtures or charging a shorter comparator
branch as though all six tests were reached.

For every n, `Nat.le_pow_clog` and the power adjunction give
\(\operatorname{clog}_2(2n)\le\operatorname{clog}_2(n)+1\).
For n≥1, also n+1≤2n, so
\(\operatorname{clog}_2(n+1)\le\operatorname{clog}_2(n)+1\).
First using monotonicity with n+1, and then L≥1, gives

\[
F(n)\le206nL+64n+8\le278nL\quad(n\ge1).
\]

Alternatively put \(J=\operatorname{clog}_2(n)\). For n≥2, both logarithms in
F(n) are at most J+1, and J≥1. Since8≤4n,

\[
F(n)\le206nJ+246n+8\le456nJ.
\]

`sweepRun_isBigO` applies the existing numerical ceiling-log bridge to an
arbitrary input family `inputs n` with length exactly n. It concludes ordinary
real-cast \(O(n\log_2 n)\) work for the actual measured full executor. The bridge
can use constant912 beyond n=2, from the natural coefficient456 and
\(\operatorname{clog}_2(n)\le2\log_2 n\). It does not claim an all-n bound by
the zero-vanishing n log n expression. Repeated-square families supply a concrete
consumer for every input length, including0 and1.

The separate generic operation results use
`Resources.isBigO_logb_succ_of_clog_bound`: an eventual bound a·clog₂(n+1)+b
implies ordinary \(O(\log_2(n+1))\), with coefficient2(a+b) beyond max(N,1).
This bridge absorbs the additive term where the logarithm is positive; it does
not introduce the extra factor n of the full-sweep theorem. Shape balance and
global callback cost bounds remain explicit in those operation families.

## Qualification and remaining book work

The measured source-work composition for the selected balanced pipeline is now
implemented. The source convention gives unit observations to the specified
endpoint/ID tests and arithmetic events; it supplies no allocation,
physical-sharing, bit-cost or host-runtime theorem. Functional geometric
correctness, finite-work bounds and asymptotics remain separately named results.

The earlier measured generation/scan/cardinality components were accepted under
[issue #659](https://github.com/VladimirMarko/conaled/issues/659), together with
FDSA-5-85. The cumulative source now implements the complete selected FDSA-5-90
cost composition, qualified under
[issue #660](https://github.com/VladimirMarko/conaled/issues/660). That issue owns
the exact receiving build/audit, final verification and independent acceptance
records. Chapter 5 is 92/94; FDSA-5-92 and FDSA-5-93 remain open.
The old author's whole-run UNKNOWN outcome remains a historical fact; receiving
acceptance uses its own isolated execution and exact source identity.
