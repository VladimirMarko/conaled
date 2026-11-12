# Retained-state incremental shortest paths

Issue [#111](https://github.com/VladimirMarko/conaled/issues/111) delivers a native
LPA* loop, independent shortest-distance correctness, ordered repair, and an
operation-producing comparison with a specified fresh A* implementation. The
public interface is `Session.begin`, `Session.advance`, and `Session.observe`.
Repair retains `g`, `rhs`, and the inconsistent worklist. It does not rerun the
fresh comparator or globally settle every distance before returning.

## Baseline and source

The implementation baseline is conaled
`55944ef88b74472d1d3af9d719040f86fe1c342f`, initially clean. The textbook revision
used here is the integrated ADWH code at that commit, not a separate uninspected
archive or a historical checkpoint. Lean is `leanprover/lean4:v4.35.0`; Mathlib is
`56a005855ea17e0b0958f73ec801ae140b0a1679` from `lake-manifest.json`. No dependency,
toolchain, or pre-existing search API changes are required.

The primary algorithm source is Koenig, Likhachev and Furcy,
[*Lifelong Planning A*](https://idm-lab.org/bib/abstracts/papers/aij04.pdf),
section 2 and Appendix A, especially printed pages 41–51. The inspected PDF has
420965 bytes and SHA256
`12e451bf000280f892ace112cc6c480116bb302e6eec203586e8e863989b3903`.
The proof preparation read the complete appendix. Its termination argument
counts expansions on a finite carrier; it does not require rational numbers
to be well-founded. Its path reconstruction discussion needs a reachable-goal
premise. The implementation instead returns distance, including infinity with
a proof that no finite walk reaches the goal. The later Theorem 10 comparison
is not used as a primitive-operation bound.

[*D* Lite](https://idm-lab.org/bib/abstracts/papers/aaai02b.pdf) applies incremental
heuristic search to navigation from a changing robot position. That workload
is outside this delivery: starts, goals, vertex identifiers, and the heuristic
remain fixed across a `Session`.

## Workload and observation

[`Semantics.lean`](../../Applications/Search/Incremental/Semantics.lean) defines
vertices `Fin n`, weights `WithTop ℚ`, and `Positive`: each edge is strictly
positive or infinite. Positive self-loops are allowed. Infinity represents a
blocked edge. `successors` and `predecessors` in
[`Core.lean`](../../Applications/Search/Incremental/Core.lean) provide finite
access by scanning the vertex set; this representation does not promise sparse
constant-time adjacency queries.

An assignment carries source, destination and new cost. A batch is an ordered
list; repeated writes use the last value. New rational denominators are allowed.
All written costs must be positive or infinite. The fixed rational heuristic
is nonnegative, zero at the goal, and consistent with the final graph of each
repair. Intermediate graphs inside a batch need not satisfy consistency:
assignments refresh destinations but do not run search between writes.

`DistanceResult` uses the existing `RationalCost.Walk` semantics. A finite
observation has an attaining walk and is no larger than every goal-reaching
walk. An infinite observation means no such finite walk exists. No equality of
tie-selected paths is claimed. `Session n start goal h` fixes endpoints and the
heuristic in its type.

## Derivation and declaration dependencies

The construction combines existing ADWH operations with new local-update and
search proofs. The following table distinguishes those contributions.

| Role | Existing declarations used | New checked step |
| --- | --- | --- |
| Ordered assignment store | `Dijkstra.Store.accum`, `accum_lookup`, `valuesAt` | `LocalRows.updateStore_lookup` and `updateStore_frame` retain write order and prove untouched entries unchanged |
| Row-fold dependency | Ordinary `List.foldr`, the preceding store law | `LocalRows.fold_congr`, `recompute_correct`, `recompute_untouched` identify exactly which cached rows can be reused |
| Bellman minimum as a fold | `Finset.inf`, finite lattice laws | `LocalRows.inf_eq_fold`, `predecessorMinimum_fold`, `rhsValue_congr_inputs` connect the literal row computation to its specification |
| Goal-directed selection | `Optimization.Thinning.argmin` and its minimum-membership facts | `select_spec`, `select_selected` expose exact minimum inconsistent vertices; keys are recomputed from current labels |
| Fresh reference search | `Heuristic.run`, `mstar_terminates`, `mstar_correct`, `observeDistance`; `PrioritySearchQueue.keyed` | `Fresh.run_total`, `Fresh.result_correct` specialize the actual closed-list search |
| Rational reference transport | `RationalCost.Scale`, `monotonic_iff`, `distance_iff` | `Fresh.scale_fits`, `compatible` collect a per-query denominator and prove exact conversion |
| Relational integration | `Relational.RelRep`, `RelSquare`, `compose` | `repairSquare`, `observationSquare`, `repairDistanceSquare_correct` compose retained repair with distance observation |

The reusable step lives in
[`LocalRows.lean`](../../Applications/Incremental/LocalRows.lean). Its fold law is
consumed by the actual search proofs `rhsValue_update_blocked` and
`rhsValue_assign_other`, through
[`Rows.lean`](../../Applications/Search/Incremental/Rows.lean). The first avoids
refreshing vertices whose incoming edge from the changed label is blocked; the
second justifies refreshing only the destination of an edge assignment. These
are derivation dependencies, rather than an unused generic wrapper.

[`IncrementalRows.lean`](../../Examples/IncrementalRows.lean) is the second
consumer: two weighted-sum rows depend on different columns. Ordered writes
5 then 7 to column 0 change row 0 from 8 to 20, while row 1 remains cached at
−4. `updated_exact` instantiates the generic correctness theorem and
`untouched_row` uses its frame result. This reusable dependency analysis can
support compiler transformations for row folds with supplied read sets. The
LPA* key order, frozen-vertex argument, and goal stopping still require
search-specific reasoning.

## State invariants, termination, and goal correctness

`Valid` states that cached `rhs` equals the one-step Bellman equation, the queue
has no duplicate vertices, queue membership is exactly `g ≠ rhs`, and `g` is
nonnegative. It does not assume globally optimal labels or successful
termination. The start rhs is always zero. The queue is a native list with
remove-and-refresh behavior; the static keyed queue's lower-priority replacement
rule would not implement arbitrary upward refresh correctly.

| Source proof obligation | Checked declarations and files |
| --- | --- |
| Appendix A Lemmas 1–3, exact rhs/worklist | `initial_valid`, `expand_valid` in [Invariant](../../Applications/Search/Incremental/Invariant.lean); `applyUpdates_valid` in [Patches](../../Applications/Search/Incremental/Patches.lean) |
| Lemmas 4–6, newly inconsistent and remaining keys | `newly_inconsistent_key`, `next_inconsistent_key`, `overconsistent_rhs` in [Keys](../../Applications/Search/Incremental/Keys.lean), including positive self-loops |
| Theorems 2–3, threshold permanence | `frozen_step`, `overconsistent_frozen`, `Trace.frozen` in [Trace](../../Applications/Search/Incremental/Trace.lean) |
| Lemma 7, finite expansion bound | `Trace.count_le_two`, `Trace.length_le`: at most two expansions per vertex in one fixed-graph episode |
| Total executable loop | `runWith_exhausted`, `runWith_total`, `run_total`, `drain_total` in [Termination](../../Applications/Search/Incremental/Termination.lean) |
| Bellman attainment and uniqueness | `bellman_walk_le`, `bellman_attains`, `bellman_correct`, `distance_unique` in [Bellman](../../Applications/Search/Incremental/Bellman.lean) |
| Lemma 8 and Theorems 4–5, early goal result | `stopped_frozen`, `frozen_correct`, `run_correct`, `complete_correct` in [Correctness](../../Applications/Search/Incremental/Correctness.lean) |
| Stateful repeated updates | `applyUpdates_append`, `repair_correct`, `Session.advance_correct` in Patches |

`Trace.length_le` is proved for any legal finite expansion trace. Exhaustion at
fuel `2*n` would allow one more selected expansion, contradicting that theorem.
Thus `complete` extracts a stopped result using a proved existence theorem;
it has no fallback, default answer, or assumed termination field.

Bellman attainment uses a strict relation on the finite vertex carrier. Positive
edge weights make predecessor labels strictly smaller. `frozen_correct` extends
an early-stopped state with an actual terminating full drain, proves the final
Bellman result, and uses permanence to show the already frozen goal was equal
to it. The public loop still returns early. The four-vertex example returns goal
distance 1 with another vertex's `g = ∞`, `rhs = 10`, and that vertex still queued.

The `2*n` theorem bounds expansions per repair episode, not scalar operations,
all repairs combined, or queue maintenance. Key monotonicity is used within a
fixed-graph episode, not across arbitrary graph patches.

## Conaled integration

[`Interpretation.lean`](../../Applications/Search/Incremental/Interpretation.lean)
relates a `RepairInput` containing a valid retained state to its semantic graph
and ordered batch. `repairSquare` produces a retained state with independent
distance correctness; `observationSquare` forgets the state and observes the
distance. `repairDistanceSquare` composes those actual implementations with
`Relational.compose`.

The existing `Incremental.Map` finite-update equation concerns observation after
an input change. It does not express the stronger retained-state invariant or
establish reuse. `Session.advance_correct` supplies that obligation here;
`applyUpdates_append` proves ordered batching before repair. Inserting repairs
between batches may produce different internal states, but both observations
satisfy the same final graph specification. `distance_unique` gives equality
when the graph and endpoints agree.

The current FirstOrder frontend can compile its supported source terms from
proved primitive interpretations. It cannot translate this recursive search
loop from arbitrary Lean. These relational squares could be supplied as a
whole-search primitive interpretation; that would not mean the compiler derived
LPA*. Generic recursive source support remains #109's scope. Transporting
complexity through interpretations remains #110's scope. No new compiler
interface or recursion axiom is introduced here.

## Costs and storage

[`Accounting.lean`](../../Applications/Search/Incremental/Accounting.lean)
defines one shared `Prices : Event → Nat`. Events count logical cell reads and
writes, comparisons, additions, multiplications, divisions, denominator access,
allocations, and branches. Both machines use the same price function.
[`Measured.lean`](../../Applications/Search/Incremental/Measured.lean),
[`RepairCosts.lean`](../../Applications/Search/Incremental/RepairCosts.lean), and
[`FreshCosts.lean`](../../Applications/Search/Incremental/FreshCosts.lean)
produce event traces while executing their branches and traversals, with
kernel-checked erasure to the ordinary implementations. `measuredRepair_fresh`
in [Costs](../../Applications/Search/Incremental/Costs.lean) proves equal
distance observations for every admitted batch.

Repair charges initialization of both label maps, ordered patch processing,
predecessor/successor scans, current-key selection, queue filtering and append,
expansions, and the final observation read. `measuredRerun` charges the same
ordered graph assignments followed by a fresh query. Fresh preparation collects
all finite weights and heuristic entries, multiplies their denominators,
materializes encoded adjacency rows and heuristic values, runs the existing
closed-list A* with `PrioritySearchQueue.keyed Path.vertex`, and decodes the
result. Every queue removal includes the reference queue's actual insertion
sort by vertex. Both literal calls to path extension in its successor routine
are charged; no common-subexpression optimization is assumed.

This is an explicit logical-cell/scalar interpretation. Finite enumeration
allocates one list cell per vertex. A materialized path record allocates three
fields, and extending its prior list allocates one cons cell per extension call.
The nonnegative scalar floor in rational encoding is charged as `divide`.
Administrative tuples and state-record packing are free; trace construction is
instrumentation and is unpriced. Rational arithmetic prices are not bit costs.
Function-map reads/writes denote logical cell operations, not a claim that Lean
closure lookup or update has constant host cost.

`retainedCells_le` bounds the retained logical graph, heuristic, two label maps,
queue identifiers, and endpoints by `n*n + 4*n + 2`. It uses queue uniqueness,
not an assumed capacity. Caller-owned input batches and event logs are separate;
the trace itself contains one event per recorded operation. Transient list and
path allocations are charged in the traces. Fresh search additionally builds
its encoded graph and paths on each query. No peak Lean heap bound is proved:
persistent function updates can retain closure chains, and allocation counts
do not imply garbage collection or deallocation behavior.

The following are exact kernel-checked computations with every event priced 1,
in [IncrementalSearchCosts](../../Examples/IncrementalSearchCosts.lean).

| Workload | Retained repair | Fresh query, including patch |
| --- | ---: | ---: |
| Four vertices, update an edge beyond the settled goal | 110 | 559 |
| Three vertices, increase an edge on the former shortest route | 641 | 429 |

Initialization plus observation in the first workload costs 445. Initial query
plus one repair therefore costs 555, and the checked comparison includes the
initial fresh query on the other side. The reuse example proves every retained
`g` label is unchanged. The adverse example changes two downstream labels and
returns distance 2; a single assignment is enough for repair to exceed fresh
search. These are bounded workload claims, not asymptotic or general amortized
speedup theorems. No scalar worst-case bound is inferred from the `2*n`
expansion theorem. Existing static-search termination and rational transport
results are reused; no ADWH complexity theorem is claimed to price this new
retained-state machine automatically.

## Checked applications and validation

The public entrypoint `SquareApplications.lean` imports the search cost,
heuristic, fresh-cost, and row-fold examples, transitively covering all new
modules. Checked applications include fractional costs, new denominators,
increases and decreases, loss/restoration of reachability, repeated writes,
empty batches, positive self-loops, equal-cost alternatives, start equal to goal,
nonzero consistent heuristics, and a batch with an inconsistent intermediate
graph but consistent final graph. Concrete facts use kernel `decide +kernel`,
not native evaluation as a proof.

Focused development checks used the pinned direnv shell, CPU 0, and the shared
build lock. The main targets were `Examples.IncrementalSearchCosts`,
`Examples.IncrementalSearchHeuristics`, `Examples.IncrementalSearchFreshCosts`,
and `Examples.IncrementalRows`. Actual execution is checked with:

```sh
direnv exec . lake env lean --run scripts/IncrementalSearchTest.lean
```

The runtime seam is initialization, ordered repair, and observation. A stale
pre-repair-result mutant failed the edge-increase assertion before the repaired
version passed. The tests also execute the fresh comparator and check the
reported bills. Runtime observations are separate from kernel correctness
proofs and do not measure elapsed-time superiority.

Final acceptance requires the coordinator's clean integrated candidate, fresh
build and exhaustive proof audit, independent Standards and Spec reviews, and
candidate verification. Focused checks alone do not discharge that gate. No
new axiom, `sorry`, native proof shortcut, dependency change, or verification
tooling change is part of this delivery.
