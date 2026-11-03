# Finite-sentinel Dijkstra

[#184](https://github.com/VladimirMarko/conaled/issues/184) reconstructs the
complete `DijkstraSentinel` source module as a client of the accepted
[Dijkstra development](adwh-dijkstra.md). It retains the raw mathematical-Int
executor and proves its correspondence with genuine infinity under the source's
explicit sufficient domain. No machine-integer implementation is introduced.

## Execution and correspondence

`Applications/Dijkstra/Sentinel/Encoding.lean` retains raw links, fresh vertices,
selection, relaxation, start, step and fixed-count execution. `rawDijkstra` runs
exactly `n-1` updates. In particular, `rawSum sentinel d w` returns the sentinel
only when **the edge weight** equals it; otherwise it computes `d+w`. There is
no additional guard on `d`, saturation or replacement by the accepted executor.
Equal relaxation distances keep the old parent.

Raw scores use standard `Int ×ₗ Nat`. `rawScore_le_iff` and `rawScore_decide`
prove the source order and decidable guard correspondence. Selection reuses
`Optimization.Thinning.argmin`; encoded score comparisons prove exact choice
agreement, including vertex ranks and first occurrences. Both genuine and raw
updates use `Dijkstra.Store.accum` and the now-public
`Dijkstra.Store.valuesAt_map_unique`. This lemma was moved from Core's private
helper and generalized over its value universe; Core's public contracts are
unchanged. The old provenance ledger records the new location and preserves
immutable candidate `e0d76c8` as its historical location.

Encoding maps infinity to a natural sentinel and finite distances to integers.
`Valid S d` requires each finite value to be strictly below S. Order and equality
reflection require validity. The raw-addition correspondence requires a finite
selected distance and a valid edge; update correspondence additionally requires
valid stored labels and candidate sums. It preserves the complete state,
including parents and fresh-list order.

`Range.lean` bounds a parent chain by `(path.length-1)*bound`, and a simple
parent label by `(n-1)*bound`. The sufficient guard `n*bound < sentinel` covers
one further edge in every candidate relaxation. All-vertex reachability ensures
a selected label is finite. These assumptions transport the accepted invariant
and parent-chain results through every step and arbitrary-length run. They yield
exact encoded-state agreement and independent shortest-distance correctness.
They are sufficient conditions, not a characterization of every safe input.

The standalone jogger arithmetic bound is also preserved: two path distances
plus an edge require `(2*n-1)*bound < sentinel`. This is an arithmetic theorem,
not a reconstructed jogger algorithm. All arithmetic here is over unbounded
mathematical integers. The proved ranges are transfer conditions for a separate
machine realization; no Int64, BitVec, wraparound or runtime theorem is claimed.

## Composed consumers and checked cases

`Observation.lean` packages the sufficient domain as `SafeProblem` and uses
existing `Squares.Square`/`Squares.compose`. `executionSquare` runs raw Dijkstra;
its specification runs accepted Dijkstra and encodes its result. State
observations retain outer `Option` failure. `allDistances_exact` connects the
actual raw vector to the encoded accepted `Observation.allDistanceSquare`.
`allParents_exact` retains exact parent identity. `targetDistance_queue` connects
the raw target observation to the actual existing `Observation.queueRun`:
outer failure remains distinct from a completed inner no-path result. Under
the safe domain, completion and a finite optimum follow. No queue witness or
parent tie equality is asserted.

The original finite-source example was a direct calculation; its missing
connection to the universal refinement is supplied in
`Examples/DijkstraSentinel.lean`. The six-vertex graph reuses existing #180
weights, shortest paths and vector facts. Proved reachability, edge bound 11
and `6*11 < 100` establish its domain. Its raw distances are
`[0,7,9,12,11,10]` and one-based parents `[1,1,2,5,6,3]`. The target-three case
uses the actual queue-agreement result to obtain cost 12.

A second graph has zero-weight edges and tied alternatives, bound zero and
sentinel one. Public correspondence and observation results establish its
zero distances and retained old parents. Singleton cases check zero source
updates, root distance and parent. An overlong run returns outer `none`; an
empty raw state has no next step. A separate accepted disconnected-graph case
returns `some none` from the queue, preserving the distinction from exhaustion.

The failure evidence is explicit. `unguarded_infinity` gives
`rawSum 10 10 1 = 11`, while a missing edge returns 10. `sentinel_collision`
identifies the encoded values of finite distance 10 and infinity. A reachable
two-vertex graph with edge cost 10 and sentinel 10 demonstrates actual state
refinement failure: raw execution keeps the target's self-parent, while accepted
Dijkstra installs the root parent. The failed range hypothesis is consequential;
reachability alone does not restore the theorem. Arithmetic examples separately
exercise the relaxation and stronger jogger range results.

## Statement review

| Claims | Checks |
|---|---|
| Raw operations and score | Int parameters stay unrestricted at the execution layer. Only the edge is guarded. Standard lexicographic comparison is proved equal to the source guard; old-parent ties and exact step count remain unchanged. |
| Encoding and update | Finite-value validity is strict; infinity is allowed. Equality/order reflection requires both operands valid. Update hypotheses separately cover stored labels, edges and sums. Parent and fresh-list equality are retained. |
| Chains and safe ranges | Independent accepted parent chains supply the bound; simple paths have at most n vertices. Existence of a root supplies n>0. The extra candidate edge needs n times the bound. Zero weights and zero bound are permitted. |
| Step/run/global transport | All-vertex reachability supplies a finite selected label. Invariant and parent preservation come from accepted #180. Arbitrary-count runs preserve outer failure, and the source entrypoint retains n−1 updates. |
| Consumers | Implementations execute the raw program. Accepted distance/route semantics and the existing queue supply correctness; encoding does not pretend arbitrary negative Int labels are nonnegative distances. Whole-parent agreement is with the accepted array executor, not with an arbitrary tied queue witness. |
| Arithmetic and examples | The two arithmetic guards remain distinct. No finite-width integer assumption is hidden. Boundary cases establish their public theorem premises or explicitly demonstrate why a premise fails. No rooted Fin 0 input is invented. |

No outstanding statement-review defect was found. Targeted validation
`direnv exec . lake build Examples.DijkstraSentinel` passed (771 jobs), including
the existing Dijkstra examples after the shared-helper move. Existing Mathlib
module-import advisories remain; no proof warning was suppressed. Whole-project
fresh compilation, exhaustive axiom audit and independent reviews belong to the
root integration gate.

## Provenance and remaining scope

The [preserved reference](../history/algorithm-design-haskell/README.md) is
`adwh-checkpoint-233`. The entire ZIP hash and selected member hashes were
verified against metadata/manifest and inspected extraction. The
[ledger](adwh-dijkstra-sentinel-provenance.tsv) has 100 rows:

- All 44 `Chapter09/DijkstraSentinel.lean` declarations, including private-helper
  replacements, and two explicit standard-order instance bridges. Member hash:
  `f75e7e0348dd84f83742ee8f222b9f45a60f7acf30726a23666add167aaa7f92`.
- All 22 `GraphWorkedExamples.lean` names: one newly reconstructed finite-source
  case, 12 previously reconstructed names, and nine deferred names. Member hash:
  `5c53b9bf44f426b84e998c1f1becc4a8b1b6c52a90d227923529feb1cc7875da`.
- All 32 `PrimWeights.lean` names explicitly deferred. Member hash:
  `f8b823b0ca92e54e01f75bd841242d90215313900edbd6e82a1ac4f6748bf8ed`.

The initial scope counted 13 existing figure names. Inspection found that
`figure_tree_edges` was absent from #180 code and ledger; it is accurately
marked deferred here. Other deferred figures concern Prim/partial diagrams and
matrix construction. PrimWeights is not required by this direct graph client.
NumericCached, roots/saved roots, execution costs, broader jogger clients,
machine realization and queue witness equality remain outside this scope.
