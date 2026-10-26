# Dijkstra state execution costs

[#187](https://github.com/VladimirMarko/conaled/issues/187) reconstructs all 38
named declarations of `Chapter09/DijkstraCosts.lean` and seven selected Arrays
helpers. The actual measured computation returns the accepted Dijkstra state
and a source work count. Its complete entrypoint bound is
`(n-1)*(18*n+6)+2*n+3`, with the coarser upper bound `29*n*n`.

## Execution and shared interfaces

`Applications/Resources/Dijkstra/StoreCosts.lean` specializes `Resources.run`
to ordered Store read/combine/write associations. Each association costs three;
`bulkRun` copies n slots once and costs `n+3*m`. The loop executes accepted
`accumStep`, so repeated indices observe previous writes. `accumRun_cons`
exposes the source recurrence. Both element types are universe-polymorphic.

`Execution.lean` retains the source measured comparator, candidate producer,
minimum, filter, optional addition, update producer and state step. Scores use
the accepted `WithTop Nat ×ₗ Nat` order. The selector materializes each score
once; `minimumRun_value` refines the accepted first-tie `argmin`.
`Applications/Optimization/SelectionMap.lean` proves exact selector transport
through any map, without an injectivity premise. The composed cost preserves
all comparisons and ties. This replaces the historical private `foldr1_map`
client without reconstructing generic source fold machinery.

The lifted `iteration` runs `stepRun` on a present state and charges one unit on
an absent state. `runCost` specializes the existing `Resources.run` to k unit
commands and adds one base unit. Its zero/successor equations recover the
complete historical recurrence, including each requested iteration after
failure. `run_nodup` uses `Resources.run_invariant`. The dijkstra entrypoint
executes n−1 iterations and adds initialization charge `2*n+2`.

`Observation.lean` composes the measured erasure square with a target observation
square. `targetRun` observes the actual returned state and retains its work;
lookup is explicitly semantic and unpriced. Its value equals the accepted
optimal/no-path distance and the value of the actual accepted queue execution.
Outer failure remains distinct from an inner no-path result. `segmentedRun`
feeds the first block's returned Option state into the second block; the exact
state/cost law follows from `Resources.run_append` with one base charge.

## Accounting boundary

The source model counts abstract monolithic indexed cells and unit scalar
operations. Its whole-score comparator counts one, two or three scalar tests,
while Store accumulation charges one atomic combine as part of its three-unit
association. These are separate source conventions. The one-copy tariff does
not prove physical allocation behavior of Lean's `Vector.set`. It differs from
the Knapsack source copy tariff `2*size+1`.

Weights are supplied. Matrix construction, paths, output enumeration, queue
execution, bit complexity and compiled runtime are not charged. `plusRun`
models genuine infinity: it checks the edge first, then the accumulated label.
It does not price the finite-sentinel executor's edge-only guard. Value
correspondence alone cannot transfer these resource counts.

## Checked cases and statement review

`Examples/DijkstraCosts.lean` connects public erasure, store, cost, segmentation
and observation results to concrete expectations. Missing connections during
development were the materialized-selector map law, exact shared-run recurrence
and composed measured target observation; these are now public results used by
the cases. Reduction establishes branch constants, while public theorems carry
the cases across representations and to independent accepted semantics.

| Claims | Statement checks and examples |
|---|---|
| Comparator and minimum | All three short-circuit prices are checked, including unequal ranks at equal distance and exact ties. Empty selection costs 1; singleton choice costs 3. Equal-score candidates retain the first actual occurrence. A noninjective map exercises selector transport. |
| Store | Actual left-to-right associations use previous writes. Prepend 20 then 40 gives `[40,20]`, price 7 for n=1 and m=2, through `bulkRun_exact`. Empty bulk still pays one copied slot. No commutative-combine assumption was introduced. |
| Filter, plus, updates, step | Filter preserves order; update associations remain ordered. Missing edge costs 1, finite edge/infinite label costs 2, two finite operands cost3. Step erasure is unconditional; only its work bound needs fresh-list Nodup. Empty fresh returns none at price 2. |
| Iteration and global bounds | Arbitrary k and arbitrary states are supported. Base cost 1 and failed suffix increments remain explicit. Empty-fresh counts0/1/2 cost 1/4/5. Rooted singleton costs 5; counts 2/3 from its start cost 14/15. Root existence supplies n≥1; no Fin0 root is fabricated. |
| Segmentation | Actual continuation passes the previous Option state. `segmented_failure` runs one successful block, exhaustion, then a failed suffix, with exact cost 15. `arbitrary_segments` specializes both the universal value and bound laws to arbitrary states. |
| Graph observations | The accepted six-vertex figure retains distances and parents, target distance 12, fine bound 585 and coarse bound 1044. Public queue agreement observes the actual queue but asserts no queue-cost equality. Disconnected and zero-cycle graphs retain the no-path and zero-distance values with bound 129; accepted tied-parent identity is preserved. |
| Shared structures | `Measured`, bind, run, run_state, run_invariant, run_append and erasureSquare are reused. No generic runner, potential machinery, order structure or independent path semantics was duplicated. |

The source accounting expectations required no correction. No outstanding
statement-review defect was found. Targeted validation
`direnv exec . lake build Examples.DijkstraCosts` passed (785 jobs), including
the existing Dijkstra examples. Existing Mathlib module-import advisories
remain. Whole-project fresh compilation, axiom audit and independent reviews
belong to the root integration gate.

## Provenance and deferred work

The [preserved checkpoint](../history/algorithm-design-haskell/README.md) is
`adwh-checkpoint-233`. The full ZIP hash was checked against metadata; both
selected member hashes were checked against the manifest and inspected
extraction. No historical code was executed. The
[45-row ledger](adwh-dijkstra-cost-provenance.tsv) covers:

- All 38 DijkstraCosts names, SHA-256
  `63016bc858b38b6923a3c050af85d55bfbbb6909c6aa87cce2aa2705af411c5a`.
- Arrays `copy`, `copy_value`, `accumRun`, `accumRun_value`, `accumRun_work`,
  `bulkRun`, `bulkRun_exact`, member SHA-256
  `6bd6f2b7e674814271f1e9dcf5bbed9486d59cc06bcbb8e6239a76c5c47310fb`.

Accepted Core, Store, standard Score and selector dependencies are pinned by
base commit `cb47f65b0cbc4738bed09047aea9ee9258d61610`. The generic private fold
helper is recorded as a replacement, not as a claim to arbitrary-fold
reconstruction. The remaining 58 Arrays names are outside this issue's new
closure; earlier accepted Store semantics remain in place.

DijkstraPathCosts, LinkCosts, SavedCosts, SavedRoots, NumericCached, PrimWeights
matrix builders, JoggerBaselineListCosts, SortByCosts, other Arrays tariffs,
finite-sentinel costs, queue prices and machine realization remain deferred.
The quadratic result is an upper bound, not a Θ statement.
