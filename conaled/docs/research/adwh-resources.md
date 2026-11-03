# Instrumented execution and source resource models

[#154](https://github.com/VladimirMarko/conaled/issues/154) reconstructs the
thinning models and one complete immutable-array knapsack row. The
[provenance table](adwh-resource-provenance.tsv) names source declarations in
[checkpoint 233](../history/algorithm-design-haskell/README.md), member hashes
and local destinations. This is a bounded resource-model reconstruction under
#149, not completion of all knapsack costs.

## Shared operations

`Resources.Measured` is an ordinary value/observation pair. `bind` sequences
existing Lean functions and adds observations in execution order. Associativity
requires an additive semigroup; identities need zero laws. Commutativity is not
required by the shared operation. This is the additive form of writer
composition; Mathlib's `WriterT` uses multiplicative monoid observations.
No new program syntax, state representation or universal runtime model is
introduced.

`reweight_bind` uses an `AddMonoidHom`, keeping the operation-preservation
premise explicit. `reweight_bound` separately requires a monotone map between
ordered observations. Additivity alone does not assert order preservation.
`bind_erases` composes semantic erasure proofs, and `erasureSquare` packages an
ordinary measured function and its existing proof as a current `Squares.Square`.
These operations do not extract events from arbitrary Lean code.

The actual observation products use natural counters, so their arithmetic is
commutative. They record quantities, not a complete execution trace. The
instrumented programs still preserve branch order and short-circuiting; no
claim of reconstructing event order from counts is made.

[#113](https://github.com/VladimirMarko/conaled/issues/113) owns initialization,
repair, retained-state invariants and boundary-change composition. This change
does not supply those interfaces or imply mutable constant-time indexed access.
It can express an observation attached to a future #113 realization once that
realization proves its own semantics and charges.

## Thinning

`bumpMeasured` evaluates the forward relation first and the reverse relation
only if needed. One execution records relation calls and richer work.
`thinMeasured_calls` and `thinMeasured_work` identify its projections with the
literal `thinRun` and `thinWorkRun`. The full source bounds remain proved:
relation calls at most `2 * length`, richer work between `length + 1` and
`6 * length + 1`.

The richer model charges a list case, each guard and each constructed cons,
including the retained head in the reverse-guard branch. It also charges each
fold visit, including termination. The relation-call model excludes those
operations. Neither measures the internal cost of deciding the relation.

## Knapsack array row

The actual row uses the existing #151 `Item`, `Selection`, `add` and empty
selection. `better` preserves the source's skip-on-value-tie behavior. Every
entry reads the same old row, then the writes apply to an explicit copy. The semantic update uses
`DynamicProgramming.arrayAssign`, shared with the bracketing and value-DP
clients; `writes_exact` connects the measured writes to that operation.
The first three observations recover the source `ArrayWork` row equation:
`(capacity + 1, capacity + 1 - weight, capacity + 1)`, counting weight tests,
value comparisons and update calls. These counts exclude initialization,
indexed-read latency, scalar arithmetic, list construction and copies.

The fourth observation recovers `KnapsackWork.arrayStepRun` through
`stepMeasured_sourceScalar`, using separately retained literal scalar routines.
Entry tariffs are 7 on the skip branch and 30 on the fitting branch. Association
construction and map traversal add three per cell and one terminal charge;
writes add eight each and one terminal charge. The explicit bulk copy adds
`2 * old.size + 1`, and source range/outer overhead is retained.

`stepMeasured_exact` derives total scalar work
`21 * n + 23 * (n - weight) + 2 * old.size + 9`, where `n = capacity + 1`.
`stepMeasured_bound` recovers the source bound `50 * n + 10` when the old size is
`n`. An update count records each call even for malformed input bounds; the
ordinary row shape premise is explicit in the bound. This model does not equate
many immutable API calls with a free physical copy. It models one bulk copy and
writes to a fresh indexed store, with no compiler or physical allocation theorem.

The [complete immutable workload](adwh-knapsack-workload.md) under #162 now
connects initialization, all rows and final names observation to exact source
selection and independent global optimality. It recovers `arrayRunRows`,
`arrayRun`, their scalar bounds, the first three whole-run counts and the array
component of `complete_variants_optimal`. This #154 record retains the scope
and evidence for the shared row used by that extension. Recursive/list scalar
work, bit complexity, peak space and runtime claims remain outside both slices.

## Checked uses and statement review

The first obligation was to obtain both original thinning counts from a single
branch-sensitive execution, then transport those observations through sequential
composition. `Examples.Resources.thinning_two_models` connects `[3,1,2]` to
output `[1]`, three relation calls and thirteen work units through the projection
results. Reverse and incomparable guard cases retain their differing tariffs.
`composed_thinning` uses the homomorphism theorem for two actual thinning runs;
`composed_erasure` uses the shared semantic composition theorem.

The knapsack case has capacity two and one item of weight one/value seven.
`row_observations` uses the public row theorem to obtain `(3,2,3,124)`.
`row_tariffs` interprets that execution as eight selected primitive calls or
124 full-work units. `old_row_once` uses semantic erasure to show value seven,
not fourteen. The no-fitting-capacity case still charges copying and writes; a zero-weight,
zero-value tie retains the skip selection. `row_bound` uses the public bound,
and `monotone_work_bound` exercises bound transport separately. `rowSquare` supplies the
ordinary function/proof pair to the existing square interface.
The concrete unequal-tariff example proves that equal outputs do not transport
cost equality.

Statement review checked operation laws separately from order/bound laws;
source branch/tie behavior; all old-row reads; source copy and excluded charges;
and the distinction between count projections and a trace. Generic statements
quantify over actual supplied functions and observations, not a correctness
assumption equal to the desired cost bound. No blanket per-module parity is
claimed by the provenance rows.

Targeted compilation covers the four resource modules and the connected examples.
The supervising workstream owns fresh full compilation, the exhaustive axiom
audit, reference gate #150 and independent reviews before acceptance.
