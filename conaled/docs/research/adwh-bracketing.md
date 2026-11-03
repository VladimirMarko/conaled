# Bounded bracketing reconstruction

Part of [#153](https://github.com/VladimirMarko/conaled/issues/153), under
[#149](https://github.com/VladimirMarko/conaled/issues/149). The immutable source
is [checkpoint 233](../history/algorithm-design-haskell/README.md).
[Declaration provenance](adwh-bracketing-provenance.tsv) records the snapshot,
member, SHA-256, source declaration and corresponding local declaration.

## Mathematical contract

`Bracketing.Recursive.mctH_minimum` compares the chosen tree with **every**
full binary leaf tree with the requested ordered fringe. Feasibility does not
refer to the program's candidates. Fork cost is `h leftCost rightCost + f
leftSize rightSize`, with arbitrary natural-valued charge `f` and a
coordinatewise monotone `h`. No associativity is required. The nonempty input
proof excludes the nonexistent empty leaf tree; `Array.mct3Option_nil` gives
the separate empty request result.

`Cached.triple_eq_pack_mct` and `Array.mct3Tuple_eq_triple` preserve the exact
tree and both cached fields. They require no monotonicity. Ties choose the
first split among recursively optimized children. A non-strict combiner can
hide a nonoptimal child's cost, so this does not promise the first tree in
an exhaustive enumeration. The four-leaf nonmonotonic counterexample retains
its original cost 20 versus a feasible competitor of cost 0.

## Interfaces and reuse

The source's chapter imports pulled in unrelated matrix and knapsack proofs.
The local dependency graph separates tree/cut/selection facts, recursive
optimality, cached construction, and diagonal array construction. `Tree` has
nonempty leaves and no empty constructor; this preserves the feasible domain
rather than adapting an empty-node tree representation. Existing `List`,
`Array`, arithmetic and order operations are reused. The tree, recursive, cache and batch proofs need only `Std`; the array
selector and optimum integration reuse the existing Mathlib order interfaces.

`Bracketing.argmin_eq_sourceMinWith` proves that
the generic `Optimization.Thinning.argmin` from #151 agrees with the source
nonempty selector. The actual array implementation uses this shared selector.
`argmin_firstMinimum` retains the source strict-prefix/weak-suffix occurrence
contract. The source selector remains as the exact recursive specification;
its naturality proof is used by cached refinement. This dependency is based
on integration commit `0871aa348b9260cbff66cbbf04f1c452e6770ff1`.

`Tree.fold_fusion` exposes the leaf and fork equations needed by an
interpretation. `Tree.fold_pair` computes simultaneous observations.
`cached_fold` identifies the cached constructor interpretation with the
cost/size/tree package. The checked ordered-leaf/count example uses the
product law and the length interpretation uses fusion.

`arraySquare` interprets an actual built array result as the recursive tree.
`solveSquare` composes that square with cache erasure through `Squares.compose`.
`solveSquare_minimizer` transfers its exact equation to the existing
`Optimization.minimizers` contract. Callers provide the combiner's monotonicity
once; they do not repeat table induction to obtain optimality. The checked
work and depth examples consume this composition and its optimum theorem.

`DynamicProgramming.ArrayBatch` specifies distinct, in-bounds simultaneous
writes. Bracketing diagonals and the separate 0/1 knapsack value DP both prove
these conditions. The knapsack `table_entry` theorem relates each capacity
entry to its recursive recurrence, and its capacity-two, weight-one case
returns 7 after one value-7 item. Reading an accumulating ascending row would
return 14. Every association value reads the old immutable row. These are
value-level array proofs, without allocation or in-place runtime claims.

## Checked cases and statement review

The four-leaf additive merge example has cost 8; parallel unit-charge depth
has cost 2. Both produce the balanced tree and establish its independent
minimum through `solveSquare_minimizer`. A three-leaf all-zero example checks
the first, right-branching cut through the exact representation theorems.
Empty requests return `none`. The counterexample applies the public failure
witness to refute membership in the shared minimizer set.

Statement review covered all new definitions and claims by their dependency
families: tree fringe and size, proper cuts and termination, first minimum,
recursive optimum, cached agreement, interval/table invariants and uniqueness,
batch updates, knapsack entry recurrence, interpretation composition and
examples. The following distinctions remain explicit:

- Optimum quantifies over arbitrary competitors with equal ordered fringe.
- Exact representation agreement does not assume the optimum hypothesis.
- Table uniqueness compares valid upper-triangular cells, not arbitrary
  padding or malformed table sizes.
- Batch semantics requires distinct valid indices; the two callers discharge
  both premises. Knapsack permits zero weight and reads the previous item row.
- The knapsack client proves the value recurrence, not selection witnesses or
  a new global feasibility theorem.

## Coverage and remaining work

The provenance table is declaration-level coverage, not a claim that whole
source modules were migrated. The generalized cost, cached and array families
are retained. Only their required tree/cut/selector, interval, flattened-index,
optional traversal and batch-update dependencies were reconstructed. Matrix
compatibility, matrix guard proofs, generic associative weight bracketing,
exhaustive all-tie generators, Garsia–Wachs, cost instrumentation and source
knapsack selection agreement remain outside this bounded delivery.

Targeted Lean compilation covers every new module and `Examples.Bracketing`.
The supervising workstream owns the fresh complete build, exhaustive axiom
audit and independent reviews; those are acceptance requirements, not implied
by targeted compilation.
