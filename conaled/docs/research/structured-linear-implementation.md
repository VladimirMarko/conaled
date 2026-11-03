# Structured linear application and measured realizations

Issue [#265](https://github.com/VladimirMarko/conaled/issues/265) adds replaceable
realizations of exact finite matrix-vector application. The
[research assessment](structured-linear-representations.md) explains the scope.
The original coordinate backend remains unchanged.

## Coordinates, storage and client laws

[`Structured`](../../Applications/Linear/Structured.lean) observes each stored
matrix as a Mathlib matrix on `Fin m × Fin n`, then uses `Matrix.toLin'` for its
linear-map meaning. Scalars require a commutative semiring. Equality with zero
is required only for optional zero elimination; cancellation examples use integers.

| Realization | Stored data | Coordinate observation |
|---|---|---|
| Dense | Vector of row vectors, backed by arrays | Every stored coefficient |
| Coordinate entries | List of bounded row, column, value triples | Add all entries at each coordinate |
| Diagonal | Vector of diagonal coefficients | Mathlib `Matrix.diagonal` |

`Fin` indices enforce coordinate bounds. `validateEntry` rejects raw indices
outside the shape. Entry order, stored zeros and duplicate coordinates can vary
without changing the decoded matrix. The proofs never require an injective
sparse decoder. The sparse representation has no sorting or uniqueness invariant.
It was chosen because the client needs traversal and accumulation; compressed-row
storage can be assessed when row access or repeated conversion warrants it.

`Realization` asks for a storage carrier, matrix observation, vector application
and its observation law. `applicationSquare` exposes this law as an ordinary
`Squares.Square`. `batch_correct`, `repeat_correct` and `twoStage_correct` prove
the clients once. The last result uses Mathlib's matrix composition law and
allows the two stages to use different storage formats. Mathematical structure
and coordinate storage remain local to each realization.

Diagonal addition and composition stay diagonal in these coordinates, as proved
by `diagonalAdd_correct` and `diagonalCompose_correct`. General mixed composition
can be materialized into dense storage with `composeDense_correct`. This helper
has no measured matrix-multiplication contract. Application always produces a
dense vector, so a sparse matrix does not imply a sparse output vector.

## Execution and target assumptions

[`StructuredMeasured`](../../Applications/Linear/StructuredMeasured.lean)
instruments a bounded staged machine. Dense and diagonal application enumerate
coordinate entries, then use the same scatter loop as sparse application. A
scatter step reads an input component and an accumulator, multiplies a coefficient,
adds the product and writes the accumulator. Output initialization visits every
output coordinate, including empty-input and all-zero cases. Staging is charged;
this baseline does not claim a fused dense or diagonal kernel.

The target supplies finite-vector allocation, indexed scalar reads and writes,
index operations, entry traversal and exact scalar arithmetic. Event tariffs
specify their costs. Scalar and index slots are abstract units. Zero testing is
an explicit scan event. Stored-entry counts include zero entries and cancelling
duplicates; they are not mathematical nonzero counts. Dense-to-sparse conversion
visits every dense coordinate before discarding zeros. Arbitrary coordinate
functions are tabulated over the entire shape by nested measured traversal,
with each coordinate evaluation treated as a target observation primitive.

The execution observations use `Resources.Measured` and its additive sequencing.
Erasure theorems connect measured operations to the semantic implementations.
Retained storage and temporary live storage are recorded separately from additive
work. Conversion allowances include the simultaneously retained source, staged
entries and destination, and a separate allowance for staging-list flattening.
These are declared slot budgets for the abstract machine, not proved liveness
bounds for the Lean evaluator. The model does not prove bounds on Lean allocation,
persistent-array copies, garbage collection, scalar bit complexity, cache traffic,
CPU/GPU time or floating-point error. A physical backend needs its own refinement
and tariff evidence.

## Checked applications and optimization scope

[`StructuredLinear`](../../Examples/StructuredLinear.lean) checks the independently
calculated action `(2·4, 3·5) = (8,15)` through all three realizations. It reuses
the common batch proof, checks repeated application `(16,45)`, and composes with
a coordinate swap to obtain `(15,8)`. It also checks empty shapes, explicit zero
entries, duplicate cancellation, raw bounds validation, optional zero elimination,
dense materialization and diagonal closure.

[`StructuredLinearCosts`](../../Examples/StructuredLinearCosts.lean) connects
measured executions to workload and format choices. The optimization contracts
reuse `Optimization.Basic` and `Optimization.Transport`; any least-cost result
is restricted to the stated eligible family and tariffs. Retained-storage Pareto
comparison is a separate question from minimizing additive work. Consumer format
requirements and conversion work belong in the composed objective. No search
pruning, general executable selector, automatic sparse multiplication planner or
cross-mathematical-setting transport is supplied.

No shared preservation-interface change was needed. The local realization law
feeds existing square composition and matrix laws. Further formats can implement
that same application contract without requiring a universal matrix-operation
class or reopening the shared interface work in #235.
