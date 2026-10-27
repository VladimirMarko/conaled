# Retained-state incremental composition

Implementation of [#113](https://github.com/VladimirMarko/conaled/issues/113).
The earlier [optimization research](compositional-optimization.md) supplied the
vector-sum case. This delivery provides semantic composition and an abstract
operation-count realization. It does not provide code generation, a mutable
Lean array implementation, or a runtime speed measurement.

## Semantic interface

[`Stateful.Ops`](../../Applications/Incremental/Stateful.lean) supplies a state
type, initialization, repair, and observation. Repair returns both a new state
and an output change. `Stateful.Laws` separately relates states to mathematical
inputs, establishes initialization and repair validity, and relates observations
to an ordinary Lean function. Its boundary law says that applying the emitted
change to the old observation gives the new observation. It does not require
output changes to be unique.

These contracts use the existing `ChangeObj` operations. They require no
decidable equality, finite encoding, cost algebra, mutable storage, or
computability of the semantic function. State and validity relations belong to
a chosen realization; the specification is still the supplied function and
input/output update operations. A different realization may retain different
data or use noncomputable operations.

Composition retains both component states. Its validity relation says that the
second state represents the first state's observation. Initialization passes
that observation to the second initializer. Repair invokes the first repair,
passes its emitted change to the second repair, and keeps both resulting
states. `Laws.comp` proves validity, observation agreement and the boundary law.
No semantic evaluation or initializer is called by this repair operation.

The backend supplies local state operations and their laws. The shared
composition construction supplies the wiring and its proof, suitable for a
compiler to reuse. This delivery does not extract caches automatically from
arbitrary Lean functions or extend the source compiler's primitive language.
`ofMap` adapts existing finite-change maps as a baseline; their change operation
may still recompute. `project_repair` proves observation agreement with the old
`Map`/`Cache` semantics, without claiming that the old cache holds internal
states. `initializationSquare` reuses the existing exact-square interface.

## Vector sum and a consuming computation

[`VectorSum`](../../Applications/Incremental/VectorSum.lean) uses an exact
additive commutative group. Inputs are functions `Fin n → G`; patches are lists
of indexed assignments. The list is processed in order. Each assignment reads
the current value, adds `new - old` to the cache, and replaces that indexed
value. Repeated indices therefore read the value left by the previous assignment.
The invariant equates the indexed values with the semantic input and the cache
with their finite sum. No group operation is required by the general stateful
interface; this realization needs subtraction to repair a sum.

The consuming component retains twice the sum. On a boundary change `d`, it
adds `d + d` to its own cached output. The composed proof follows from the
shared composition law. The downstream output and the upstream sum are both
retained, and their invariant survives an arbitrary ordered patch.

[Checked clients](../../Examples/StatefulIncremental.lean) include the input
`[2,3,5]` and assignments `[(1,7),(1,4),(0,-2)]`. The expected result is
`[-2,4,5]`, sum `7`, doubled observation `14`, and sum boundary change `-3`.
Computing both changes at index 1 against its original value would instead
produce the wrong sum `11`. Other cases cover empty input, empty patches,
multiple batches, the charged execution's semantic projection, and the generic
group theorem.

## Evaluation and resource model

[`VectorSumCost`](../../Applications/Incremental/VectorSumCost.lean) interprets
indexed reads/writes, scalar addition/subtraction, scalar-cache stores and scalar
emission as unit-cost primitives. Scalar operands are already in registers.
Tuple formation, control, index arithmetic, and register reads are uncharged.
The model assumes fixed-size scalar cells and mutable constant-time indexed
access. The functions specifying indexed updates describe store contents;
Lean's function closures do not implement this cost model.

The interpreter sequences actual primitive operations through `Resources.bind`
and patches/batches through `Resources.run`. Value-erasure theorems connect
initialization and repair to the semantic realization. Costs are derived from
these executions, rather than attached to the semantic function as a promised
bound. Existing `Resources.reweight_bind` and `reweight_run` can transport an
additive observation interpretation; a target with different primitive costs
must establish its own cost correspondence, not infer it from value agreement.

For a vector of length `n`, a patch of length `k`, and `m` batches containing
`K` assignments in total, the proved work counts are:

| Operation | Unit operations |
|---|---:|
| Sum initialization, ownership of indexed input transferred | `2n + 1` |
| Sum repair, including emitted boundary subtraction | `5k + 1` |
| Sum scalar observation | `1` |
| Doubled-sum initialization, including boundary observation | `2n + 4` |
| Doubled-sum repair, including downstream addition and cache maintenance | `5k + 4` |
| Whole composed workload, one emitted scalar per batch | `2n + 4 + 5K + 5m` |
| Copy through a unit-cost indexed reader into owned cells | `2n` |
| Copy followed by composed initialization | `4n + 4` |

The five assignment operations are an indexed read, subtraction, addition,
indexed write, and sum-cache store. The downstream repair computes its delta,
adds it to the cached output, and stores the result. Scalar output emission is
charged once per batch; outputs are streamed and not retained as a history.
The boundary subtraction costs one even for an empty patch. Initialization
retains its constant overhead when `n = 0`. The exact affine workload bound is
at most `5(n + K + m + 1)`; the single-variable initialization and repair claims
also use the existing standard `Resources.isBigO_of_nat_bound` bridge, with a
positive-size threshold. Empty workloads and zero-length vectors remain covered
by the exact formulas.

Ownership transfer is an input contract, not a free conversion from any
mathematical function to memory. `copy` explicitly charges each reader access
and each destination cell write. The reader must itself be realized with the
stated access cost. An arbitrary function, including a noncomputable one, has
no such cost guarantee merely because it has type `Fin n → G`.

The retained composed store has slot type `Fin n ⊕ Fin 2`: one slot per input
index plus two scalar caches. `contents` gives its values and `slot_count`
proves its cardinality `n + 2`. The uncomposed store uses `n + 1` cells.
This is a retained-cell model, not a Lean heap or allocation-byte theorem.
Copy initialization writes `n` newly owned input cells; transfer initialization
reuses the caller's cells. Repair updates existing cells in this model. Input
patch lists, temporary registers, initialization recursion frames, allocator
metadata, and consumer-retained output histories are outside the retained
footprint. No bound on cumulative host allocation or peak temporary memory is
proved here. A physical interpreter must establish those separately if claimed.

Immutable copying can charge a vector copy per assignment or batch. Persistent
trees can add logarithmic lookup/update work and path allocation. Functional
update closures can accumulate lookup depth. Unbounded integers and rationals
have operand-size-dependent scalar costs. None of those costs are made constant
by the exact group laws.

## Materialized prefix observation

[`PrefixSum`](../../Applications/Incremental/PrefixSum.lean) specifies all
inclusive prefix sums. Changing the first input by a nonzero group element
changes every prefix. `prefix_write_lower_bound` quantifies over any ordered
list of scalar writes which transforms the old materialized output into the
new one, and proves that its length is at least the vector length. The proof
uses the fact that an unwritten cell retains its old value. It covers repeated
output writes as well. The nonzero assumption excludes trivial groups and
no-op input changes; the integer example witnesses a nonvacuous case.

Thus a one-assignment input patch can require linear output work under a
materialized observation contract. Compressed deltas or deferred observations
have different contracts. This lower bound does not establish a universal
speedup for incremental computation.

## Other compilation targets

Lean is the host in which these mathematical contracts and interpreter proofs
are checked. Nothing requires a future executable target to use Lean's runtime,
closures, garbage collector, or array representation. A target can choose its
own indexed store, scalar representation, state ownership and emitted-output
mechanism. It must prove a representation relation for those states, local
initialization/repair/observation laws, and any claimed primitive work or space
correspondence. Composition then reuses the boundary-change law; semantic
agreement alone does not transfer costs. Machine integers require an overflow
contract or a different mathematical domain, and approximate scalars require
an approximation contract. A universal target IR or code generator is not
introduced by this bounded case.

## Precedent and scope

Ley-Wild, Acar and Fluet's [A Cost Semantics for Self-Adjusting Computation](https://software.imdea.org/~rleywild/publications/popl09/popl09.pdf)
uses a language with mutable references, execution traces and a translation
whose cost properties are proved alongside meaning preservation. That is a
precedent for stating cost correspondence separately. This implementation
neither ports that language nor inherits its trace-distance bounds. Its proofs
concern the explicit sum/assignment interpreter and composition contract above.
