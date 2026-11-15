# Compiled mapped aggregates with retained repair

[Issue #583](https://github.com/VladimirMarko/conaled/issues/583) connects the
first-order scalar compiler to the retained indexed sum from #113. The public
implementation is [MappedAggregate.lean](../../Applications/Incremental/MappedAggregate.lean);
[the checked clients](../../Examples/MappedAggregate.lean) use integer square
sums and sums of `x*x+x`, followed by the separately compiled `y*y+1`.

## Practical entry points

Import `Applications.Incremental.MappedAggregate` for the generic API; import
`SquareKit.Arithmetic` explicitly when using its scalar vocabulary. The
[checked clients](../../Examples/MappedAggregate.lean) define independent
polynomial specifications alongside source syntax. `Cost.repair_after_init_output`
connects a measured initialization followed by one patch to the mapped sum,
without a caller invariant proof. For continued repairs, `Cost.repair_output`
accepts the existing `Valid` relation for the current raw input and retained
state. `Cost.workload_output` supplies the composed downstream result for any
finite patch workload; `workload_cost`, `recompute_cost` and
`repair_le_recompute_iff` supply its complete cost comparison.

A measured result is a value/cost pair. Aggregate initialization returns
`VectorSum.State`; aggregate repair returns that state and its output delta.
The composed workload returns the aggregate state and the downstream
input/output pair, so `.1.2.2` is its final output and `.2` its bill.
The new observation theorems avoid unfolding that state relation in client
proofs. They preserve the underlying operations and validity laws.

The shifted-square client uses `(x+2)*(x+2)` and the same downstream body as
the original clients. Ordered writes of index 1 to 5 and then -1 on `[1,2,3]`
yield mapped sum 35 and downstream output 1226. Its source contains two copies
of a named shift term: two literal executions, two additions and one
multiplication cost five. `shiftedSquare_exec_cost` connects this calculation
to actual compiled scalar execution. Naming a Lean term does not introduce
source-level sharing; the existing source `.letE` must be written explicitly
when that binding is intended. This adaptation adds no sharing mechanism.

## Author interface and retained state

Supply a `Scalar`: primitive vocabulary, primitive meaning, fixed primitive
tariff, and a first-order term with one scalar input. `Scalar.exec` uses
`FirstOrderCompiler.compile` with `Resources.FoldCompiler.scalar`.
`Scalar.exec_value` reuses `compile_sound` and `scalarSound`; `exec_cost`
reuses `scalar_cost`. The examples supply arithmetic syntax, not a primitive
whose meaning is the whole aggregate.

The mathematical specification is the finite sum of the scalar denotation over
an indexed input. Its carrier needs an additive commutative group. An assignment
contains an index and a new raw value. The semantic `realization` retains only
`VectorSum.State`: the mapped contributions and their sum. Its validity relation
connects each retained contribution to the current raw input. There is no second
raw-input store in this stage.

Pointwise mapping commutes with assignment and ordered patches.
`realization_laws` uses this fact and `VectorSum.realization_laws`, whose repair
proof uses `total_assign`. The measured repair evaluates the compiled scalar on
each assigned value and calls `VectorSum.Cost.step` immediately. Repeated writes
therefore read the contribution left by the preceding write. `mappedPatch` is a
semantic description; the measured executor does not allocate an intermediate
mapped list.

The downstream component retains its scalar input and output. On an aggregate
delta it updates that input and evaluates its already-compiled body, then emits
the output difference. `Stateful.comp` and `Stateful.Laws.comp` supply composition;
the downstream component does not inspect or rescan the vector. This composition
has `n` contribution cells and three scalar caches, including the downstream
input. No new general recursion or arbitrary-fold interface is introduced.

## Execution model and complete costs

The interpreter uses the owned indexed-store model from `VectorSumCost`.
Reading a cell, writing a cell, prepending a newly materialized cell, adding,
subtracting, storing a scalar and emitting a scalar each cost one. Scalar
primitive executions use their supplied fixed tariff. Tuple construction,
register access, function wiring, patch traversal control, index arithmetic and
empty-store construction cost zero. A patch's supplied value is a register;
accessing it is not an indexed read. The patch storage belongs to the caller.
The scalar tariff is not integer bit complexity.

Functional stores specify the contents of the modeled owned memory. They do not
establish mutable arrays, physical sharing, constant-time Lean function updates,
heap allocation costs or elapsed runtime. Source compilation and proof checking
are outside this execution tariff. Both compared executors use the same scalar
source and tariff; neither is a Wasm artifact.

Initialization reads every raw input, executes the compiled map, and allocates
its contribution cell. A separate charged scan computes and stores the sum.
The aggregate observation initializes the downstream caches. The workload
publishes an initial output, even when it has no patches. Each subsequent patch
performs the repair, downstream evaluation, output-difference subtraction, and
publication of both that difference and the new scalar output. Publication is a
unit modeled `emit`, not an external delivery protocol. Outputs are streamed;
the interpreter retains no growing output list. Correctness at every prefix and
the boundary law justify the intermediate observations.

Write `n` for input size, `k` for the total number of assignments, `b` for the
number of patches, `c` for the compiled map's `bodyCost`, and `d` for the
compiled downstream body's cost. The checked exact bills are:

| Operation | Cost |
|---|---:|
| Contribution materialization | `n*(c+2)` |
| Aggregate initialization, including materialization | `n*(c+4)+1` |
| Aggregate repair with its boundary subtraction | `patch.length*(c+5)+1` |
| Complete retained workload | `n*(c+4)+d+5 + k*(c+5) + b*(d+7)` |
| Complete recomputation workload | `n*(c+4)+d+2 + k + b*(n*(c+2)+d+4)` |

The recomputation baseline copies and retains raw input, charges its assignment
writes, scans it through the same compiled map, evaluates the same downstream
body, retains the previous output, and publishes the same observations. It
needs no contribution cache or downstream input cache. `recompute_output` and
`equal_outputs` connect both executions to the same specification. The erasure
lemmas for measured initialization, repair and composition also identify the
actual retained execution, rather than only its final value.

`repair_le_recompute_iff` proves the exact condition for the retained workload
to cost no more:

```
3 + k*(c+4) + 3*b ≤ b*n*(c+2)
```

The three extra setup units and repeated patch overhead cannot be dropped.
An empty workload is strictly cheaper for the recomputation baseline under this
model. Empty patches still incur downstream evaluation and boundary publication;
there is no implicit no-op optimization.

## Checked consumers and statement review

The client specifications `squares`, `quadratics` and `report` are ordinary
finite sums and polynomials, defined independently of compilation. Universal
client theorems use `realization_laws` and `Cost.workload_output`, connecting
both the retained aggregate and its composed output to those specifications.

For `[1,2,3]`, initial outputs are 197 and 401. Writing index 1 first to 5 and
then to -1 leaves `[1,-1,3]`; outputs become 122 and 197. A subsequent write of
index 0 to zero gives 101 and 145. The checked cases also cover a single write,
empty patches, the retained contribution after repeated writes, and input size
zero. `zero_patch` proves that every representable patch on size zero is empty;
initial output and observation costs remain nonzero.

The square client on the three-cell workload with three assignments in two
patches costs 61 for repair versus 55 for recomputation. The quadratic client
costs 67 versus 64. On 100 inputs with three single-assignment patches, the
square client costs 556 versus 1429. These are exact modeled operation bills,
not timing measurements or a uniform speedup claim.

Statement review checked arbitrary ordered patches, input-size quantification,
validity of initialized states, repeated-index semantics, the additive boundary
law, and both directions of the cost comparison. Scalar soundness assumes only
the supplied primitive meaning; concrete arithmetic consumers discharge their
meaning by reduction to independent polynomials. All scalar execution bills
come from syntax. Group subtraction is essential to the retained sum repair;
this result makes no claim about summary-only repair for arbitrary monoids.

## Remaining scope

[#109](https://github.com/VladimirMarko/conaled/issues/109) retains generic fold
and control-flow questions. A native-versus-compiled loop experiment remains a
separate prepared investigation. [#174](https://github.com/VladimirMarko/conaled/issues/174)
retains physical data-structure and target-capability work. Insertion/deletion,
changing vector size or stopping conditions, physical allocation evidence,
input-dependent primitive tariffs and external output delivery need their own
contracts. This bounded consumer supplies neither a new author trial nor a
reason to adopt a universal recursion architecture.
