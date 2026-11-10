# Finite list execution, fusion and demand

## Ownership and reuse

`Resources.ListAppend` owns the existing executed recursive append-copy primitive.
`TreeFlattening.appendWithCost` remains available with the same type, definitionally
the same recursion and exact theorem. Its implementation now delegates to that
shared owner. `CollapseMaterialization.appendRun` specializes the weighted append at
dispatch/copy prices 1,1, retaining its exact signed-list result and 2n+1 bill.

`Resources.ListExecution` provides actual finite structural executions. The direct
left fold uses the existing `Resources.run`, followed by the final constructor test.
The new `run_observation` law in Workload retains arbitrary zero and addition
operations and proves the ordered, right-associated sum of state-independent command
observations. It requires no associativity, identity laws or commutativity.
The direct right fold sequences its recursive execution
with `Resources.bind`. Reversal, selectors and selector recursion have their own
executions. Standard Lists give independent values; ordinary finite range sums
replace the source's separate triangle function.

`Resources.ListFusion` supplies weighted map and the actual materialized/fused
pipelines. It composes measured executions with the existing bind and calls the
shared append. Flattened length is the element-count observation; no parallel mass
function or basic-list library is introduced. `Examples.ListFusionCosts` connects the
new executions to the previously integrated `Steepness.sumRun`, through an actual
composite representation square that retains the producer's bill.

## What the work observations mean

A structural dispatch costs one, a produced/copied cons costs one, and a supplied
price c counts an opaque combining operation. Map and takeWhile additionally expose
independent nonnegative dispatch, cell and function/predicate prices. Zero prices
project away part of the observation while the same value-producing algorithm runs.
Arithmetic of the instrumentation counter, tuple construction, proof totalization,
GC, native instructions and the internals of an opaque user function are outside this
model. A caller must choose an appropriate supplied price for that function.

The generic append first executes the copied-cell recursion and then prices each
left cons and the final nil observation. The affine expression `(d+k)*copies+d`
is applied per append call. It is not asserted to be an additive homomorphism that
can reweight an already summed multi-call trace.

Full folds observe the entire finite spine and charge each combining operation.
A constant-time head observation has the same finite value as a suitable fold,
but a strict full fold has a different demand/cost contract. Last/init dispatches
inspect at most two spine constructors; their unit is a bounded source dispatch,
not a hardware memory read. All supplied premises, finite-domain qualifications and
nonnegative prices remain explicit in the formal statements.

## Structural results

For n input cells and combining price c:

| Actual execution | Exact work |
|---|---|
| Shared source-priced append | 2n+1 |
| Direct left or right fold | (1+c)n+1 |
| Reverse | 2n+1 |
| Reverse then flipped right fold | (3+c)n+2 |
| Head or tail | 1 |
| Last, nonempty input | n |
| Init, nonempty input | 2n-1 |
| Recursive head/tail fold | (3+c)n+1 |
| Recursive init/last fold | 3*sum(range(n+1))+cn+1 |

The one-unfolding head and init wrappers are separate from the self-recursive forms.
On x::xs, their bills are respectively `(1+c)*length(xs)+c+4` and
`(4+c)*length(xs)+c+4`. The init/last recursion retains both a quadratic lower bound
and the source upper bound `(3+c)*(n+1)^2`. The range-sum identities are proved
independently of the executor and then connected through its exact recurrence.

The digit example deliberately distinguishes fold order. The left decimal step
`10*n+d` on [2,7,1,8] returns 2718. Direct, reversed, recursive-init and one-init
realizations cost 9,18,35,20 at price 1. A right fold with merely flipped arguments
returns 8172; its recursive head/tail and one-head realizations cost 17 and 11.
Argument flipping alone is not an order-preservation law. Empty selectors return
none, while singleton init/tail return `some []`.

## Fusion and concatenation

Weighted map work is `(d+k+c)*n+d`. Executing two maps then fusing the element
functions preserves ordered values and saves exactly `(d+k)*n+d`. The same saving
holds for the stated fold-map and concatMap-map transformations. The supplied call
prices are retained, including their sum in the fused combining function.

Right concatenation costs `2N+2m+1`, where N is flattened length and m is the number
of blocks. Left concatenation costs twice the sum of actual previous accumulator
lengths, plus `2m+1`. These are theorems about executions that call shared append;
the closed prefix sum is not substituted for execution. Singleton blocks give the
exact right bill `4n+1` and left bill `n*n+n+1`. There is no universal pointwise
advantage: one block [1,2,3] costs 9 on the right and 3 on the left; four singleton
blocks cost 17 and 21 respectively.

Fold after materialized concatenation and the nested fused fold have equal ordered
values for arbitrary combining functions. The fused bill is `(1+c)*N+2m+1`, and
the materialized pipeline costs exactly `2N+1` more. An actual measured sum consumer
reuses `Steepness.sumRun`, with a proved equality to the generic fold at price 1.
The composite square retains both producer and consumer costs. For [[-1,2],[],[4]],
its result is (5,20), while the fused bill is 13. For no blocks, the materialized
producer/consumer result is (0,2); the two terminal tests remain visible.

## First-false demand

Demand-driven takeWhile returns the standard prefix. Its exact work is
`(d+k+c)*length(takeWhile p xs)+d+c*failed`, where failed is 1 exactly when a
nonempty remainder begins with the first false cell. The nil case has no final
predicate test. The executor does not visit the suffix after that false cell,
and a universal equality states that replacing that suffix changes neither value
nor work. All-unit prices on [1,2,8,9,10] with predicate <3 give ([1,2],8).
Test-only prices count 2 calls on [1,2] and 3 on [1,2,8]. This demand executor is
separate from the full-spine fold, despite their finite value correspondence.

## Retained source worked cases

All thirteen anonymous cases in the two source cost modules are checked through
the public results in `Examples.ListFusionCosts`. The source coordinates refer to
the exact hashed files below.

| Source cases | Checked destination | Expected observation |
|---|---|---|
| StructuralCosts, line 313 | `source_reverse` | Three-cell reversal costs 7. |
| StructuralCosts, lines 314–316 | `source_selectors` | Head, init and last cost 1, 5 and 3. |
| FusionCosts, lines 352–353 | `materialized_successors`, `fused_successors` | Two maps cost 20; the fused map costs 13. |
| FusionCosts, lines 354–355 | `long_block_costs` | Right and left concatenation cost 9 and 3. |
| FusionCosts, lines 356–357 | `singleton_block_costs` | Four singleton blocks cost 17 and 21. |
| FusionCosts, line 359 | `first_false_cost` | The complete prefix/work result is `([1,2],8)`. |
| FusionCosts, lines 360–361 | `no_false_at_nil`, `first_false_is_charged` | Predicate-only work is 2 on exhaustion and 3 on first failure. |

## Provenance and acceptance boundaries

Source hashes are:

- StructuralCosts: 19de70c91c4f64db5137b6ea3cdc12917021201c75418d6a58cffc4b012daba1.
- FusionCosts: dafb5559d8440cd1d7c9f372bdd559da9da5bc0b36f78894dff0a87b63f3c4e9.
- Selected Lists declarations: 6f08454e2deeb5fe00df14e997b9d7f24bd53ba979546c8636bc3254e4a151b0.

The declaration map distinguishes retained observations, shared/generalized primitives,
standard-operation replacements, and private range-sum proof helpers. The public
examples are imported normally. Focused elaboration and statement checks precede
immutable integrated build, exhaustive axiom audit and both independent review axes.
None of these finite equations establishes machine time, physical allocation, peak
memory, big-integer bit cost, whole-language lazy semantics, or whole-chapter/book
completion. Partial/infinite and floating-point source families retain their own
separate obligations. No sixteen-queen numerical proof or generated witness graph
is part of this work.
