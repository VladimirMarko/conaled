# Native and compiled measured loops

The bounded #584 experiment retains the native ranked-loop API and adds an
experimental compiler client. It does not select a general recursion interface.
The checked modules are
[`Applications/Resources/MeasuredLoop.lean`](../../Applications/Resources/MeasuredLoop.lean)
and [`Examples/MeasuredLoop.lean`](../../Examples/MeasuredLoop.lean).

## Shared source mathematics

For input `(n,a)`, descending-square accumulation returns counter zero and
`a + sum(i*i, i=1..n)`. The threshold client receives `(n,a,t)`, retains `t`,
returns counter `min(n,t)` and accumulator
`a + sum(i+i, 1≤i≤n and t<i)`. Both stop immediately when their initial guard
succeeds. The second client changes the arithmetic body as well as the guard's
input data.

`visited` is a finite-prefix sum independent of syntax and execution.
`visited_sum` identifies it with the corresponding `Finset.range` sum.
`source_steps` proves the complete result and exactly `n-t` continuing steps
for the parameterized source body. Its induction handles both initial stop
and continuation; no whole-loop result is supplied as a primitive. `decreases`
uses the counter as a natural rank. The rank establishes termination, while
the separate step theorem establishes the number of iterations.

The native adapter accepts measured guard and body operations.
`run_value` connects it to the existing `Iteration.runUntil`; `Steps.until`
connects counted executions to `UntilSpec`. Existing first-hit semantics,
invariants, uniqueness and the identity-loop rejection remain available.
The native body evaluates decrement, weight and accumulation once each.
Its two instantiated weights are single arithmetic primitives, exactly as in
the compiled source. The general native weight parameter has a declared unit
charge, not a claim that every Lean function executes in unit time.

## Typed tests and execution

The existing scalar grammar has one base type, unit and products. With `Nat`
as the base, a Boolean result is not another scalar object. This probe adds
`Test`, a pair of typed scalar operands compared with natural-number `≤`.
`Test.compile` executes both compiled operands and charges the comparison.
The guard is not an uncharged host predicate supplied by each client.

Extending the scalar grammar would require Boolean objects and corresponding
operations across existing targets. These clients need one comparison at the
loop boundary, so the smaller test layer avoids imposing those requirements on
scalar, list-fold or guarded clients. It does not offer Boolean scalar data,
compound tests, branch syntax or heterogeneous base types. A client requiring
those capabilities would need a separate comparison of the two designs.

`Program` contains finite seed, test, body and post terms. The first seed adds
threshold zero; the second retains the supplied threshold. Both bodies contain
visible decrement and arithmetic. The post term reconstructs the output tuple
from projections. Compilation reuses `FoldCompiler.scalar`, its primitive
semantics, `compile_sound` and `scalar_cost`. `execute_of_steps` derives both
result and cost from source execution. The second client supplies no new
whole-loop target proof.

The actual runner executes seed once, each guard once, each continuing body
once and post once. One guard comparison costs one; its scalar operands are
charged by their syntax. Every guard also costs one control-dispatch unit.
Each arithmetic primitive, including a literal, costs one. Wiring, tuple
construction and projections cost zero. Thus for `k` continuing iterations the
bill is

```
seed cost + (k+1) * (test cost+1) + k * body cost + post cost
```

This includes the final successful guard and the initial guard when `k=0`.
There is no additional unmodeled control charge within this declared tariff.
The model does not measure host execution, allocation, natural-number bit
complexity or an ordered primitive trace. Equality of these bills does not
establish physical performance equality.

Both bodies cost three. The square seed costs one; the threshold seed costs
zero. Both post terms cost zero. Checked examples return `(0,19,0)` with cost
18 from square input `(3,5)`, and `(2,31,2)` with cost 17 from threshold input
`(5,7,2)`. Square input `(0,a)` costs three. Any threshold input with `n≤t`
costs two and preserves the accumulator. `squares_native` and
`threshold_native` prove equality of the entire measured result under the
matched native tariff, not just equal output values.

## Transport boundaries and controls

`transport` derives finite relational lockstep execution from guard agreement
and continuing-step compatibility on related states. Validity may be included
in the relation. It does not assert global target termination. Its graph-relation
specialization `transport_map` recovers the contract of `UntilSpec.map`.

`rank_pullback` separately requires an erasure from target states to source
states that preserves guards and continuing steps. `Program.targetDecrease`
uses this construction with identity state erasure and scalar compatibility.
The measured backend retains the source state representation; it is not a
proof of executability for arbitrary relational targets. Seed and post remain
explicit compiled terms with their own value and cost laws.

`guard_disagreement` combines an immediately stopping source and a never-stopping
identity target. Their step functions agree, but their finite results do not.
It reuses the existing identity-loop impossibility theorem. The checked
`equal_values_different_costs` instead executes the square program under two
primitive tariffs: outputs agree for all inputs, while the second bill is
strictly larger. Value preservation cannot infer resource preservation.

## Author obligations and next direction

This is a retrospective implementation comparison by one author, not a frozen
independent author trial or a causal productivity measurement.

| Work | Native route | Compiled route |
|---|---|---|
| Shared backend preparation | Measured runner, connection to `runUntil`, counted-execution bill | Same runner plus typed comparison, finite program record and scalar value/cost lifting |
| First client | Native arithmetic graph, declared charges, independent source result and decrease | Seed/test/body/post syntax; same source result and decrease; instantiate general compiler theorem |
| Second client | Change weight and supply threshold; reuse source theorem and adapter | Change seed and weight term; reuse source theorem and compiler theorem |
| Mathematical obligations | Source finite sum, stopping point and termination | The same obligations remain |
| Representation/conversion | Ordinary tuple projections | Typed term constructors and explicit variable/projection terms; no result casts |
| Target-specific whole-loop proof per client | None after adapter preparation | None after compiler preparation |

The native adapter removes recurring loop accounting without requiring source
syntax. Compilation derives scalar bills and compatibility compositionally,
but the small arithmetic clients do not show that its term-construction
bookkeeping pays for itself. Keep both routes available. Do not broaden to a
universal loop interface on this evidence.

The initial implementation needed ordinary proof repairs: exposing a
well-founded recursion's guard condition, distributing natural multiplication,
using explicit scalar soundness equalities, avoiding a structure-field name
collision and qualifying the resource `bind` operation. These are elaboration
and proof-engineering observations, not mathematical obstructions or measured
author savings.

A useful next probe would use thresholded indexed aggregation or measured tree
annotation, where reusable representation and observation laws have more work
to remove. Changed stopping points and incremental trace repair remain a
separate algorithmic task: no cache invalidation, retained trace repair or
asynchronous execution follows from this experiment. #109 retains the broader
recursion investigation, with #235 owning shared-interface usability decisions.
