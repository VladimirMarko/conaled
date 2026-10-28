# Initialized feedback and finite FRP deliveries

[Issue #217](https://github.com/VladimirMarko/conaled/issues/217) implements the
first experiment in the [recursion and reactive priorities](recursion-and-reactive-priorities.md).
A total discrete step and an initial state determine a unique state history and
output stream. The construction agrees with existing Mealy execution, supports
relational transport, and factors a coupled recurrence into separately stateful
stages. A finite FRP adapter feeds actual completed deliveries into that boundary.

## The reusable boundary

[Progress.Feedback](../../Applications/Progress/Feedback.lean) exposes ordinary
Lean operations through `Initialized A B S`: a body `A × S → B × S` and an
initial value. No internal-language syntax is required. A direct client can
construct this pair and call `output`, `state`, or the finite `run` interpreter.

The independently stated `Solution` equations are

```
s(0)   = initial
s(n+1) = (step (a(n), s(n))).2
b(n)   = (step (a(n), s(n))).1
```

`existsUnique_solution` proves existence and uniqueness of both histories for
every input stream. `output_mealy` identifies the output with `runStream`;
`output_prefix` recovers finite execution through `runStream_prefix`.
`causal` reuses the existing delivery-to-causality result: equal input prefixes
of length `n` yield equal output prefixes of length `n`. The body may read the
current input, while state comes from earlier ticks. This is synchronous
causality, not a prohibition on current-input dependence.

`transport` accepts heterogeneous input, state and output types and three
relations. Related initial states and one-step compatibility imply related
states at every index and related outputs at every index. `prefix_related`
lifts the latter to every finite prefix. The state relation need not choose
a decoding function. `solutionSquare` packages the output contract in the
existing `RelSquare` interface, so downstream observations compose without
another feedback proof. `producer_transport` specializes to a functional
state map and reuses `unfold_transport` for independently supplied coalgebra
inputs. It does not replace the more general relational contract.

The underlying operations are total Lean functions. This experiment does not
interpret potentially diverging bodies. `mealy_delivery` supplies the existing
`n+1` atomic-transition bound for a finite list of length `n`, including the
empty-tail check. That metric excludes the body computation, list allocation,
and host runtime; it is not a new cost bound for FRP execution.

## Coupling and decomposition

[CoupledFeedback](../../Applications/Progress/CoupledFeedback.lean) starts from
arbitrary operations `p : A → Y → X → X` and `q : A → X → Y → Y`. Its independent
`CoupledSolution` retains both initial states and requires

```
x(n+1) = p (a(n)) (y(n))   (x(n))
y(n+1) = q (a(n)) (x(n+1)) (y(n))
```

Left uses old right state; right uses the newly computed left value. The edge
back to left crosses a stored-state delay. Output is the updated pair.
`joint` executes this recurrence with pair state. `wired` independently calls
`leftStage`, then `rightStage` with its intermediate result, retaining the two
component states before continuing. It never calls the joint interpreter.
`factorization` proves equality of outputs and final state for every finite
input list. `coupled_prefix` connects this execution to the joint stream
solution for every prefix.

This is more than renaming a pair-valued transition. `left_stream` and
`right_stream` identify each coordinate of any independently specified coupled
solution with the corresponding separate Mealy stage, driven by the appropriate
old-state or current-intermediate stream. `coupled_unique` identifies every
such solution with the joint state history. The construction proves this
particular delayed wiring discipline; it does not claim all categorical trace
or Conway identities.

The [checked client](../../Examples/InitializedFeedback.lean) uses
`p a y x = a+y+x`, `q a x y = x+y`, initialized at `(0,0)`. Inputs `[1,2,1]`
produce `[(1,1),(4,5),(10,15)]`. The equality is checked through the generic
prefix/factorization interface as well as direct finite evaluation. A second
realization carries an unconstrained Boolean tag and toggles it on every tick.
Both tags relate to the same source state. Generic transport supplies all
finite-prefix comparisons, and a composed square transfers the observer that
adds the pair's coordinates. Projecting the decorated state also exercises the
existing coalgebra transport law.

## Finite FRP adapter

[FRP.Feedback](../../Applications/FRP/Feedback.lean) consumes a finite list of
`Option (List α)` observations. `none` performs no feedback transition;
`some batch` advances exactly once, including `some []`. A batch is one input
value, not one tick per payload element. The adapter neither sorts nor deduplicates
its input. `agreement` equates execution with feedback over the supplied
completed batches, retaining final state. `chunk` proves continuation over
concatenated processing chunks; `tick_count` counts actual completed batches.
`stream_agreement` connects a chosen finite batch prefix to the corresponding
feedback stream. No infinite filter or delivery assumption enters these results.

The Demand bridge uses `Frame.emitted`, not its persistent `observed` field.
`feedbackInputs` visits processing positions `0` through `n-1` once in order.
Event timestamps remain a different index from these processing positions and
from the resulting feedback tick count. A caller supplying arbitrary optional
observations is responsible for supplying each delivery once; this finite adapter
is not a network duplicate-suppression protocol.

`feedback_response` consumes an actual response and the existing `traceRep`
honesty premise. It uses `responseSquare` to identify the delivered batch with
`truth left t ++ truth right t` before applying the feedback body. Source packet
validation alone cannot discharge that premise. The query parameter used to
construct a frame concerns its observation field; `frameBatch` takes the actual
emission, including its batch even if a frame was observed at another query.
The truth theorem explicitly requires the emitted timestamp to be `t`.

The checked Demand trace delays emission until processing index 5. Seven
processing positions produce one feedback tick with batch `[3,4,3]`. At position
6 the known batch remains observable but no new emission occurs, so the adapter
does not repeat it. A separate existing known-empty response produces one tick
with `[]`. A history-accumulating client retains duplicate entries and order,
and counts empty deliveries separately from silence. Both cases also consume
the honest response theorem; executable `#eval` checks return the same finite
outputs. No unfinished retained-state engine from #31 is required.

## Caller obligations and boundaries

A general caller supplies one total body and an initial value. A transport caller
supplies the input/state/output relations, related initial states and one-step
compatibility; it inherits the history and prefix proofs. A coupled client
supplies `p`, `q` and two initial states, then reuses both stage proofs and
factorization. The concrete decorated client proves one compatibility lemma;
it does not repeat the recurrence induction. The FRP bridge additionally needs
actual emission evidence and source honesty. These are structural reuse claims,
not measured reductions in development time.

Checked negatives show that instantaneous Boolean negation has no fixed point,
that a recurrence without initialization can admit distinct constant histories,
and that incorrect initial states or step compatibility invalidate transport.
`none` and `some []` have different outcomes. These cases delimit the hypotheses
rather than supplying an unrestricted fixed-point operator.

The motivation is [Milius–Litak's guarded fixed-point/trace comparison](https://www8.cs.fau.de/ext/milius/publications/files/ml_fics13.pdf),
with the model-specific admissibility visible in Felix's pinned
[`Traced` interface](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Raw.agda#L151-L160).
The implementation here is a direct discrete construction using the repository's
Mealy, coalgebra and relational interfaces. It does not implement those theories
in full. Discrete state delay is not dense-time or physical delay. Source
advancement, honest observations and fair processing remain independent of
feedback causality; no theorem here guarantees that another completed batch
will arrive. #27 retains general runtime/feedback scope, #31 the incremental
command engine, #193 resource consumers, #196 environmental contracts and #109
recursive compilation.
