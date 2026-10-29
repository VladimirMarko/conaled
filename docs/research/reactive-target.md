# Compiled initialized reactive machines

[ReactiveCompiler](../../SquareKit/ReactiveCompiler.lean) lowers an initialized
first-order seed and transition body to stored target morphisms. A transition
receives input and previous state and returns output and next state. Compilation
has no runtime input stream: `Compiled` holds the compiled seed and body, and
`realize` constructs a machine that executes those morphisms. Source terms and
the source evaluator occur in the independent specification and its proofs.

The body has context `[input,state]`, whose value is `(((),state),input)`, and
result type `output × state`. `initial_sound` and `step_sound` reuse the existing
first-order `compile_sound` theorem for every input and state. `realize_compile`
identifies the two initialized machines when their state types coincide;
`run_sound` gives equality of complete finite output lists and final states.
`compileMap` and `map_sound` provide the corresponding pure transformation route.

An additional backend supplies the existing `FirstOrderCompiler.Target`
cartesian operations and primitive interpretation, plus local `Sound` evidence
for its denotation. These obligations yield the initialized-body equations;
there is no new compiler induction. A denotation is not automatically an
executable implementation. The concrete consumers use the existing
`ListFoldCompiler.functionScalar` and `functionScalarSound`, with executable
natural-number literals and addition. This reuses the scalar backend from
[finite recursive compilation](recursive-compilation.md); its outer final-value
list fold is not being treated as a streaming scan.

## Wiring and state

[Progress.Reactive](../../Applications/Progress/Reactive.lean) adds three
operations over the existing `Initialized` type:

- `pure` lifts a function with a trivial `PUnit` state.
- `seq` runs the first component on this tick, passes its output to the second,
  and stores both new states.
- `par` runs independent components on the two input fields and stores both
  resulting states.

Stream output and component-state laws follow from the existing solution
uniqueness theorem. `run_pure`, `run_seq`, and `run_par` describe finite outputs
and final states. The existing `run_append` supports continued execution from a
chunk's retained state. `run_related` supplies a finite relational counterpart
to the existing stream `transport`: one local output/state law lifts to related
output lists and related final states. It uses the existing runner.

These are feed-forward composition operations. Their laws do not identify raw
machines with different state types, assert a categorical trace, or solve
instantaneous loops. Previous-state delay and initialization remain the ones
from [initialized feedback](initialized-feedback.md).

## Two consumers and their checked uses

[ReactiveConsumers](../../Applications/FRP/ReactiveConsumers.lean) supplies an
explicit batch adapter: sum each `List Nat`, then tick a compiled scalar
machine. Summation is an aggregate observation; it discards payload order and
occurrence identity.

The first consumer compiles seed `(0,0)` and a body that emits and stores
`(k+1,total+x)`. The second compiles separate count and total machines, preceded
by compiled pure duplication and followed by a compiled pure map
`(k,total) ↦ (k,total+k)`. Its state is
`((PUnit × (Nat × Nat)) × PUnit)`. `StateRel w s := w.1.2 = s` relates that state
to an independently defined joint machine with state `(k,total)`. The local
compiled equations discharge `wired_step`; existing stream transport and the
finite relational law then compare arbitrary inputs, outputs, and final states.
The checked wiring decomposition also invokes the public pure/seq/par run laws.

[ReactiveTarget examples](../../Examples/ReactiveTarget.lean) prove and evaluate
these independently expected results for
`[none, some [3,4], some [], some [3]]`:

| Consumer | Outputs | Final count and total |
|---|---|---|
| Joint compiled body | `(1,7), (2,7), (3,10)` | `(3,10)` |
| Independently wired bodies | `(1,8), (2,9), (3,13)` | `(3,10)` |

The adapter reuses `FRPSpec.Feedback.consume`, its completed-batch agreement,
and its chunk law. `none` does not call a transition body; `some []` does and
increments the count. A checked wrong adapter that drops empty batches yields
only two ticks and final count 2. A separately compiled delayed body seeded at
42 emits `[42,7,0]` on inputs `[7,0,3]`, ruling out an instantaneous interpretation.

## Actual engine emissions and scope

The examples consume a real [incremental engine](frp-engine.md) command run.
`actualResponses` retains its complete timestamped optional event list;
`actualBatches` derives a separate batch observation with `Option.map Prod.snd`.
The engine's `(2,[3,4,3])` response supplies one tick, producing `(1,10)` for the
first consumer and `(1,11)` for the wired consumer. Repeated processing supplies
no additional tick. This one-shot use is distinct from the synthetic multi-batch
examples; neither extends the engine's request lifecycle.

Processing positions, completed-batch ticks, and source timestamps remain
separate, as required by the [multimodal assessment](multimodal-reactive-assessment.md).
Compilation and wiring add no fairness or liveness guarantee. The implementation
contains no network syntax, universal modal interface, graph scheduler,
cancellation, external IO, reclamation, or cost bound. The next pipeline adapter
can pair the accepted engine and consumer states one command at a time; it need
not alter either component's semantics.
