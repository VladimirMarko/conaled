# Executable command-to-consumer pipeline

[Pipeline.lean](../../Applications/FRP/Pipeline.lean) connects the accepted
[incremental engine](frp-engine.md) and [compiled reactive consumers](reactive-target.md).
Its state holds the engine state and the consumer state. `step` receives one
concrete engine command, calls `Engine.step` once, and passes that actual optional
response to `responseMealy`. It returns the updated states and a pair:

```text
(original timestamped optional response, optional derived observation)
```

`none` leaves the consumer state unchanged and produces no observation.
`some (time, [])` runs one consumer tick, just like any other emitted batch.
The original ordered payload and timestamp remain present even when the
consumer's observation is a lossy aggregate. Runtime needs no reference stream,
command history, or precomputed response trace. It calls the supplied machine's
step; the compiled consumers execute their stored target bodies rather than
source syntax evaluation.

`run` accepts finite concrete commands and retains one pair of optional events
per command. `run_append` proves that chunked execution, passing both intermediate
states to the next chunk, has exactly the same paired events and final state as
whole execution.

## Preservation contracts

`step_engine` and `step_original` identify the unchanged engine transition and
emission. `step_silent` and `step_emitted` specify consumer stuttering and ticking.
`step_reference` composes the engine's one-step refinement: the state before
command `n` advances to the boundary `n+1`, while its event stays at processing
position `n`.

`run_factor` proves the universal finite factorization. On the proof side, first
compute the engine's event list, then run the existing feedback runner with
`responseMealy` over that list. The pipeline's full event list is their zip, and
its final state contains exactly those two final component states. This is a
specification of the incremental runtime, not its implementation. Each response
input produces one optional observation, so silent positions are retained.

`response_run_completed` connects this position-preserving execution to the
existing `FRPSpec.Feedback.consume`: filtering silent derived outputs after
execution recovers the completed-batch outputs, with the same retained consumer
state. This finite comparison does not define an infinite event filter or identify
processing positions with completed-batch ticks.

`run_consumer_related` permits different consumer state representations. One
local output/state law is lifted using the existing `Feedback.run_related`,
preserving the entire paired optional-event list and relating final consumer
states. The checked wired consumer uses the Unit/product projection relation
from #228, rather than equality of differently represented machines.

`compiled_reference` composes three existing obligations:

- The scalar backend supplies its ordinary first-order `Sound` evidence.
- Source seed and body have types `[] → state` and
  `[input,state] → output × state`; an explicit payload observation supplies
  the input, such as `List Nat.sum`.
- `Engine.Corresponds` identifies concrete commands and the packets at their
  pre-consumption reference cursors, including rejected packets.

The conclusion equates every paired event and both final states with reference
demand events driving the independently interpreted source machine. The proof
uses `Engine.run_refines` and `ReactiveCompiler.realize_compile`. Compatibility
never assumes equal outputs, successful delivery, or eventual responses. The
source fragment remains the existing first-order unit/product/primitive language
with an explicitly initialized transition body.

## Run and inspect the examples

From the repository shell:

```sh
direnv exec . lake build Examples.ReactivePipeline
direnv exec . lake env lean Examples/ReactivePipeline.lean
```

[ReactivePipeline.lean](../../Examples/ReactivePipeline.lean) proves and evaluates
a literal command script with early processing, ordered left fragments, silent
right advancement, and delivery. Its four silent paired events are followed by
`(some (2,[3,4,3]), some (1,10))` for the compiled count/sum consumer. The wired
consumer retains the same original response and observes `(1,11)` instead.

Checked cases include known-empty delivery with observation `(1,0)`, duplicate
registration after completion, rejected packets before and after delivery,
stalled frontiers, and repeated processing. A concrete cut before right-source
readiness resumes to the same full state and event list. Universal applications
exercise the compiled-reference theorem, the wired state relation, and the
completed-batch comparison, beyond the executable outputs.

This is still the two-source, one-shot protocol. There is no new liveness theorem:
conditional delivery remains with `Engine.eventual_response`, under its explicit
source availability, fair consumption, frontier advancement, and enabled
processing assumptions. Compilation and consumer composition establish none of
those environmental premises. Request lifecycles, cancellation, external IO,
concurrency, crash recovery, reclamation, and cost bounds remain outside this
experiment. The [clock-boundary assessment](multimodal-reactive-assessment.md)
still applies; this pipeline requires no modal or cursor-transport framework.

The [identified request lifecycle](request-lifecycle.md) extends this one-shot
protocol with sequential sessions while retaining source and consumer state.
