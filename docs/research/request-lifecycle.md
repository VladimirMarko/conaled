# Sequential identified requests

[Lifecycle.lean](../../Applications/FRP/Lifecycle.lean) extends the
[incremental engine](frp-engine.md) with natural-number request IDs. Its retained
state contains the engine's two concrete source states, its request cell, and
an optional last accepted ID. It stores no request history or completed-ID set.

Commands are `begin id time`, `source which packet`, `process id`, and `idle`.
A begin while pending returns `busy`, even when its ID would otherwise be stale.
It changes neither sources nor the accepted-ID mark. When idle or done, a begin
is accepted only if its ID exceeds the previous accepted ID, or no ID has been
accepted. Otherwise it returns `stale`, even if the timestamp changed. A fresh
ID rejected as busy can therefore be retried after completion.

An accepted begin retains the sources and initializes the request cell through
the existing absent/register behavior (`registered_engine`). Matching processing
uses the engine; an unknown or old processing ID stutters. Source commands use
unchanged window validation. Each command returns an optional begin status and
an optional response containing ID, timestamp, and ordered payload. `some []`
is a completed empty batch; silence remains `none`.

## Safety across session boundaries

`session_step` and `session_run` compare a fixed-ID session with the one-shot
engine. Their `Segment` premise excludes an accepted begin at each step; busy or
stale begins and wrong-ID processing project to idle. The finite theorem equates
the final engine state and every optional response position, tagging the latter
with the fixed ID. It does not filter silent processing positions.

[LifecycleSafety.lean](../../Applications/FRP/LifecycleSafety.lean) supplies
properties that also cover arbitrary later accepted sessions:

- `marks_monotone` and `accepted_increases` track the accepted-ID mark.
- `response_provenance` finds an earlier accepted begin with exactly the emitted
  ID and timestamp, starting from `init`.
- `at_most_once` rules out a second response with the same ID anywhere later in
  execution. Its `Finished` invariant survives source updates and newer sessions.
- `no_lost_work` and `pending_or_emitted` retain the pending ID and timestamp
  until a response is emitted. Busy begins cannot reset pending work.
- `run_valid` and `state_valid` preserve source validity; `response_sound` returns
  the ordered left/right batches under completion hypotheses for the current
  retained sources.

Source validity alone does not identify an external truth. Fixed-truth claims
still require the existing completion and accepted-window honesty obligations.
A new session starts from its actual retained knowledge, not fresh empty logs.
The checked second session answers the same timestamp from the previous session's
retained packets.

## Conditional progress

[LifecycleProgress.lean](../../Applications/FRP/LifecycleProgress.lean) reuses
`Engine.eventual_response`. Its `eventual_response` theorem starts with a pending
accepted ID and actual retained source states. A reference stream has one
synthetic registration followed by the fixed-ID projection of actual commands.
Packet alignment refers to pre-consumption source cursors. Delivery availability,
fair source consumption, frontier advancement, and matching-ID processing
fairness remain explicit environmental assumptions.

Wrong-ID processing cannot witness `ProcessingFair`. Rejected begins create no
new delivery obligation. The conclusion permits later accepted begins after the
response: it does not assume that the current ID remains active forever. In the
proof only, supposing that this response never occurs keeps the request pending
by no-loss, excludes accepted resets, and supplies the one-shot simulation needed
for a contradiction with engine progress.

## Continued compiled observations

[LifecyclePipeline.lean](../../Applications/FRP/LifecyclePipeline.lean) pairs the
lifecycle state with a retained consumer state. Each runtime step passes that
command's actual response through the existing `Pipeline.responseMealy`, forgetting
the ID only for the consumer input. Its output retains the entire original
status/tagged-response event separately from the optional derived observation.
Every begin preserves consumer state, including accepted begins.

`run_factor` specifies the full finite event list and both final states;
`run_append` supports chunked execution. `event_run` reduces the adapter to the
existing response runner. `run_consumer_related` uses that runner's relational
transport theorem for different state representations. `compiled_run` uses
`ReactiveCompiler.realize_compile` to equate arbitrary lifecycle executions of
the compiled seed/body and their source meaning. No reference history or
precomputed response trace is an input to the runtime step.

[RequestLifecycle.lean](../../Examples/RequestLifecycle.lean) checks ID0 at time2
with `[3,4,3]`, followed by ID1 at time2 with no new packets. The compiled count/sum
consumer observes `(1,10)` then `(2,20)`. Cases cover changed-timestamp replays,
busy fresh-ID retry, old-ID processing, rejected packets, known-empty delivery,
source validity, generic session refinement, wired-consumer transport, compiled
correctness and chunked execution. A second-session progress theorem discharges
availability and processing premises without assuming an emission. Separate
stalled-source and wrong-ID scripts exhibit why both progress assumptions matter.

Run the executable example inside the repository shell:

```sh
direnv exec . lake build Examples.RequestLifecycle
direnv exec . lake env lean Examples/RequestLifecycle.lean
```

This is local at-most-once emission with unbounded natural IDs. A bounded wire
format needs an exhaustion policy. Concurrency, cancellation, queued requests,
ID reordering, external acknowledgments, crash recovery, IO, reclamation and
performance bounds remain outside these contracts.
