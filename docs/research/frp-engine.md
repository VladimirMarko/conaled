# Incremental one-shot demand engine

[Engine.lean](../../Applications/FRP/Engine.lean) implements the bounded demand
protocol from [the demand experiment](frp-demand.md). A caller supplies one
`Command` to `step` and receives a new `MachineState` and an optional response.
The machine retains two concrete source states and one request cell. It needs
neither future source streams nor an action history or global cursor. The
`sources` function is a view of the two stored fields; `pack` evaluates both
source projections when constructing the next state, avoiding a retained chain
of source-update closures. Source logs are still retained, and no memory or
execution-cost bound is claimed.

Commands register a query, supply a concrete packet for one source, request
processing, or idle. Source updates reuse `Trace.process`; request transitions
and emissions reuse `Demand.next` and `Demand.emit` on the **pre-command** state.
Only processing can emit. It returns a response and marks the request done in
the same transition. A duplicate registration is ignored while pending and
after delivery. Rejected packets leave source knowledge unchanged; the caller
has nevertheless consumed that packet. Silent-source frontier advancement can
enable a response, and `some (t, [])` remains distinct from `none`.

`run` accepts a finite list of concrete commands and returns the final state and
one optional event per command. [FRPEngine.lean](../../Examples/FRPEngine.lean)
checks and evaluates a literal script: register time 2, process too early,
supply ordered left fragments `[3,4]` and `[3]`, close the silent right source,
and process. Its event sequence is
`[none, none, none, none, some (2, [3,4,3])]`. Other checked scripts cover packets
before registration, strict frontier crossing, empty output, duplicate
registration, and rejected late packets before and after delivery.

## Refinement contract

`reference s ms actions n` packages the reference source knowledge and request
cell at the boundary **before** action `n`. `commandAt` translates that action;
a source command receives `ms source (count schedule source n)`. The count is
before consumption and advances even when validation rejects the packet.
These streams and cursors belong to the proof relation, not the runtime state.

`step_refines` identifies both the next stored state at `n+1` and the event at
`n`. `Corresponds` recursively constrains only command kinds and packet values.
`run_refines` proves equality of the final state and the entire ordered optional
event list for any finite sequence satisfying that relation. It does not assume
output agreement or discard silent positions. The literal eight-command
`referenceScript` demonstrates this theorem across a rejected second packet.
A caller can execute the finite runner without constructing any reference
stream; streams are needed when comparing that execution with a chosen
reference trace.

For infinite-execution statements, `state` iterates the same retained-state
`step`, and `emission` selects its event. `Aligned` is the pointwise command-only
correspondence. `state_refines` and `emission_refines` transfer the existing
public demand results:

- `response_sound` quantifies over every completion of current source knowledge.
- `response_honest` uses the existing `responseSquare` to connect an emission to
  external truth, retaining initial completion and accepted-window honesty.
- `registration_order_agrees` compares executions with the same ordered source
  streams, allowing different interleavings and registration positions.
- `pending_or_emitted`, `response_registered`, and `at_most_once` establish no
  lost work, strictly earlier registration, and no second response. The local
  `no_lost_work` also applies directly to any machine state and command.
- `step_valid` and `run_valid` preserve validity without assuming source honesty.

Initialization sets the request absent and stores the supplied source states.
For `initial w`, `initial_completes` explicitly requires the source to be empty
before `w`. The examples disprove unconditional completion for a nonempty past.
Packet validation checks window shape; it does not certify an external source's
truthfulness.

## Delivery and limits

Engine `ProcessingFair` says that a pending request whose sources are ready
will eventually receive a processing command. It mentions scheduled commands,
not eventual emission. `processing_fair_refines` derives the reference fairness
premise through alignment. `eventual_response` then reuses the reference theorem
with explicit source availability, legal consumption, fair delivery, and
available prefixes that strictly cross the requested timestamp.

A concrete command stream discharges all these obligations and delivers the
ordered answer. Separate examples retain the two failure modes: stalled
frontiers despite fair processing, and a ready request whose consumer is never
scheduled. Neither the finite runner nor initialized state supplies missing
commands or fairness. Processing positions are preserved, so the clock warning
in [the multimodal assessment](multimodal-reactive-assessment.md) still applies:
filtering `none` events changes the clock, while an empty emitted batch counts
as a response.

This remains an experimental alternative alongside `Trace` and `Demand`, whose
implementations are unchanged. The [shared-transition assessment](frp-shared-transitions.md)
requires no new Felix construction here: local command correspondence supplies
the implementation obligation, then public demand theorems supply the reusable
safety and conditional-progress arguments. This is a pure two-source, one-shot
engine, without multiple requests, switching, graph scheduling, concurrency,
external delivery, reclamation, or a general FRP runtime claim.
