# When FRP requests can omit identifiers

Explicit request identifiers are unnecessary for some useful reactive protocols.
The existing initialized machines already execute without them. A sequential
request interface can also omit them if its communication contract prevents
old operations from being admitted as new operations. Timing can help establish
that contract, but the repository's present causality and signal-stability laws
do not establish it.

This is a source-based assessment and proposed experiment for
[#232](https://github.com/VladimirMarko/conaled/issues/232), coordinated with the
driver [#233](https://github.com/VladimirMarko/conaled/issues/233), indefinite
service [#234](https://github.com/VladimirMarko/conaled/issues/234), and durability
[#225](https://github.com/VladimirMarko/conaled/issues/225). No new protocol,
identifier-erasure theorem, timer implementation or memory bound is formalized
by this note.

## Existing identifier-free execution

[`Feedback.Initialized`](../../Applications/Progress/Feedback.lean) stores an
initial state and a transition `A × S → B × S`. A transition returns its output
directly. The interface requires no request ID or retained execution counter;
a particular choice of state `S` may still contain either.
`Feedback.state` and `output` use natural-number positions to specify streams;
those positions are not fields of the transition state. `Feedback.run` returns
a finite output list, so indefinitely retaining that list would be a separate
resource problem.

[`Feedback.seq` and `par`](../../Applications/Progress/Reactive.lean) pass values
directly between synchronous transitions. `seq_output`, `par_output`, `run_seq`
and `run_par` establish the corresponding stream and finite-run meanings.
These constructions need no request correlation metadata. A backend that adds
queues, asynchronous callbacks or retries would need a further preservation
contract; those mechanisms are absent from these definitions.

The one-shot [`Engine`](../../Applications/FRP/Engine.lean) and
[`Pipeline`](../../Applications/FRP/Pipeline.lean) also have no request IDs.
`Demand.Request` moves from absent to pending to done, and `Demand.next_done`
makes done permanent. That supplies one-shot at-most-once emission, not repeated
identifier-free request service. `Pipeline.responseMealy` consumes an actual
optional emission: absence stutters, while every present batch, including an
empty one, advances the consumer. See
[`Demand.next`, `emit`, and `at_most_once`](../../Applications/FRP/Demand.lean).

## What timing and causality establish

| Existing contract | What it supplies | Missing obligation for removing IDs |
|---|---|---|
| [`Temporal.Synchronous`, `state_prefix`, `response_prefix`](../../Applications/FRP/TemporalCausality.lean) | Output/state depends on the relevant input prefix, without anticipating later actions. | A causal machine can remember its entire past. Causality gives neither bounded lookback nor exclusion of delayed or replayed commands. |
| [`Digital.correct`, `compose`, `matrix_stable`](../../Applications/Timing/Digital.lean) | Stable input signals yield the specified Boolean output throughout calculated stability intervals; composition preserves that relation. | Signal stability does not identify message instances or establish their maximum lifetime, admission multiplicity, or disappearance from buffers. |
| [`Interval.contains_shift`, `finite_mul`, `finite_add`](../../Applications/Timing/Intervals.lean) | Exact algebra for shifting and intersecting stability bounds. | A transport-lifetime or request-admission interpretation needs its own model and proofs. The current algebra is not already such a model. |

The digital gate templates permit signed rational shifts. Even causal physical
delay assumptions would therefore need explicit restrictions when reusing them
for a clocked implementation. [ADR 0008](../adr/0008-timing.md) also explains why
empty or inverted stability intervals cannot be treated as usable observation
windows. A timing-based request protocol must prove that its sampling/admission
windows exist and that its external signals or messages meet their contracts.

Event timestamps, wall-clock time, processing positions and completed-batch
positions must remain distinct. A source frontier establishes completeness of
event data at earlier event timestamps. It does not establish that an old
`begin` or `process` command has left an external transport. This separation
also follows from the concrete command handling in
[`Lifecycle.step`](../../Applications/FRP/Lifecycle.lean).

## Proposed exclusive-current-request interface

A candidate interface accepts `begin time` only when no request is pending,
processes the current request with an untagged `process`, and returns its
timestamped batch directly to the sole owner. Accepting a subsequent begin
resets only the request cell; source and consumer states remain retained.
This repeated-request wrapper is proposed, not implemented.

Its simplest realization is one local owner making serialized calls, consuming
each response before beginning the next request. The caller performs each
intended begin once. No old callback, queued begin or deferred response can
survive into a later request. Processing is defined as a generic scheduling
action on the current pending work, rather than an operation targeting a named
request. Several such scheduling actions are harmless after completion until
another request is accepted, at which point they concern that new current work.

These are communication and ownership requirements. A single outstanding request
alone does not supply them, and an ordered channel may still deliver duplicate
begins. A typed session description could make legal phases explicit, but an
external adapter must still implement its admission and isolation assumptions.

The comparison with today's identified lifecycle is:

| Current guarantee or observation | Identifier-free candidate |
|---|---|
| Accepted versus busy begin | Retain using the pending request cell. Busy must not reserve a later request. |
| Stale begin rejection based on the last accepted ID | Omit this observation. Rejecting replay requires a boundary contract; repeated equal arguments cannot reveal whether the caller intended a new request. |
| Only matching-ID processing affects the current request | Replace with generic current-request processing. If request-specific deferred processing must remain distinguishable, untagged processing is insufficient. |
| Global `Lifecycle.at_most_once` for each ID | Replace with at most one emission per accepted request occurrence. Occurrences can be indexed in the proof trace without retaining a runtime counter. This does not identify retransmissions as one logical request. |
| Response provenance and sound batches | Prove provenance from the accepted occurrence and reuse engine completion evidence. Named-ID provenance is no longer an observable property. |
| Repeated queries at the same event timestamp | Retain as separate accepted occurrences; timestamps cannot serve as unique identities. |
| Retained source/consumer state and silent consumer stuttering | Preserve through request reset and the existing response adapter. |
| Conditional eventual response | Re-establish using source advancement and scheduling of current pending work. Removing IDs does not create those conditions. |

The current stronger named-request results are in
[`LifecycleSafety`](../../Applications/FRP/LifecycleSafety.lean), with progress in
[`LifecycleProgress`](../../Applications/FRP/LifecycleProgress.lean).
[`Examples.RequestLifecycle`](../../Examples/RequestLifecycle.lean) checks both
a repeated timestamp with a new ID and rejection of the previous request's
processing command. An erasure comparison must restrict input traces or change
the processing observation; erasing every ID from arbitrary existing traces
would not preserve those behaviors.

## Positive and negative scenarios

**Proposed positive scenario.** A local owner requests timestamp `2`, waits for
the two frontiers to pass `2`, and processes the response synchronously. After
receiving it, the same owner requests `2` again. Retained source knowledge can
answer without new source packets, while the consumer advances a second time.
Only pending/done state and the current timestamp are needed for request
control. No growing request identity is needed. This extends the pattern checked
with IDs in `Examples.RequestLifecycle`; the identifier-free extension still
needs its own checked implementation and refinement theorem.

**Replay counterexample.** After the first response, the receiver sees
`begin 2`. In one history the caller deliberately repeats the query. In another,
the transport replays the previous begin. If receiver state and incoming command
are identical, a deterministic receiver takes the same action in both cases.
It cannot both accept the intended repeat and reject the replay without
additional distinguishing evidence or a contract excluding the replay. Delivery
order, causal processing and stable payload values do not distinguish them.

**Overlap counterexample.** A delayed `process` intended for a completed request
arrives after the next request has become pending and ready. With IDs the old
command stutters. Erasing its ID lets it complete the new request. This is
permitted under generic current-work scheduling, but fails preservation of the
existing request-targeted behavior. Delayed responses crossing the same boundary
create a corresponding correlation problem for an external caller.

## Timing or quiescence contracts that could suffice

An alternative to synchronous calls is an explicit quiescence barrier. Before
opening the next request, the producer stops generating old operations and the
barrier establishes that all old commands and responses are consumed, discarded
or permanently unable to affect later requests. Merely observing an empty local
queue does not establish that remote producers or buffers are drained.

A bounded-lifetime transport could implement such a barrier by waiting after
old traffic stops. Its lifetime bound must cover delayed copies, retries,
intermediate buffers and responses, with stated clock-error and scheduling
assumptions. It must also prevent multiple admissions of one begin during the
same request window. If delayed production remains possible, waiting from the
first send time is insufficient. A windowed implementation needs nonoverlapping
admission phases and proof that traffic from each phase cannot enter a later
one. These are candidate contracts, not consequences of `Digital.correct`.

Any finite phase or timer implementation must justify reset and wraparound.
Replacing IDs with increasing timestamps, epochs or retained global tick counts
would move the growth elsewhere. A finite relative timer or reusable phase can
avoid that representation growth only under a contract ruling out surviving old
traffic when it is reused. Proof-only trace indices are acceptable; executable
metadata and timer state must be included in the resource accounting.

Restart complicates both approaches: resetting local state does not erase old
external traffic or an already-published response. The driver and durability
workstreams must specify fresh transport isolation, a proved drain/lifetime
condition, or another recovery protocol. Local emission and externally
acknowledged delivery remain different observations.

## Bounded comparison experiment

#232 should compare the current lifecycle with a small identifier-free wrapper
under the exclusive-owner contract before choosing bounded ID reuse. Prove
per-accepted-occurrence emission safety, batch soundness, retained state, repeated
same-timestamp queries, and finite-run preservation after the chosen observation
erasure. Include replay and delayed-processing counterexamples. Use existing
engine transitions and consumer transport rather than another reactive evaluator.

For #234, compare a finite-value synchronous delay realization that already needs
no request identity. Account separately for timestamps, source history, payloads,
consumer state, buffers and output consumption; removing lifecycle IDs alone
does not bound those resources. For #233, select whether the external protocol
can implement exclusive admission or must retain explicit correlation. Coordinate
restart acceptance with #225 instead of assuming that every new process starts
with an empty environment.

For [#231](https://github.com/VladimirMarko/conaled/issues/231), this supplies a
preservation test involving assumptions as well as outputs: a translation may
erase correlation metadata only on traces satisfying its isolation contract,
and may preserve occurrence observations without preserving named-ID ones.
Composing adapters must preserve that contract, including traffic lifetimes and
buffer bounds where used. It is a useful extension case for composable laws,
without requiring every guarantee to become a scalar timing bound.
