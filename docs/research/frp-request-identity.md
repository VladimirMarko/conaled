# When FRP requests can omit identifiers

Ownership update: #193 is closed and supplies completed measured-execution
evidence. Historical assignments to #193 below are not an active work queue;
use the [current residual-owner map](workstream-status-reconciliation.md) for
new resource, runtime and error-comparison work.

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

## Admission, cancellation and recovery boundaries

The local synchronous machine associates each result with the call returning
it. There is no retransmission or cancellation command. The proposed exclusive
request adapter retains that association across several calls: the sole owner
keeps its current request until the response is consumed, and source commands
remain ordered per source. A busy begin changes neither the request nor the
consumer and is not queued. A retry after a response is a new accepted
occurrence, even if its timestamp equals the previous one. An untagged process
always concerns current work; it carries no claim about an earlier request.

For the first experiment, cancellation is unsupported. A caller cannot abandon
a pending request and start another by discarding its own handle. Adding cancel
would require a specified linearization point relative to emission and a rule
for disposing of outstanding responses before ownership is reused. Under
windowed delivery, retransmission is permitted only if the admission mechanism
ensures one acceptance per intended occurrence. Nonoverlapping windows alone
do not prevent two copies being accepted in one window after an early response.
Ordered delivery also does not eliminate duplicates.

Neither today's lifecycle nor this candidate implements crash recovery. A
restart must establish a new isolated communication context or recover the old
one consistently. Resetting `last` to `none` accepts a delayed old begin;
restoring an earlier checkpoint can accept IDs whose effects occurred after
that checkpoint. Persisting a high-water mark alone does not atomically commit
the consumer update and external response. Recovery must specify which of
local emission, durable state transition and acknowledged external delivery is
the observation it preserves. [#194](https://github.com/VladimirMarko/conaled/issues/194),
[#225](https://github.com/VladimirMarko/conaled/issues/225) and
[#226](https://github.com/VladimirMarko/conaled/issues/226) retain those decisions.

## State audit and explicit representation model

This assessment uses a structural binary-encoding model, not Lean allocation
measurements. Let `b(n) = max(1, ceil(log₂(n+1)))` bits for a natural number,
`cT(t)` and `cA(x)` for chosen encodings of time and payload, and `cS(s)` for the
consumer state. Constructor tags and list cells have fixed positive overhead
in this model. Shared storage is counted once when live; the estimates below
can conservatively count duplicated values. Transient allocations, stack use,
serialization buffers and runtime overhead require a backend-specific model
before a physical bound can be claimed.

| Actual state or operation | Representation and retention obligation |
|---|---|
| [`Lifecycle.State.last`, `Fresh`, `classify`](../../Applications/FRP/Lifecycle.lean) | One optional `Nat`, costing a tag plus `b(M)` for last accepted ID `M`. It is not a list of completed IDs. Callers may jump directly to a large ID, so command count alone does not bound its width. A pending request returns busy before testing freshness. |
| `Engine.MachineState.request` | A finite phase tag and, while pending, one timestamp of cost `cT(t)`. No bound on `T` is supplied by `LinearOrder T`. |
| [`Frontier.State.frontier`, `.log`, `advance`](../../Applications/FRP/Frontier.lean) | Two source frontiers and two lists of timestamped batches. Successful advancement uses `s.log ++ xs`; it retains every accepted log entry, including explicitly stored empty batches. Storage is proportional to cells plus encoded timestamps and payloads, not just the number of requests. Rejected packets stutter via [`Trace.process`](../../Applications/FRP/Trace.lean). |
| [`Lifecycle.Pipeline.State.consumer`](../../Applications/FRP/LifecyclePipeline.lean) | An arbitrary `S`. The checked count/sum consumer in [`Examples.RequestLifecycle`](../../Examples/RequestLifecycle.lean) has natural-number components. Repeated empty responses still increase its count. A finite number of fields does not bound their encodings. |
| `Response`, `Event`, incoming packets | IDs, timestamps and complete batches can themselves be large. A driver must bound or stream inputs and outputs under an explicit semantics; bounding retained machine state does not bound a single input allocation. |
| `Lifecycle.run`, `Lifecycle.Pipeline.run`, `Feedback.run` | Return finite output lists whose cells grow with the executed input length, including silent events. Streaming repeated `step` calls can discard consumed outputs, but calling `run` on an ever-growing transcript does not. Caller-retained commands, responses and old states also count against a whole-program bound. |

For a source log with entries `(tᵢ, xsᵢ)`, a conservative encoded-size expression
is a constant plus `Σᵢ(cell + cT(tᵢ) + Σₓ∈xsᵢ(cell + cA(x)))`.
The two logs, frontiers, request, last ID and `cS(s)` must all be included.
Rational timestamps in the examples have unbounded numerator/denominator
encodings; replacing request IDs by those timestamps provides no fixed bound.

In a simple bit algorithm, comparing two binary IDs costs at most a constant
times the larger encoded width; increment can touch that many bits too.
This is not constant bit cost merely because the source contains one comparison.
For lists, packet validation traverses new entries, append traverses the old
list spine in a straightforward persistent implementation, and `batch` examines
the retained log. Payload concatenation and time comparison add their own
costs. These are structural cost warnings, not measured Lean performance or a
verified backend complexity theorem. [#193](https://github.com/VladimirMarko/conaled/issues/193)
owns measured cross-domain execution.

## If a client needs names

| Policy | Safety contract and service limit |
|---|---|
| Unbounded increasing `Nat` IDs, as implemented | Preserves stale rejection and global per-ID at-most-once within the mathematical execution. No namespace exhaustion, but width grows. Restart is outside this theorem. |
| Fixed `w`-bit IDs without reuse | Preserve the increasing-ID discipline by rejecting allocation beyond `2^w - 1`, with an explicit exhausted outcome. At most `2^w` accepted IDs from a fresh namespace; jumps reduce availability. Refusing work safely does not establish indefinite service. |
| Finite IDs reused after quiescence | All earlier traffic capable of acting on the reused name must be excluded. State safety per accepted occurrence or isolated session, not globally per numeric ID. The exclusion contract also covers responses, not only begins. |
| Session/epoch plus local ID | An unbounded epoch moves growth; a bounded epoch eventually exhausts or repeats. Reuse needs isolation or lifetime evidence for the complete tuple. A transport connection can supply scope only if old connection traffic cannot be admitted in the new one. |
| Random `w`-bit ID | Requires a distribution and collision policy. For independent uniform draws with replacement, the union bound for `k` draws is at most `k(k-1)/2^(w+1)`, capped at 1. This is a probabilistic bound under those assumptions, not deterministic global uniqueness or unlimited bounded-state service. |

A concrete hypothetical reuse failure uses two names, `0` and `1`. Complete
request `0`, complete request `1`, then reuse `0` for a ready new request. A
previously delayed `process 0` now matches it and emits its response. It would
have stuttered under the current never-reuse lifecycle. Similarly, after reuse
becomes permissible, a delayed `begin 0 2` and a deliberate new `begin 0 2`
are identical to the receiver. No finite-width comparison distinguishes them.
A delayed old response tagged `0` can also be assigned to the new request by
a caller. These examples concern a proposed reuse policy; today's `Fresh`
rejects reused IDs and has no wrapping operation.

`Lifecycle.at_most_once` states that two emissions at different positions have
different IDs. A functioning reused-ID protocol intentionally violates that
statement. Its replacement must quantify over accepted occurrences or scoped
identities, with proof-only occurrence indices when executable names are absent.
Identity scope and observation erasure belong in the preservation statement;
they cannot be hidden behind a type conversion from `Nat` to a finite type.

## History reclamation requires a query contract

Advancing a frontier certifies old data and leaves it queryable. For example,
retain a nonempty batch at timestamp `2`, advance both frontiers beyond `10`,
then accept a fresh request for `2`. The current semantics returns that batch.
Dropping entries below `10` silently changes it to empty even though the query
is ready. `Frontier.State.Completes` quantifies over *every* timestamp below the
frontier, so the same completeness relation generally fails after deletion.

The retention follow-up [#237](https://github.com/VladimirMarko/conaled/issues/237)
will introduce an explicit lower query boundary
`q`. It would accept queries only at `t ≥ q`, preserve any already pending
request when advancing `q`, and retain entries at `q` until the boundary moves
strictly beyond them. The evidence relation becomes completeness on
`q ≤ t < frontier`. The outside-range result must be a distinct rejection or
unavailability observation, not an empty batch. Previously promised future
queries, retry obligations and retained external handles must respect the same
boundary; source-frontier advancement alone is not that promise.

This follow-up is scoped as a query-policy and reclamation experiment: specify
the boundary-admission transition, prove admitted-query response equivalence
against the unreclaimed engine, and check a repeated boundary query, an old
query rejection, and refusal to invalidate pending work. Bound packet density,
retained timestamp/payload encodings and burst sizes separately. A fixed time
window with arbitrarily many entries or arbitrarily large payloads is not a
space bound. Persistent snapshots or archives, if used, must be accounted for
rather than shifting retained history outside the measured component. The
implementation proposal below leaves reclamation out and retains this explicit
follow-up under the FRP resource workstream.

## Bounded comparison experiment

The implementation follow-up [#236](https://github.com/VladimirMarko/conaled/issues/236)
compares the current lifecycle with a small
identifier-free wrapper under the exclusive-owner contract before choosing
bounded ID reuse. Prove per-accepted-occurrence emission safety, batch soundness, retained state, repeated
same-timestamp queries, and finite-run preservation after the chosen observation
erasure. Include replay and delayed-processing counterexamples. Use existing
engine transitions and consumer transport rather than another reactive evaluator.

For #234, compare a finite-value synchronous delay realization that already needs
no request identity. Account separately for timestamps, source history, payloads,
consumer state, buffers and output consumption; removing lifecycle IDs alone
does not bound those resources. The selected bounded-driver plan for #233 keeps
explicit IDs with no wrap or reuse, a finite frame budget and bounded input
encodings. It exercises today's stale and wrong-ID behavior without waiting for
the identifier-free adapter. An accepted maximum ID must remain processable;
exhaustion cannot silently discard pending work. This is a planned finite-run
policy, not an indefinite-service theorem. Coordinate restart acceptance with
#225 instead of assuming that every new process starts with an empty environment.

For [#231](https://github.com/VladimirMarko/conaled/issues/231), this supplies a
preservation test involving assumptions as well as outputs: a translation may
erase correlation metadata only on traces satisfying its isolation contract,
and may preserve occurrence observations without preserving named-ID ones.
Composing adapters must preserve that contract, including traffic lifetimes and
buffer bounds where used. It is a useful extension case for composable laws,
without requiring every guarantee to become a scalar timing bound.

The implementation issue should require the following prose theorem statements
as checked Lean claims, with concrete specializations. They are obligations,
not results established by this assessment:

1. **Reference simulation.** Given equal initial source/request states and related consumer states,
   lift an untagged command trace to a reference trace by assigning increasing
   mathematical labels to accepted occurrences. Busy begins use a fresh label
   without reserving it; process commands use the current reference label.
   Inductively prove equal source/request states, related consumer states and
   equal events after erasing response labels. The lift is proof machinery;
   neither its labels nor desired responses are runtime inputs. This restricted
   comparison does not claim preservation for arbitrary old labelled commands.
2. **Occurrence safety and meaning.** Each response belongs to a preceding
   accepted begin with the same timestamp, with at most one response before
   the next accepted begin. Under source completion evidence, its batch equals
   the left batch followed by the right batch. Silent transitions stutter the
   consumer; a present empty batch advances it once. Begin retains source and
   consumer state, including on repeated equal timestamps.
3. **Conditional progress.** For an accepted pending occurrence, sufficient
   source advancement and fair enabled current-work processing imply eventual
   response. A permanently stalled source or absent processing defeats this
   conclusion. Completion does not require a newly allocated runtime ID.
4. **Resource scope.** The adapter introduces no growing identifier or occurrence
   counter into runtime state. Any stronger uniform bound is conditional on
   bounded representations of timestamps, payloads, source logs, consumer state,
   communication buffers, transient working memory and output consumption.
   Under those bounds and progress assumptions, repeated operation need not
   exhaust an identity namespace. The experiment alone is not a proof of
   indefinite service for the current accumulating source/consumer examples.

Positive checked cases should include two requests at the same timestamp,
known empty batches, busy attempts followed by completion, and retained source
knowledge and consumer state. Negative cases should include replayed begin,
delayed old targeted processing, stalled source, and a growing count consumer.
The first two expose protocol/observation differences; the last two separate
progress and resource bounds from semantic preservation. The implementation
must retain the existing identified lifecycle for clients needing its contract.

## Implemented exclusive adapter

[#236's implementation](exclusive-request-adapter.md) now supplies the bounded
exclusive-current-request adapter, its command-constructed labelled reference,
occurrence safety and progress proofs, and retained compiled consumers. The
proposals above record the assessment that preceded it. The implementation keeps
its serial admission boundary and does not extend arbitrary identified traces by
erasure. Query-retention reclamation remains with #237.
