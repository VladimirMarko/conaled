# Exclusive requests without runtime identifiers

[#236](https://github.com/VladimirMarko/conaled/issues/236) implements the
exclusive-current-request experiment proposed by the
[request-identity assessment](frp-request-identity.md). A caller can repeatedly
request the same timestamp while retaining source knowledge and compiled
consumer state. Increasing occurrence labels exist in the proofs, not in the
runtime state or commands.

The contract is one local owner making serialized calls, admitting each intended
begin once, and consuming each response before beginning another request. An old
request-targeted callback is not a generic scheduling action under this contract.
There is no cancellation, retransmission, concurrent callback, or restart
protocol. The existing identified lifecycle remains available when stale-request
rejection is part of the required observation.

## Runtime and observations

[`Exclusive.step`](../../Applications/FRP/Exclusive.lean) accepts `begin time`,
a concrete source packet, `process`, or `idle`. Its state is exactly
`Engine.MachineState`: the two source states and the absent/pending/done request
cell. A begin while pending returns busy and preserves all state; it neither
queues nor reserves another request. An accepted begin resets only the request
cell. Source/process/idle commands use the existing engine transitions.

Each output retains an optional admission status and an optional timestamped
batch. Repeated equal timestamps are distinct accepted occurrences. A response
is an event at the processing transition, not a stored value emitted again by
later polling. The existing strict-frontier, packet-validation, completion,
order and multiplicity semantics are unchanged.

[`Exclusive.Pipeline`](../../Applications/FRP/ExclusivePipeline.lean) adds only
the chosen consumer state. It calls the existing `Pipeline.responseMealy` on the
actual response. Silence stutters; a present empty batch advances the consumer.
`run_factor` relates arbitrary finite command execution to that adapter,
`run_consumer_related` reuses its existing relation transport, and `compiled_run`
recovers the source consumer from the compiled body. Source syntax is not
reinterpreted at every transition.

## Constructed reference and guarantees

`labelCommand`, `nextLabel`, and `lift` construct an identified reference trace
from the concrete commands and actual admission states. Each accepted begin
receives the next proof label; busy begins do not advance it. Generic processing
targets the current label. The reference starts with `some 0` as its reserved
high-water mark and the same engine state; for an initialized client the request
is absent and the first accepted occurrence receives label 1. This is an explicit
related initial state, not an assertion that it equals `Lifecycle.init`.

`step_refines` proves exact reference state, status and tagged response equations.
`run_refines` lifts them over arbitrary finite inputs and preserves each event
position and final engine state. Its premises do not assume response agreement.
The status erasure function maps stale to busy to be total, but the stronger
step theorem proves that the constructed trace produces only accepted/busy
statuses. It does not claim equivalence on arbitrary identified input traces.

The infinite command-derived `label` and `labelled` functions support the same
state and event equations. `label_accepted` advances a label strictly on an
accepted occurrence. `at_most_once` reuses the identified lifecycle theorem to
show that two response positions have different occurrence labels, even when
timestamps and batches agree. `response_provenance` identifies a strictly earlier
accepted begin with the response timestamp and the same occurrence label. Thus
there is no response from the initially reserved label. Local `emitted` and
`no_lost_work` retain pending-work and completion behavior. `response_sound`
requires current completion evidence for both sources; packet validity alone
is not source honesty. Validity is preserved by steps and finite runs.

[`ExclusiveProgress.eventual_response`](../../Applications/FRP/ExclusiveProgress.lean)
uses the existing engine delivery theorem. Its assumptions describe actual
commands: source-stream alignment, finite closing prefixes and their availability,
fair source consumption, and scheduling of generic process commands when work
is enabled. It does not assume eventual output. A temporary silence argument
keeps the request pending and therefore prevents accepted resets until delivery.
Later begins after completion are unrestricted. Closing prefixes may have length
zero, so retained knowledge can answer without new packets. These progress
assumptions concern the pure atomic machine, not external transport.

## Checked clients and statement review

[`Examples.ExclusiveRequests`](../../Examples/ExclusiveRequests.lean) runs the
compiled count/total consumer on concrete packets. Two requests at timestamp 2
produce `[3,4,3]` twice and final aggregate `(2,20)`; the second uses retained
source knowledge. The emitted finite script is also evaluated by Lean's
executable evaluator.

| Claims | Checked use and statement review |
|---|---|
| Admission, source retention, finite and step simulation | Busy begin preserves the pending request; rejected packets preserve knowledge; the constructed six-command lift uses labels 1 and 2. The arbitrary-list example consumes `run_refines`. Initial reference state and label erasure are explicit. |
| Occurrence safety and timestamp provenance | Universal examples consume `at_most_once` and `response_provenance`, including equal timestamps/batches. Labels identify admitted occurrences, not transport retransmissions. Helper state/event equations are exact for every command. |
| Soundness and validity | The retained second request uses `response_sound` with arbitrary compatible completions. Arbitrary finite commands preserve valid source states. The empty-past initialization assumption remains with the underlying source model. |
| Consumer preservation and compilation | Wired and direct consumers use `run_consumer_related`; the compiled aggregate uses `compiled_run`. Chunking consumes `run_append`. Two empty responses advance the count twice while silent processing does not. |
| Conditional progress and its limits | `second_eventually` supplies actual alignment and fair processing, with zero available packets and already-closing retained frontiers. A stalled-source execution processes forever without output and fails the closing-prefix premise. An idle ready execution emits nothing and fails processing fairness. |
| Observation and resource counterexamples | An old targeted process command stutters in the identified model while generic processing completes the new request. Repeated begin arguments are accepted after completion, so replay cannot be rejected as a different intent. `empty_count n` proves count `n` after `n` empty-response cycles through the public runner. |

Statement review covered every new theorem family, including the local
initialization/session helpers: quantifier scopes, pre/post state positions,
accepted rather than merely attempted begins, strict ordering of provenance,
exact optional emissions, and satisfiability of progress assumptions. The
single-step simulation derives output equality from transitions; the finite
and infinite lifts derive their labels from commands. None adds an axiom or a
fairness premise that already asserts response delivery.

## State size and acquisition boundary

The executable state inventory is:

- two `Frontier.State` values, each with a frontier and accepted source log;
- one `Demand.Request` phase, carrying a timestamp while pending;
- the arbitrary consumer state in the pipeline.

There is no occurrence counter, epoch, timestamp-as-identity, stored proof trace,
or labelled reference state in this inventory. The label constructors are
specification functions and are not called by `step`, `run`, or pipeline execution.
The caller supplies actual packets and serial commands. Packet validation does
not prove the source's completion/honesty promises or ensure that an external
adapter admits a begin only once.

This inventory is not a memory bound. Timestamp/payload encodings, complete source
logs, consumer values, temporary allocations, input buffers and caller-retained
responses remain separate costs. The checked unbounded count consumer makes the
limitation concrete even when every batch is empty. `run` returns a finite event
list; indefinitely retaining successive transcripts consumes space. Streaming
`step` calls can discard consumed outputs, but no physical allocator guarantee
is proved here. [#237](https://github.com/VladimirMarko/conaled/issues/237) owns
query-retention reclamation; the finite circuit service from #234 has a different
resource contract.

The result supplies an optional consumer without changing the shared preservation
interface. Existing engine and lifecycle proofs discharge safety, existing
optional-response laws discharge consumer transport, and engine progress supplies
delivery. No new preservation-family mismatch was needed. #235 retains broader
architecture ownership. No default transport, global identifier-removal policy,
or further implementation ticket follows from this bounded result.

## Validation scope

The three implementation modules and checked clients are imported through
`SquareApplications.lean` and included in the normal exhaustive proof audit.
The task handoff records the exact candidate, targeted build and executable
output, candidate build/audit and final verification. Independent Standards,
Spec and requested originating-context review belong to the enclosing workflow.
