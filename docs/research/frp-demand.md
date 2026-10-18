# One-shot demand delivery

Status: experimental. [Issue #30](https://github.com/VladimirMarko/conaled/issues/30)
extends the [two-source traces](frp-traces.md) with a registered consumer and an
observable response. The [complete-window protocol](frp-runtime-scope.md) and
existing implementations remain available. This experiment leaves #27 open.

## Atomic transition model

[Demand.lean](../../Applications/FRP/Demand.lean) accepts a stream of actions:
register a timestamp, consume the next message from one source, process consumer
work, or idle. Each action is atomic. `sourceSchedule` erases consumer actions;
`Trace.run_step` supplies the local source transition, preserving stream order
and consuming rejected packets without changing certified knowledge. `request`
recursively updates a separate request cell with `next`. Together these functions
compute the state before each action. `response` is the event emitted by that
action, and includes the query timestamp and exact output list.

The request cell starts absent. Registration changes it to pending. Any later
registration is ignored, even if it repeats the same timestamp or occurs after
delivery. A processing action on a pending, ready query emits its batch and
changes the cell to done in the same atomic transition. Processing before
readiness leaves the request pending. Source updates and idle actions preserve
the cell. Done is absorbing; no stored answer is re-emitted.

The pending cell is the work representation. There is no notification edge to
consume or queue entry to drop. Enabled work means a pending request whose two
source frontiers strictly exceed its timestamp. A processor can deliver that
work in one transition. `no_lost_work` proves that every transition preserves
the pending request unless it emits. `enabled_persists_or_emitted` adds source
observation persistence: at any later state, the work still has an emitting
processing transition, or an intervening step already emitted. This covers
registration after readiness and readiness after registration without requiring
polling to have happened at the moment a frontier crossed the timestamp.

This is a pure executable model of atomic actions. It proves neither a concurrent
callback implementation nor external network delivery. Emission is delivery in
this model. The implementation recomputes source prefixes and retains logs; no
latency, allocation, or history bound is claimed.

## Safety and conditional progress

`response_sound` quantifies over every pair of completions of the source states
at the emission step. Its conclusion is exact left-before-right concatenation,
including order and multiplicity. `some (t, [])` certifies empty output; `none`
means no response event at that step, which can also happen before registration
or after delivery. It does not itself describe knowledge of the query.

Packet acceptance, source honesty, availability, and scheduling remain separate.
`responseSquare` reuses `executionSquare` and `mergeObservation` to connect an
emission to fixed source truths under the existing `traceRep` relation. That
relation supplies initial validity, initial completions, and honesty for every
accepted source window. `initial w` still assumes an empty past below `w`.
Equality with a frontier is insufficient for readiness; a silent source must
advance to certify absence.

`registration_order_agrees` compares emitted answers for the same query and
initial states/streams, allowing arbitrary registration order, interleavings,
and different consumed prefix lengths. It uses `interleavings_agree`, so it
needs no honesty assumption for agreement within those same streams. For
different representations sharing completions, `response_sound` gives agreement
through the common semantic batch. No comparison at equal global step counts
is asserted.

`eventual_response` starts with an unanswered registered request. Its assumptions
are:

- Each source supplies a finite prefix closing the query, and that prefix is
  available at some step.
- `Delivery` permits consumption only of available messages. `Delivery.Fair`
  eventually consumes every available finite prefix.
- `ProcessingFair` requires a processing action at or after any state containing
  enabled consumer work. It constrains actions, without assuming a response.

The proof obtains persistent source readiness from `eventual_observation`, then
uses preservation of pending work and consumer fairness to find an emission.
Safety and local readiness need none of these fairness assumptions. Honesty is
needed to identify the answer with external truth, but not to produce an answer.
`at_most_once` prohibits any later response following an emission, regardless
of its query or value. `pending_registered` and `emit_iff` require a registration
at a strictly earlier action for every response.

## Checked cases and statement review

[FRPDemand.lean](../../Examples/FRPDemand.lean) uses rational timestamps. The
first missing interface was a request/emission transition: the existing trace
could observe `[3, 4, 3]`, but could not express delivery to a registered consumer.
The retained expected list comes from the left packet's ordered fragments and
a silent advancing right source.

| Claims | Checked use and statement review |
|---|---|
| `emit_iff`, `process_ready`, `register_ready` | Early processing emits nothing; processing after both sources close emits `[3,4,3]`. Registration after readiness enables the same answer. A query equal to frontier 3 stays unknown. Known-empty output emits `some (1, [])`. |
| `no_lost_work`, `pending_or_emitted`, `enabled_persists_or_emitted` | Source updates surround registration and processing; a duplicate registration for time 3 cannot replace time 2. The later-state invariant includes an actual emission transition or an earlier event, not just an available observation. |
| `next_done`, `emit_done`, `done_persists`, `at_most_once` | Repeated processing, a rejected late packet, and registration after completion cannot cause a second emission. The theorem excludes all later response values, including empty lists. |
| `pending_registered` | Every emitted answer in the early schedule has a strictly earlier matching registration. Processing an absent cell emits nothing. |
| `response_sound`, `responseFor_iff`, `responseSquare` | The completion case quantifies over arbitrary compatible futures. The mapped consumer composes the new square with `mapObservation`, retaining the trace honesty obligations and exact list semantics. |
| `registration_order_agrees` | Early delivery at step 5 and late registration followed by delivery at step 3 agree. The theorem compares successful emissions, without promising that unfair executions emit. |
| `eventual_response`, `ProcessingFair` | `available_fair` and `processing_fair` establish the scheduling premises; one closing packet per source supplies progress. The request is proved pending at step 3, rather than assumed to have delivered. |

The stalled-source case retains fair source consumption and consumer processing,
but every prefix has frontier 2; the closing-prefix premise is false and no
response is emitted. The starved-consumer case retains available closing prefixes
and fair source consumption, but has no processing actions after registration.
Its consumer fairness predicate is false and it emits nothing at every step.
The imported trace cases also establish the independent need for source fairness:
available closing packets cannot help a schedule that never consumes them.

Statement review checked the quantifier scopes, strict frontier inequalities,
exact list equality, and the separation of safety, readiness, and progress.
The successful schedule witnesses simultaneous satisfiability of all progress
premises. The stalled and starved schedules prevent interpreting any individual
premise as sufficient. The pending-work and at-most-once results apply to all
action sequences, including malformed or dishonest source packets; source
acceptance and semantic honesty keep their existing separate contracts.

## Reuse and architectural limits

The implementation reuses the source trace, completion preservation, observation
persistence, and interleaving proofs. `responseSquare` composes existing trace
and merge squares, and the checked mapped consumer composes it again. The new
request invariants have one concrete automaton caller. They do not yet justify
extracting a general scheduling or transition framework.

The Felix comparison remains at revision
`6f36d28097db7ea5f5df3263db3e8be08f74e490` from [SOURCES.md](../SOURCES.md).
The inspected [CategoryH interface and composition proofs](https://github.com/conal/felix/blob/6f36d28097db7ea5f5df3263db3e8be08f74e490/src/Felix/Homomorphism.agda)
separate operations from congruence, identity, and composition preservation.
The existing relational squares provide that preservation discipline for this
consumer. The upstream commented product construction contains holes; it does
not establish a demand scheduler capability. No missing Felix construction with
concrete callers emerged here, so this experiment creates no new #8 follow-up.
Full Felix parity remains tracked separately by #8 and #25.

Request replacement, cancellation, multiple requests or consumers, graph
scheduling, phase evaluation, dynamic switching and residual state, analytic
primitives, feedback, partial spines, nested-event bind, cancellation ownership,
reclamation, and cost/history bounds remain outside this slice.

## Validation

Both new modules are reachable from `SquareApplications.lean` and subject to the
normal exhaustive proof audit. Commands:

```sh
direnv exec . lake build Examples.FRPDemand
direnv exec . ./check.sh
```

Exact validation and immutable-candidate review results accompany the task
handoff. Proof infrastructure is unchanged, so audit regression tests are not
required for this change.
