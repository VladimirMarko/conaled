# FRP query admission and retained source history

Implementation of [#237](https://github.com/VladimirMarko/conaled/issues/237).
The optional retained lifecycle adds a lower query boundary to the existing
identified request protocol. The default complete-history engine and its
clients keep their existing APIs.

The implementation is split into [source cropping](../../Applications/FRP/RetainedSource.lean),
[admission and simulation](../../Applications/FRP/RetainedLifecycle.lean),
[continued consumers](../../Applications/FRP/RetainedPipeline.lean), and
[resource accounting](../../Applications/FRP/RetainedResource.lean).
[RetainedRequests](../../Examples/RetainedRequests.lean) supplies the checked clients.

## Admission and observations

`Retention.State` contains a lower boundary and the native lifecycle state.
`advanceLower q` succeeds only if the boundary does not decrease and the
pending timestamp, if any, remains at or above q. Failure leaves the state
unchanged. A successful advance filters both source logs, retaining entries
whose timestamps equal q. A native begin below the boundary emits
`outsideRetention`, without reserving its identifier or emitting a batch.
This test precedes the native busy/stale classification. Expired work never
becomes an empty answer.

The caller promises to relinquish future queries below each accepted boundary.
A source frontier certifies completeness; it is not that promise. The wrapper
has no clock policy, lease negotiation, archive fallback or external handle
registry. An owner with outstanding handles must keep the boundary below their
promised query range, in addition to the wrapper's checked pending-request guard.
The experiment chooses an explicit command, not an automatic age-based policy.

Cropping preserves exact batch lists for admitted timestamps, including their
order and multiplicity. Completeness is restricted to `q ≤ t < frontier`.
Packet acceptance still uses the native source interval validation. Accepted
incoming packets are also cropped, which matters when q is ahead of the source
frontier. Rejected packets do not create retained values.

The full-history lifecycle exists only in `Related` and refinement statements.
The runtime stores no reference execution or command trace. `projected` maps
retention commands and expired attempts to native idle commands. Admitted native
commands retain their original positions. Step and finite-run comparison derive
native status/response equality from cropping and pending admission; callers do
not supply an output-agreement premise. The reference remains unrestricted,
while the theorem compares only this projected admitted workload.

## Continued consumers and recovery

`Retention.Pipeline` uses the existing lifecycle optional-response adapter.
A real empty response runs the consumer; silence and retention notices do not.
The compiled count/total example queries the retained timestamp twice and expects
`[3,4,3]` both times, with consumer states `(1,10)` and `(2,20)`. It also checks
strictly older entry removal, expired rejection, pending-conflict refusal,
accepted packet filtering and invalid packet rejection.

Native identifiers keep their existing local high-water semantics. A repeated
query uses a fresh identifier; an old identifier is not a transport retry token.
An expired retry is rejected even if an earlier execution answered it. There is
no replay cache, network acknowledgement or exactly-once storage guarantee.

Finite `run_append` preserves the lower boundary, retained native state and
consumer at a continuation boundary. Durable restart must persist those values
together with any external ownership commitments. Restoring a smaller boundary
against already cropped logs would promise answers that no longer exist.
Restoring an old complete snapshot must also reconcile externally visible
responses and handles. No crash-atomic storage or recovery mechanism is selected
here. The separate retained-history service from #251 has its own snapshot and
storage contract; it is not silently installed as this adapter's backend.

## Resource model

The generic semantic adapter accepts any linearly ordered timestamp type.
The bounded retained-list result specializes to natural timestamps and counts
fragments, including empty fragments. For a retained list within `[q,q+W)`,
with at most D fragments per timestamp, its length is at most `W*D`. A finite
window alone supplies no density bound: arbitrarily many empty fragments may
share one timestamp. Rational timestamps would need a separate packing or
arrival bound; the natural-timestamp theorem does not cover a dense order.

Encoded accounting charges each fragment a header, a timestamp cost, and a
payload cell plus payload encoding cost per element. If timestamp cost is at
most BT, each fragment has at most P payloads and each payload cost is at most
BA, the list costs at most

```text
W * D * (header + BT + P * (cell + BA)).
```

These are explicit workload and representation hypotheses. A fixed timestamp
span does not bound the encoding of an unbounded absolute natural timestamp.
The caller must bound timestamp encoding or choose and validate another encoding.
Likewise, a payload count does not bound arbitrarily large payload integers.
The sum is an abstract serialized/list cost, not measured Lean heap bytes.
The concrete cost example charges two units for its fixed timestamp 2, unary
payload length n for value n, and one unit each for headers and payload cells.
It proves a 32-unit bound for the two retained fragments. This does not implement
a wire serializer or justify a constant cost for arbitrary natural timestamps.

For each source, density and span must be maintained by the admitted workload.
Native valid packets occupy disjoint timestamp intervals, but validity does not
bound fragments within an interval. An external delivery policy needs a packet
burst bound and payload/encoding bounds before buffering or accepting untrusted
packets. This wrapper does not reject otherwise valid packets merely because
an unspecified resource policy would reject them. A lagging pending request can
prevent boundary advance, so a fixed retained span also requires an explicit
workload/progress constraint; no finite-span invariant is inferred from fairness.

The runtime inventory extends beyond retained logs. A pending timestamp, current
boundary, frontiers and the native identifier high-water mark need encodings.
Consumers may accumulate unbounded values even on empty responses. Delivery
queues, response queues and retry metadata need independent bounds. Packet
validation, list append and filtering can retain both old and new values during
an update; packet size and transient allocation need accounting. Caller-held
snapshots may keep erased lists reachable. `run` materializes output lists for
finite specifications; a streaming caller must control its own output retention.
No theorem here bounds total reachable heap, garbage-collector behavior,
transient peak memory or all backend allocation.

## Integration boundary

The adapter supplies explicit admission, source reclamation and a restricted
complete-history comparison for one identified native consumer. It does not
require the exclusive-current-request adapter or change its semantics.
[#235](https://github.com/VladimirMarko/conaled/issues/235) retains any future
shared-interface decision. #234 owns broader resource obligations; #194/#225
own external delivery and recovery integration. Choosing a production store,
clock, retry protocol or universal retention interface needs its own concrete
consumer requirements. Generalization alone does not require another ticket.
