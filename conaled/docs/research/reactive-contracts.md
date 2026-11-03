# One-shot reactive contracts

Issue [#220](https://github.com/VladimirMarko/conaled/issues/220) connects the
existing Demand broker to initialized feedback on completed batches. The result
is finite-prefix refinement, with a separate conditional eventual-update theorem.
It implements the contract experiment in
[the recursion and FRP priorities](recursion-and-reactive-priorities.md).

## The selected consumer

[ReactiveContracts](../../Applications/FRP/ReactiveContracts.lean) defines a
history consumer initialized by `(ticks, history)`. A completed batch updates it
to `(ticks + 1, history ++ batch)` and emits that new state. It uses the existing
[feedback adapter](../../Applications/FRP/Feedback.lean), which consumes each
actual `frame.emitted` once. An absent emission leaves the state unchanged;
`some []` advances one tick. Persistent observed knowledge does not cause another
update.

For initial state `s` and truthful batch `b`, the independent specification permits
exactly these two finite-prefix results:

```text
([], s)
([updated s b], updated s b)
```

`AllowedInput b` requires the completed input sequence to be either empty or
`[b]`; optional stuttering positions remain unconstrained. `consume_zero` and
`consume_one` identify the corresponding result exactly. In particular, a
consumer that always stutters cannot satisfy the completed-input theorem.

The broker remains one-shot. This construction is a registration handshake
followed by at most one update, not a mutually recursive live network or a
repeated-query engine. No dependency on the unfinished #31 engine is introduced.

## Compatibility and refinement

Compatibility has two independently proved directions:

1. `register t tail` prepends registration to the supplied action schedule.
   `bootstrap` proves that the request is pending at processing index one,
   without any assumption that a source advances or a response occurs. This
   discharges the broker's registration requirement.
2. `broker_allowed` proves that the actual broker emissions satisfy
   `AllowedInput`. Registration fixes the response timestamp despite later
   duplicate registrations. Source honesty and the existing `responseSquare`
   identify the ordered payload with `truth left t ++ truth right t`.
   `at_most_once` excludes additional completed batches. This discharges the
   history consumer's input requirement.

The relation `broker` is the graph of actual finite `feedbackInputs`; `consumer`
is the graph of actual `consume`. Neither graph embeds the desired result as a
premise. With streams, actions, query and truth fixed, the admissible source-world
set ranges over initial states satisfying `(traceRep streams).Rel initial truth`.
The API also accepts any action stream whose first action is the registration,
so existing execution fixtures can be used directly.

`broker_compatibility` and `consumer_compatibility` establish the two concrete
image inclusions. `connected_requirement` uses the existing
[image/requirement adjunction and composition](../../SquareKit/RelationTransport.lean)
to derive the composed requirement. `handshake` combines the registration
constructor with that theorem. `connected_image` gives the forward inclusion.
`connected_refines` packages it using
[Interaction.Refines](../../SquareKit/InteractionContracts.lean), with the
permitted specification first and actual results second. `connected_history`
then transfers the property that final history is either the initialization or
its ordered append by the truthful batch. Duplicates are preserved.

These proofs add concrete broker and consumer obligations to existing relation
transport. They do not introduce a general contract calculus. A client authors
its initialization, query and action schedule, and establishes source honesty.
The registering constructor supplies the internal registration obligation; the
broker proof supplies the internal observation obligation.

## Safety, observation and environmental progress

Finite-prefix safety holds without eventual delivery. Explicit finite bounds
make `feedbackInputs` and consumption executable. A checked example reuses the
existing feedback causality theorem on batch ticks. It does not identify those
ticks with processing positions or event timestamps.

`eventual_update` separately assumes the existing Demand environment contract:

- a `Delivery` for the actual source schedule and its `Fair` proof;
- `ProcessingFair` for enabled requests;
- available finite source prefixes whose frontiers advance beyond the query;
- source honesty, independently of scheduling and protocol validity.

Registration supplies the pending request at index one. The theorem invokes
`Demand.eventual_response`, then `delivered_result` selects the updated branch
at the finite prefix ending just after the actual emission. This proves one
eventual update. It gives no global deadline, infinite productivity, repeated
response guarantee or executable horizon extracted from an erased existential
proof.

## Checked cases and incompatibilities

[Examples.ReactiveContracts](../../Examples/ReactiveContracts.lean) initializes
the consumer at `(2, [8])` and reuses the actual frontier/Demand fixtures.

| Observations | Result |
| --- | --- |
| Delayed query before its response | `([], (2, [8]))` |
| Completed batch `[3,4,3]` | `([(3,[8,3,4,3])], (3,[8,3,4,3]))` |
| Completed empty batch | `([(3,[8])], (3,[8]))` |
| Rejected late packet after delivery | Same result as before that packet |

The delayed response has event timestamp two and processing index five; it
advances the initialized consumer from two ticks to three. These numbers denote
different quantities. The examples use the general delivery theorem for both
nonempty and empty results, the composed image and requirement theorems for
arbitrary bounds, and the refinement property transfer for final history.
Existing chunk and tick-count laws are instantiated for this consumer.

A concrete availability schedule, its fairness proof, processing fairness and
closing-prefix witnesses instantiate `eventual_update`. Counterexamples keep
its environmental hypotheses visible: stalled sources fail advancement despite
processing fairness; the existing starved scheduler never processes a ready
request. Their actual consumed prefixes produce no updates. An all-`none` input
also satisfies per-delivery safety vacuously while leaving the state unchanged.

An idle consumer that omits registration cannot provide a pending request at
index one. In the other direction, a consumer demanding nonempty batches rejects
an honest known-empty response: the broker image is proved not to be included in
that stronger input requirement. A forged `[9]` also fails the truthful-batch
requirement and actually produces the wrong history when consumed.

Partial knowledge, conditional safety, executable observation, batch causality
and eventual delivery therefore remain separate contracts. Environmental games,
controller synthesis, repeated requests and resource instrumentation remain
outside this result under [#196](https://github.com/VladimirMarko/conaled/issues/196),
[#31](https://github.com/VladimirMarko/conaled/issues/31) and
[#193](https://github.com/VladimirMarko/conaled/issues/193).
