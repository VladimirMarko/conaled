# FRP preservation laws, long-running state and external execution

The discrete FRP kernel has executable IO drivers, compiled initialized
consumers, an identifier-free request adapter and source-history reclamation.
The finite Boolean circuit service also has a uniform abstract resource bound
and conditional productivity theorem. These are distinct implementations with
different contracts; none establishes the whole runtime proposed in
[#27](https://github.com/VladimirMarko/conaled/issues/27).

## Implemented execution and its limits

The [engine](frp-engine.md), [reactive target](reactive-target.md),
[pipeline](reactive-pipeline.md) and [lifecycle](request-lifecycle.md) compose
into an executable discrete kernel. Two sources supply complete windows;
requests wait until both frontiers establish completeness at the requested
timestamp. Compiled initialized consumers retain state between sequential
requests. The original ordered response and its aggregate observation remain
separate. Empty delivery advances the consumer; absent delivery does not.

| Delivered capability | Contract and limits |
|---|---|
| [Bounded stdin/stdout driver](frp-driver.md), #233 | Runs the lifecycle and compiled aggregate consumer, bounds input and session size, supports deterministic fresh-process replay, and stops after ambiguous output failure. It retains source history and does not supply crash recovery. |
| [Finite-circuit service](indefinite-reactive-service.md), #234 | Initialized Boolean circuits with sequential/parallel composition and delayed feedback. The byte-stream runner retains no IDs or history. Uniform space/work and conditional progress are proved for the circuit machine; Lean allocation, reclamation and IO remain trusted. |
| [Between-tick backend migration](between-ticks-migration.md), #464 first delivery | Transfers the live delay/complement-pair continuation in both directions after retiring one accepted tick and its local publication. Explicit preparation and ownership commit preserve old authority on refusal/cancellation. Pending-work migration remains open under #480. |
| [Exclusive-request adapter](exclusive-request-adapter.md), #236 | Serial requests without runtime request identifiers, with a constructed identified-reference comparison and conditional delivery. Its admission/communication contract excludes stale commands; it does not reject arbitrary delayed callbacks. |
| [Query-retention implementation](frp-query-retention.md), #237 | Reclaims source history under an explicit future-query contract. Its resource guarantees apply to the admitted workload and representation, not to the unrestricted lifecycle. |

The [denotational integration](../frp-integration.md) includes switching.
Executable dynamic switching and phase evaluation remain outside these runners.
The implemented progress results retain explicit source, scheduling and sink
assumptions. Internal emission does not establish external acknowledgment or
crash-recoverable exactly-once delivery.

## Identifiers and retained state

[Lifecycle.State](../../Applications/FRP/Lifecycle.lean) stores an optional last
accepted `Nat` ID, alongside the engine. It stores no completed-ID set. IDs are
supplied by callers and must increase for successive accepted requests. A fixed
number of fields does not bound their representation: growing IDs, natural-number
consumer totals and retained histories can all grow.

The [request-identity assessment](frp-request-identity.md), #232, compares
identifier elimination, bounded identities with exhaustion, and reuse under
explicit stale-message exclusion. The delivered driver uses bounded increasing
IDs without wrap or reuse. The exclusive adapter instead relies on one current
request and its communication contract. Source frontiers do not by themselves
prove retirement of old control messages, and a repeated query timestamp does
not identify a request occurrence.

The query-retention implementation restricts future admissible queries before
forgetting source data. The finite-circuit service avoids that history entirely.
Neither makes the unrestricted lifecycle bounded. Drivers must consume results
incrementally if they are to avoid retaining a lifetime transcript; the finite
`run` specifications themselves return lists.

## Compilation and reusable preservation

[ReactiveCompiler](../../SquareKit/ReactiveCompiler.lean), delivered in
[#228](https://github.com/VladimirMarko/conaled/issues/228), compiles first-order
seeds and transition bodies into stored target morphisms. An additional target
supplies cartesian operations, primitive interpretations and local soundness
laws. The compiler's existing theorem then supplies initialization and step
correctness; authors do not repeat the compiler induction. Executing a target
requires its own implementation in addition to a denotation.

The [reactive target](reactive-target.md) uses executable function targets.
The [finite-circuit service](indefinite-reactive-service.md) also accepts the
reactive compiler's Boolean circuit target. This is a concrete alternative
representation with execution and resource analysis, not a native-code emitter
or a general asynchronous graph compiler.

The completed [preservation experiment](compositional-guarantees-and-boundedness.md),
[#231](https://github.com/VladimirMarko/conaled/issues/231), exercises compiled
delay, representation change, resource transport and a non-FRP consumer.
[Feedback.transport](../../Applications/Progress/Feedback.lean),
[Reactive.run_related](../../Applications/Progress/Reactive.lean) and
[RelationTransport](../../SquareKit/RelationTransport.lean) remain reusable.
[#235](https://github.com/VladimirMarko/conaled/issues/235) owns continuing
compatibility and author usability; completed #231 is not a current blocker.

Preservation must retain the observations the caller needs. Batch summation
forgets order and occurrence identity. Deleting silent processing positions can
change temporal next and bounded horizons, as the
[multimodal assessment](multimodal-reactive-assessment.md) explains. An empty
observation fiber proves no reachable execution. Compilation and relation
composition alone provide neither fairness nor bounded memory nor durability.
Initialized execution is also a consumer for
[#109](https://github.com/VladimirMarko/conaled/issues/109), without equating
finite folds, initialized feedback and unrestricted fixed points.

## Remaining runtime scope and related work

[#27](https://github.com/VladimirMarko/conaled/issues/27) owns proposals for
executable phases, dynamic switching with residual state, a demand-driven graph
scheduler, cancellation/reclamation, partial-information semantics and continuous
time. These require selected contracts and bounded implementation specifications.
In particular, integration needs analytic or approximation assumptions; dense-time
strict causality alone does not justify productive feedback. The completed
#232–#234 sequence is evidence for that work, not unfinished prerequisite work.

[#225](https://github.com/VladimirMarko/conaled/issues/225) owns durability,
with the completed assessment #226 and recovery implementations #240/#241
providing related evidence. [#194](https://github.com/VladimirMarko/conaled/issues/194)
and [#196](https://github.com/VladimirMarko/conaled/issues/196) cover external
interaction and failures. None is a delivered crash-recoverable FRP driver.
A future adapter must connect input admission, state commit, output publication,
acknowledgment and retries under its actual storage and peer contracts.

[Policy-directed realization choice](policy-directed-choice.md), #436, can
support a future FRP client selecting admissible compiled implementations before
initialization. Admission and correctness remain independent of ranking;
measurements must include selection and representation costs. That FRP connection
is not implemented. Mid-execution replacement additionally needs a constructed
state transfer, preserved pending observations and resource/progress obligations.
The existing transport theorems can justify a suitable relation; they do not
construct a migration algorithm from equivalence alone.

Issues own acceptance criteria. This overview records delivered capabilities and
remaining ownership; it does not authorize every proposed runtime extension.
