# FRP preservation laws, long-running state and external execution

The next priority is to generalize preservation laws demonstrated by the FRP
sequence. [#231](https://github.com/VladimirMarko/conaled/issues/231) owns that
bounded experiment under [#200](https://github.com/VladimirMarko/conaled/issues/200).
It should reuse existing relational interpretation and compositional transport,
with a concrete non-FRP consumer, before adding a public abstraction. The rest
of the correspondence programme remains open.

## Implemented execution and its limits

The [engine](frp-engine.md), [reactive target](reactive-target.md),
[pipeline](reactive-pipeline.md) and [lifecycle](request-lifecycle.md) now compose
into a pure executable discrete kernel. Two sources supply complete windows;
requests wait until both frontiers establish completeness at the requested
timestamp. Compiled initialized consumers retain state between sequential
requests. The original ordered response and its aggregate observation remain
separate. Empty delivery advances the consumer; absent delivery does not.

The implementation has refinement, compilation and lifecycle safety results,
with progress conditional on source advancement and processing. The existing
[denotational integration](../frp-integration.md) also includes switching;
executable dynamic switching is still outside this kernel. There is no external
IO driver, crash-recovery implementation or bounded-memory guarantee.

## Increasing identifiers and retained state

[Lifecycle.State](../../Applications/FRP/Lifecycle.lean) stores an optional last
accepted `Nat` ID, alongside the engine. It stores no completed-ID set. IDs are
supplied by callers and must increase for successive accepted requests; they
can jump by arbitrary amounts. Natural numbers do not wrap at a machine-word
limit, but a growing value requires growing representation. In a conventional
binary encoding, a positive ID M needs `floor(log2 M) + 1` bits. This is a
representation observation, not a measured runtime cost or a checked resource
theorem about Lean's allocator.

Thus a fixed number of state fields does not establish bounded space, even if
all other program state stays bounded. Several independent sources of growth
need separate contracts:

| State or output | Current limitation |
|---|---|
| Last accepted ID and current command IDs | No fixed width, exhaustion policy or reuse protocol. |
| Source knowledge | Retained history; later requests may revisit old timestamps. Frontiers alone do not authorize deleting those batches. |
| Consumer state | Depends on the consumer. The example natural-number count and sum can also grow. |
| Finite runner results | `run` returns a list of events. A driver should consume step results incrementally instead of retaining a lifetime transcript. |

[#232](https://github.com/VladimirMarko/conaled/issues/232) compares unbounded
IDs, bounded IDs with explicit exhaustion, and reuse under a stated session or
stale-message exclusion contract. Reusing an ID can make a delayed old command
look current. An epoch moves the same question to the epoch namespace;
randomization requires a collision model. Restart or rollback can also restore
an old accepted-ID mark. Any reuse design must revisit the current global
per-ID at-most-once statement and identify the scope of identity it preserves.

This assessment coordinates with resource consumer
[#193](https://github.com/VladimirMarko/conaled/issues/193) and durability
[#225](https://github.com/VladimirMarko/conaled/issues/225). Reclamation must
state which future queries remain supported before discarding history. Neither
an indefinite-service policy nor a storage representation has been selected.

## Can request identifiers disappear?

The [request-identity assessment](frp-request-identity.md) makes elimination a
first comparison under #232. Existing synchronous initialized machines require
no request IDs. A repeated-request interface can use one exclusive current
request if its admission and communication contract excludes old commands and
responses. A timing-based alternative needs lifetime or quiescence evidence;
current prefix causality and signal-stability intervals do not supply it.

Reusing source frontiers as control-message retirement evidence would require
a separate proof. Likewise, accepting repeated queries at the same timestamp
prevents timestamps alone from identifying logical requests. Compare occurrence
safety with the current named-request contract, including busy/stale behavior,
replay, delayed processing and restart. Any growing runtime timestamp, epoch or
counter still belongs in the space accounting. The proposed identifier-free
wrapper and its refinement are not yet implemented.

## A nonempty class supporting indefinite service

The stronger objective is a class of programs or program/backend pairs that
can keep operating indefinitely.
[#234](https://github.com/VladimirMarko/conaled/issues/234) owns a checked first
witness and composition laws that can broaden that class. A finite-run driver
or a fixed number of state fields does not establish this property.

The proposed first witness is initialized delay over a finite value type,
such as `Bool`: consume one input, emit one output, and retain one value.
It needs no growing request ID or transcript. Existing initialized-machine
semantics supplies the behavioral starting point; a bounded-memory backend
realization and its indefinite-service theorem remain to be established.

The contract should quantify over every finite execution length: the next
permitted input can be processed while preserving the invariant, a retained
memory bound independent of elapsed steps, and a stated per-step work bound.
Continued input, scheduling and output consumption then support the intended
infinite productive execution. Absent input or a permanently blocked sink
cannot be repaired by a state-space bound.

A program's semantic contract and a backend's resource obligations should be
separate, allowing further backends to reuse the semantic proof. Composition
should cover bounded pure operations, sequential/parallel machines and
initialized delay/feedback where the local conditions suffice. Intermediate
buffers, backpressure, stack, allocation and reclamation need explicit
contracts. Abstract-machine bounds do not alone prove bounds for a compiled
Lean process; runtime assumptions must remain visible. This goal neither
claims fault-free hardware forever nor requires all programs to belong to the
class. The issue requires an implemented witness, a composed example and
counterexamples, including unbounded counters and queues.

## Preservation laws to reuse

The [cross-property assessment](compositional-guarantees-and-boundedness.md)
compares boundedness with optimization, resource accounting, productivity and
durability. Existing relational transport supplies the qualitative core;
quantitative observations and progress require additional laws. The next #231
experiment will test those laws across compiled delay and an interaction consumer
before selecting another shared interface. #234 needs one resource bound uniform over every
admissible execution and prefix for its configured workload, together with
separate progress evidence. Finite memory at each individual prefix is weaker.

| Checked evidence | Follow-up obligation |
|---|---|
| [Feedback.transport](../../Applications/Progress/Feedback.lean) and [Reactive.run_related](../../Applications/Progress/Reactive.lean) lift local transition relations to streams and finite runs. | Compare actual repeated caller obligations before extracting another interface. |
| [ReactiveCompiler](../../SquareKit/ReactiveCompiler.lean) and [LifecyclePipeline](../../Applications/FRP/LifecyclePipeline.lean) connect compiled bodies, state representations and arbitrary finite lifecycle executions. | Retain original observations and explicit state relations through composition. |
| [RelationTransport](../../SquareKit/RelationTransport.lean) supplies forward images and backward universal requirements. | Reuse its composition laws with an existing interaction consumer; coverage and progress remain separate premises. |
| [The multimodal assessment](multimodal-reactive-assessment.md) distinguishes event time, processing positions and completed-batch positions. | Deleting silent positions does not generally preserve temporal next or the same bounded horizon. |

#231 must distinguish equivalence, forward refinement, relational preservation,
and reflection. Batch summation cannot recover order or occurrence identity.
A universal guarantee over an empty observation fiber supplies no reachable
witness. Neither compilation nor relation composition provides fairness,
bounded memory or durability. The experiment should compare client obligations
before and after sharing; a checked negative result is preferable to a public
wrapper that merely renames existing work.

Initialized transition execution already factors recursion out of the compiled
first-order body. This supplies a consumer for
[#109](https://github.com/VladimirMarko/conaled/issues/109), without identifying
finite folds, initialized feedback and unrestricted fixed points.

## Driver ownership and sequence

1. Prioritize #231's shared preservation experiment. #232's identity and
   retention assessment can proceed alongside it. #234 then uses the preservation
   results to establish the first indefinitely operating realization and
   compositional closure, independently of the bounded driver.
2. [#233](https://github.com/VladimirMarko/conaled/issues/233) first settles the
   external boundary and a bounded identity policy, then implements deterministic
   replay and a sequential stdin/stdout driver around the existing lifecycle.
   Reconcile #231's result before finalizing its proof interfaces.
3. Under [#27](https://github.com/VladimirMarko/conaled/issues/27), scope
   executable phase evaluation and dynamic switching with residual state as
   the subsequent major semantic extension.

FRP owns driver acceptance. [#194](https://github.com/VladimirMarko/conaled/issues/194)
provides external-state and failure contracts within
[#196](https://github.com/VladimirMarko/conaled/issues/196).
#225 and [#226](https://github.com/VladimirMarko/conaled/issues/226) own durability
and recovery questions; [#227](https://github.com/VladimirMarko/conaled/issues/227)
informs persistence and diagnostic-view choices if needed. The driver does not
wait for those entire programmes to close or duplicate their research scope.

Its boundary contract must distinguish decoding, structural packet validation,
source honesty, internal emission, output publication and acknowledgment.
A failed or partial write after an internal transition does not establish
that no output escaped. Local at-most-once emission is not externally
acknowledged exactly-once delivery. Silence does not justify advancing a source
frontier. The first driver can exclude crash recovery with an explicit fresh
session/isolation contract; it must not silently reset IDs and claim replay
safety. Persistence, automatic retries and indefinite operation require further
accepted scope. Issues own acceptance criteria; this note records the evidence
and coordination behind them.

The preservation experiment feeds the continuing architecture programme
[#235](https://github.com/VladimirMarko/conaled/issues/235). New causal, timing
or identifier-free consumers should report missing laws and specialization
usability there; completing the first experiment does not close that work.

## Implemented finite-circuit service class

The [indefinite-service implementation](indefinite-reactive-service.md) supplies
initialized Boolean circuits, checked resource/progress contracts, compositional
wiring and a synchronous byte-stream runner. It covers a finite-value delay and
composed clients without IDs or growing histories. Its uniform space theorem is
for an explicit circuit arena model; host allocation, reclamation and IO remain
trusted. The frontier driver and unrestricted lifecycle do not inherit this
bound. #234's implementation record states those distinct contracts and limits.
