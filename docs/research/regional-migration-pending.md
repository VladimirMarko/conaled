# Pending shared-dependency repartitioning

The pending stage of #487 uses the accepted #480 protocol with a concrete shared
producer, two consumers and a join. The quiescent richer-input client remains in
[regional-migration-quiescent.md](regional-migration-quiescent.md). This extension
specializes the pending producer to the Boolean left summand of `Rich.code`.
It does not adopt a general graph, closure, certificate frontend or crash protocol.

## Source and execution

For input `x` and old delay state `b`, the independent source emits
`xor b (!x)` and advances to `x`. The actual producer executes `Rich.code` once,
caches its Boolean result, and owns two delivery cells. Consumer D reads the old
delay state and prepares the new state; consumer N negates the same cached value.
The join publishes their XOR through the actual stable #480 peer. The peer stores
the joined payload, including when it differs from the old delay state.

Fused execution uses the compiled joint circuit. Split execution calls the delay,
NOT and XOR circuits. Checked execution additionally runs the redundant
encode/decode boundary. Once either consumer has received the cached result,
execution resumes the retained partial phase even if the new cut is fused.
Conversion copies the cache, old state, completed consumer results, candidate
state, cancellation flag and both delivery references. It never reruns the
producer or an already delivered consumer.

The frozen three-input oracle is `[true,true,false]` → `[false,true,false]`, with
final state `false`. The first effect is published with its acknowledgment lost
while a second input is accepted. Repartitioning preserves that uncertainty;
a later cut occurs after only D receives the second producer result. The final
publication stores `published false false` while the old delay state is still
`true`, separating actual joined publication from output-log relabeling.

## Ownership and source proof

`RegionalPendingSource` defines the independent source transition and the live
invariant. Its local projection to #480 changes payload interpretation using
the retained owner's input. Incoming retry input never chooses this mask.
Conflicting retries remain conflicts. Accepted-phase dummy outputs are irrelevant;
cancelled and published payload constraints remain enforced.

`RegionalPendingInternal` proves producer, delivery, join, fused completion and
admission preservation. A free slot cannot own a queued message, so admission
cannot silently change an existing callback's payload interpretation.
`RegionalPendingProtocol` handles the actual external commands, including delayed
confirmation, publication, cancellation, close and release.

`RegionalPendingRefinement` transports the invariant through the validated whole
continuation, including changed cuts and backend placement. Its `InnerReady`
condition states that the wrapper owns migration: neither the active protocol nor
a prepared target has a nested protocol preparation. Control transitions are
source-silent even when their public status reports failure. `SourceRun` records
actual step outcomes; its balance counts accepted occurrences as either still
pending, effectively published or prevented by cancellation.

Source advancement occurs at effective peer publication. Local confirmation and
state commit can lag behind it. This distinction is essential to the lost-ack
fixture. The source relation preserves order and the XOR value; a count equation
alone would not establish those properties.

A slot cannot be released while either internal delivery references it. The
accepted protocol additionally requires terminal status, closed route and no
external queue reference. Cancellation may leave callbacks to drain, but those
callbacks cannot publish an effect or reach a reused owner. `producer_once`,
`empty_delivery_stutters` and `producer_transfer` distinguish retained results
from replay. The complete wire checkpoint also retains the peer and external
queue across migration.

## Admission, certificates and progress

Preparation retains the old authority, constructs and validates the complete new
continuation, and freezes business commands until commit or cancellation. A
prepared target carries replacement semantic and resource evidence indexed by its
actual cut, backend and requirements. Ownership commit installs that target.
Whole-wire validation rejects swapped D/N results when unequal values expose the
mistake. Unsupported requirements, stale cuts, insufficient capacity and injected
allocation or validation failure leave the old continuation usable.

The bounded policy reuses #486's charged candidate inspection, context and epoch
validation. It ranks complete pending plans from a six-entry cut/backend catalog,
including modeled protocol, copy, consumer and adapter costs. Ranking only
proposes a target. Actual preparation checks migration capacity and continuation
separately. The service-capacity fixture has a target eligible at 441 cells but
rejects migration from the checked source requiring 445. The quiescent fixture
separately distinguishes old/new overlap from target steady space.

Every permitted preparation attempt consumes one permission, including failure.
Only actual business commit restores it. Commit/cancel of migration and policy
inspection cannot restore it. Thus changes cannot consume unbounded preparation
work between business commits. A scheduler must still stop injecting controls,
finish or cancel preparation, and schedule enabled work; arbitrary infinite
control spam is not productive.

For reachable states, two internal delivery opportunities clear both internal
references. With fresh retries/queries stopped, eight external dispatch
opportunities drain the four event cells. `ten_opportunities_retire_references`
connects these to actual public commands. Releasing the request still requires
its terminal and closed-route checks. Publication liveness assumes the peer
accepts the effect and a reply is eventually delivered; it is not derived from
per-plan productivity alone.

## Resources and runtime boundary

Logical storage accounts for both request slots, four external event cells, two
internal delivery cells, retained partial computations, old/new overlap and
conversion scratch. Fused/split residual stores use 22 modeled cells; checked
stores use 24. Conversion reserves 23 cells for the complete decoded continuation.
`prepare_execution` identifies the actual copied target and event trace;
`prepare_lifetime` connects that transition to the lifetime bound checked during
admission. Validation failure releases candidate and scratch. Commit releases the
old representation, while cancellation releases the prepared representation.

The producer has an actual `Rich.Executes` and `Rich.Allocates` witness. Consumer
bills use the selected circuit work; protocol bills reuse #480 command work.
Every wrapper command includes a response/dispatch unit, and copy events are
charged. `NativeServiceRuns` relates each selected native call to its actual
code, arguments, result and allocation derivation. `ServiceExecution` connects
that call to the public wrapper branch and its stored result. Its trace retains
the old encoded store, a 22-cell decoded store, a 22-cell updated store and the
new encoded store, along with every evaluator allocation prefix. Split whole
execution retains all three consumer arenas until return. Protocol calls include
the inherited queue-copy peak; wrapper checkpoints also include any paused
prepared target and the final state.

`service_execution_bound` bounds this complete trace under the reachable
invariant and readiness conditions. `Certificate.service` now contains the
operational service evidence used by `prepare`; `committed_service_execution`
instantiates that evidence on the actual committed replacement and its next
command. `reachable_service_bound` covers every reachable business command,
including frozen and refused branches. The conservative capacities are 441 cells
for fused/split and 445 for checked. This repairs review findings 487-STD-001
and 487-SPEC-1; no prior concrete overrun was alleged. These are logical
copied-value resources,
not Lean heap bytes, CPU instructions or a verified host allocator.

The byte adapter holds one authoritative in-process session and stable peer. It
streams business and control frames and aborts on write/flush failure without
replay. A modeled atomic peer effect does not make a host write atomic or
recoverable. A partial write may be externally visible before an exception.
The `/dev/full` fixture fails on the first control write before business
publication; it does not demonstrate recovery from a partially published effect.

The runtime suite checks lost acknowledgment, pending acceptance, partial shared
delivery, placement and changed cuts, cancellation and reuse, failed preparation,
freeze, unequal swapped wiring, bounded attempts, policy control, and 128
transactions before EOF. An independent Python oracle computes every business
output. Existing #480 and quiescent clients remain separate acceptance checks.

The measurement script records per-command local pipe round trips after process
startup, with three repetitions per schedule. Recorded medians were 218 μs for
placement preparation, 237 μs for checked-cut preparation, 182 μs for the later
fused-cut preparation, and 17 μs for ownership commit. Preparation includes
conversion and validation; this instrumentation cannot isolate either component's
CPU time. Values describe this throttled host/run and establish no amortized or
cross-platform performance benefit. Raw observations are in
`regional-pending-measurements.json`.

## Statement review

- Source refinement must prove the actual joined peer payload and advancement at
  effect publication; a transported delay-output theorem alone is insufficient.
- Arbitrary suffix and repeated migration claims require readiness at business
  boundaries and validated complete continuation. Public control statuses may
  differ from the migration-free run.
- Cached producer and partial-delivery state must survive both placement and
  changed cuts; two independent computations would not test shared dependency.
- No-loss balance counts prevented cancellations separately and retains waiting
  inputs. It does not promise unconditional completion under an unfair scheduler.
- Resource certificates belong to the new actual target and required transition
  capacity. Semantic equivalence does not transfer a stale resource certificate.
- Service storage must cover the actual wrapper execution, not only a proposed
  arithmetic budget. `Realizes` identifies arguments and stored results;
  `NativeServiceRuns` supplies native code execution and allocation evidence.
  `ServiceExecution` also retains prepared-target and final-state checkpoints.
- `ServiceCertified` quantifies over bounded protocol states and every native
  call at the selected cut. Reachable invariants provide that premise; the
  post-commit theorem consumes the replacement's stored certificate. A naked
  capacity inequality would not establish the public execution bound.
- The lifetime model deliberately retains all temporary consumer arenas until
  return and all four residual-store generations together. It is conservative,
  not an assertion that Lean's garbage collector uses that schedule. Examples
  separate this accounting from a maximum single arena, an empty protocol
  queue, and omitted paused-target storage.
- Logical allocation/lifetime evidence and host timing are separate claims.
