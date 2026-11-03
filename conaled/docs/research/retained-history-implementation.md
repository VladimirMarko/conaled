# Finite retained histories and reusable durable banks

Implementation of [#251](https://github.com/VladimirMarko/conaled/issues/251),
following the [accepted contract](history-retention-contracts.md). The new
`Durability.Retention` namespace leaves the unrestricted durability APIs intact.

The service retains the newest `W` Boolean payloads and a parity bit for the
removed prefix. Its position never decreases and cannot exceed `K`. It admits
ordered reads and retry discrimination only inside the disclosed retained
interval. An expired retry cannot be mistaken for a fresh request. The full
history exists only in the specification and simulation relation.

## Code and preservation route

| Module | Role |
|---|---|
| [Retention](../../Applications/Durability/Retention.lean) | Independent full-history reads/retry classification, bounded snapshots, append update, representation and observation proofs. |
| [RetentionBanks](../../Applications/Durability/RetentionBanks.lean) | Typed cells, buffered writes, ordered persistence, atomic selector replacement, every copy cut, fixed bank addresses. |
| [RetentionService](../../Applications/Durability/RetentionService.lean) | Lifecycle kernel parameterized by storage operations, independent ghost and stored instances, command and finite-trace simulation. |
| [RetentionMachine](../../Applications/Durability/RetentionMachine.lean) | Expanded primitive machine, crashes during copying, labeled step/execution refinement, finite publication schedule, `Interaction.Refines` instance. |
| [RetentionResources](../../Applications/Durability/RetentionResources.lean) | Preservation of slot and metadata bounds through actual machine steps and every reachable finite execution. |
| [RetentionOwnership](../../Applications/Durability/RetentionOwnership.lean) | Affine driver admission, release consumption, connection fencing, actual owned-release transition, pin/mutation exclusion. |
| [RetentionClients](../../Applications/Durability/RetentionClients.lean) | Retry and acknowledgment clients, cumulative effects, scanning/parity and delayed views, reachable reader/cursor exclusion for bank reuse. |
| [RetentionSummary](../../Applications/Durability/RetentionSummary.lean) | Scalar summary state, two summary descriptors and selector, publication cuts, restricted `W=1` trace comparison. |
| [RetainedHistory examples](../../Examples/RetainedHistory.lean) | Connected positive and negative cases, including the existing cumulative graph-admission implementation. |

`Represents` says that the ghost history splits into a removed prefix and the
stored suffix, that the position is its length, that the suffix length is
`min W position`, and that the stored prefix bit is the prefix's parity.
`append_represents` proves preservation by splitting the old suffix plus the
new payload into a trimmed prefix and retained suffix. It does not assume the
new observation equation. `read_refines` and `classify_refines` compare stored
operations with definitions that read the full ghost list directly.

The lifecycle kernel shares control rules between representations. It does not
share the implementation of history reads, retry lookup, or append. `Simulates`
requires equality of those observations and preservation by one append;
`command_refines` and `execute_refines` derive lifecycle and trace preservation.
The bank instance discharges append preservation using the concrete
`replacement_root` theorem. The summary instances use a scalar cumulative XOR
and optional last payload, with a proved decoder update law.

## Publication, recovery and reuse

A replacement writes and persists each new retained record in the inactive
bank, writes and persists its descriptor, then switches the selector. The
publication boundary installs the position, boundary derived from position and
suffix length, retry payloads and prefix parity together. The descriptor is
never published before its contents are persisted. `replacement_allowed`
checks every operation's local buffer/persistence obligation;
`cut_successor` identifies each cut successor with one such primitive.

`Machine` has idle and copying modes. A copying state contains the current
cells, one target suffix, one write buffer, the control state and a finite phase
with record index. The original disk and the cut number appearing in transition
rules are proof witnesses. Neither is a machine field. In particular, the model
does not retain a hidden old disk, full history, instruction list or set of used
addresses in runtime storage. `copyingAt` presents the computed states of a
transaction for the transition relation. `cut_successor` connects that
presentation to local execution rather than postulating a completed replacement.

`machine_step_refines` covers invocation and ordinary commands, begin, each
write/persist operation, selector publication, copying crashes, idle crashes,
and recovery steps. Before publication the ghost history stays unchanged;
publication appends exactly one payload. Crash cancels volatile pending work,
pins, outputs and partial or completed delayed views. Recovery advances a
bounded selected-bank read cursor and only enables service after that traversal.
A second crash discards that cursor and starts recovery again from the durable
selector. Recovery reads typed stable cells; it does not allocate a full-history
reconstruction list or a second copy of the pinned snapshot.

`machine_execution_refines` composes all primitive steps, including repeated
copy and recovery interruptions. `crash_cut_refines` separately exposes the
old-or-new result at every cut. `newest_retained_ack`, `publication_ack` and
`duplicate_publish_busy` connect durable publication, the newest retained retry
payload and acknowledgment. `committed_effect_survives` concerns the ghost
committed effect. It does not extend the lifetime of admitted payload retrieval.

A pin freezes the selected snapshot. Synchronous range construction is one
atomic service action; streaming reads hold the pin and emit at most one record
before output consumption. A diagnostic scan uses an index and XOR accumulator.
The reachable `ScanValid` invariant connects each scan or streaming step to the
frozen suffix. `rebuild_publishes_snapshot` proves that completion publishes one
position/parity tuple for that snapshot. Later commits preserve its historical
meaning, as shown by `delayed_snapshot_survives`; they do not update its position.
The delayed view remains queryable during a copy. A minimum above its position
returns `NotReady`.

The copying mode has no admitted reader or recovery cursor.
`reachable_reuse_safe` derives this from reachable pin/mutation exclusion and
online status. The plan reads its owned target suffix, so it has no borrowed
source-bank pointer. Only the writer's destination address names the inactive
bank. `putInactive_root` proves that its writes leave the selected root intact.
After a crash no copying mode survives, so a pre-crash plan cannot resume.
This model permits reuse of the same two addresses throughout the finite
incarnation and has no monotone allocation-address history.

## Ownership and target assumptions

The physical target supplies stable typed cells, ordered persistence completion,
an atomic durable selector, one writer, and no corruption or rollback. These
are capabilities of this target, not consequences of Lean execution. Direct
Boolean cells and bounded descriptors need no universal serialization interface.
A byte encoding or physical store would have to implement these capabilities.

The driver supplies affine scoped pin ownership and fences old connections on
restart. `Ownership`, capability names and the consumed-name set are proof-side
resources. They are absent from `Machine` and are not an implementation using an
unbounded generation counter. `AdmittedHandle` allows an old connection to call
and receive `InvalidHandle`; a current connection must own the unique
unconsumed scope. `owned_release` connects this premise to the service transition
and consumes the capability. Reacquisition at an unchanged position does not
readmit the old scope.

The raw service receives a current-connection flag from that driver. It cannot
recognize an alias replay within the same connection. The checked
`raw_release_clears_new_pin` counterexample demonstrates why the affine premise
is needed. A replayable network token API would need another freshness protocol;
this implementation does not claim to provide one.

Progress requires released pins, consumption of outstanding output, scheduling
of the finite copy/recovery steps, and a sufficiently long interval without
crashes. `scheduled_publication` proves an available finite schedule from an
admitted pending request. It does not assert fairness, progress under endless
crashes, automatic incarnation rollover, or acceptance after exhaustion.

## Resource interpretation

`reachable_bounds` applies to every finite expanded-machine execution. Both
banks together contain at most `2W` live record cells, including interrupted
copies. The reserved layout is exactly two banks of `W` slots, two descriptors
and a selector. The mathematical list in each bank describes its live ordered
slots; it is not a claim about the allocation of a Lean `List`.

This realization reads stable selected cells directly. It reserves no separate
volatile full cache. Its target suffix uses at most `W` slots, write buffer at
most `W`, outstanding output at most `W`, and pending payload at most one. Thus
it meets the `3W+1` volatile record bound without an extra snapshot copy. Empty
responses require no retained record storage. The single sequential driver is
responsible for bounded transport queues and caller-retained copies.

`reachable_resources` also preserves `MetaBound`; scan and recovery counters
are at most `W`, descriptor and delayed positions at most `K`, and the copy
program counter is a finite phase with index below `W`. With `W ≤ K`, each
changing numeric metadata field encodes in `0..K`. `durableAddress` is
`Bool × Fin W`; `boundedPosition` is `Fin (K+1)`. The fixed incarnation has a
fixed finite encoding. Proof histories, ghost ownership names and execution
indices are outside the runtime layout.

`replacement_work` counts exactly two record operations per retained payload
and three descriptor/selector operations. `publication_work` bounds this by
`2W+3`. Invocation, target preparation, begin and acknowledgment are distinct
service actions. These counts describe the modeled cell operations, not CPU
instructions, allocation, elapsed time or energy. Retry indexing and each
recovery/scan traversal inspect at most `W` retained positions. Repeated crashes
can repeat this work without increasing the reserved storage.

## Statement review and checked cases

Statement review covered every new declaration, including helper lemmas used by
these families. The general theorems quantify arbitrary configurations satisfying
`0 < W ≤ K`, arbitrary related histories/stores, and arbitrary finite executions.
The concrete configuration `E=7, W=2, K=3` establishes nonempty usable instances.
No application axiom or full-history field is introduced.

| Claims reviewed | Intended meaning and discriminating evidence |
|---|---|
| Parity append; representation initial/append/total/suffix/lower/range; read/classifier refinement; reserved freshness | Actual ordered suffix and cumulative observation. `[true,false,true]` has suffix `[false,true]`, lower boundary 1 and total parity false; suffix parity alone is true. Empty expired ranges remain expired; malformed bounds remain invalid. |
| Inactive root/target, primitive root/publication, record-copy equations, allowed operation traces, cut successor and old/new refinement | Real buffered/persisted data precedes selector publication. The universal cut theorem is specialized to the final append, with separate old/new recovery retries and a recovery crash. |
| Operation simulations, command/trace simulation, expanded machine/refinement, execution composition and available schedule | Reuse crosses independent ghost, snapshot, window-bank, scalar-summary and summary-disk operations. Both W=1 summary realizations share the restricted trace contract. Arbitrary full-window observations are not inferred from parity. |
| Fits/operation bounds, prefix/cut preservation, output and metadata preservation, reachable resource bounds | Counts follow reachable intermediate states, including partial writes and recovery. Streaming a second record without consuming the first returns Busy. Neither old transaction witnesses nor ownership histories are counted as runtime data because the runtime has no such fields. |
| Driver admission/release/restart, exclusion, reachable copy readiness and reuse | Second pin and mutation while pinned reject. Release/reacquire at the same position succeeds for a fresh scoped owner. The old scope is excluded by admission, while a raw replay would wrongly release the new pin. Restart-stale release returns InvalidHandle. |
| Ghost history prefix and survival, retained retry safety, expiry, newest acknowledgment and duplicate publication | Retained matching retry acknowledges, conflicting retry rejects, both old payload alternatives expire, out-of-order and out-of-domain IDs reject, exhaustion does not wrap, and a retained retry still succeeds at K. |
| Scan step/completion, scan invariant preservation/reachability, delayed publication/minimum/historical meaning | A view at position 1 remains tagged 1 after position 2 commits. A minimum of 2 returns NotReady. Crash discards a partial scan. Streaming preserves order and duplicate payloads. |
| Summary decoder/update/total, scalar and disk simulation and publication cuts | Same summary-only state can correspond to different W>1 retained retry answers. `[true,false]` and `[false,true]` also expose the loss of ordered information from parity. |
| Existing graph admission specialization | Forgetting edge `0→1` would admit `1→0` in the empty window, while cumulative admission rejects. The unrestricted graph API is unchanged. |

Two proof-development corrections were semantic checks rather than relaxed
expectations. Resource preservation cannot reconstruct the bounds of an
already-overwritten original inactive bank from a later cut; it instead follows
the actual next primitive. Copying also cannot indiscriminately answer every
request with Busy: fenced stale handles and completed delayed views retain their
specified responses. Both distinctions are represented in the expanded machine.

## Applicability and remaining boundaries

For [#235](https://github.com/VladimirMarko/conaled/issues/235), exact labeled
execution simulation and the existing `Interaction.Refines` interface suffice.
Client predicates transfer only when they factor through admitted observations.
`machine_behaviors_refine` supplies that relation; full-history membership is
not silently transported to expired reads. Ownership admission and physical
persistence capabilities remain separate premises.

The storage-operation record is local to this service. Its repeated adapters
are projection/equality obligations for position, count, prefix bit, indexed
payloads, summary, reads, retries and append. The lifecycle proof is shared.
There is no evidence yet that a universal new interface would repay retrofitting
existing unrestricted history, graph or diagnostic contracts. The scalar W=1
specialization preserves the same vocabulary and recovers a smaller public
command surface.

The mathematical friction was the observation restriction and ownership
boundary. Lean friction involved record-update layout, reserved identifiers and
simplification of quantified Boolean cases. Explicit local lemmas resolved those
issues without changing the contract. One author's experience does not establish
an abstraction's limit or a language impossibility. Reconsider this local
operation interface when another retention/ownership consumer supplies evidence
of repeated work; retain the checked specializations during any refactoring.

[#237](https://github.com/VladimirMarko/conaled/issues/237) still owns the FRP
adapter, timestamp boundaries, pending-request preservation and density/burst
assumptions. No timestamp adapter, production store, arbitrary concurrent reader
protocol, indefinite identifier reuse, physical performance result or byte
serialization layer is supplied here.
