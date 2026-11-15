# Pending-request crash recovery: implementation development

This implements the direct composition frozen in
[pending-crash-recovery-protocol.md](pending-crash-recovery-protocol.md) for #540.
It is a development milestone, not a completed acceptance result. The universal independent-source refinement is proved. Backend continuation,
cost completeness and final acceptance checks remain in progress.

## Implemented machine

`Applications.FRP.PendingCrash.Peer` is the lifetime-keyed atomic peer. A natural
number identity names a retained reservation, publication or prevention record.
An effective publish and its published receipt are one transition. Terminal
records cannot be overwritten. The peer uses list lookup and prefix-copying
updates, with the probes, allocations, copies and releases in its work trace.
Its arbitrary-command theorem proves that effect identities have no duplicates.
The weaker peer fixture shows two effects when effect execution and retained
receipt publication are separated by a crash.

`Frame` records both physical slots, admission order, lifetime names, inputs,
optional selected outputs, full terminal receipts, phases, open routes, logical
continuation and backend kind. Validation folds permitted successor changes
from the chosen initial frame. Merely satisfying the frame invariant does not
permit an arbitrary counter jump or arbitrary state replacement.

`Journal` executes the native append plan, cell write, persist, root publication,
acknowledgment, crash and reconstruction operations. Its executable disk is a
list; its proof fields connect that list to the native heap and carry actual
`Durability.Step` certificates. The allocation counter never reuses a journal
name, including names reserved by failed or interrupted appends. Durable cells
are retained even when no longer reachable from the root.

`Runtime` separates the bounded four-entry owned queue from external inbound and
outbound traffic. An adapter crash loses the owned queue and volatile backend
copies, but preserves the peer and submitted traffic. No caller-supplied raw
receipt command exists. Network delivery and duplication operate on actual peer
receipts. Recovery queries retained identities in admission order and handles
the returned receipts; executable reconciliation never inspects the peer table.
Cancellation queues reservation before cancellation. Local queue capacity is
checked before enqueueing the pair.

Preparation uses the actual native backend conversion and retains every keyed
request and traffic field. The local budget reserves journal/cache/queue storage
in addition to conversion storage. Root publication installs the new owner;
former-owner release and caller acknowledgment are separate steps. The migrated
acknowledgment is refused while a former owner remains.

## Claims already proved

Every runtime observation contains erased certificates for its exact native
journal transition or stutter and its exact keyed-peer command/effect trace.
`execute_native` and `execute_durability` compose the actual journal transitions
for arbitrary finite runtime command lists. `execute_accepted_prefix` and
`execute_acknowledged` reuse native accepted-history and acknowledgment-survival
results. These claims concern complete journal frame records; a frame commit is
not a peer effect or automatically a logical tick commit.

`execute_peer` identifies the runtime's external effects with its actual atomic
peer execution. `execute_effects_unique` then proves at most one external effect
per lifetime identity across arbitrary commands, retries, traffic duplication,
local crashes and reconstruction. It assumes the explicit atomic durable-peer
model. It supplies no network fairness or eventual completion theorem.

`Source` defines an independent Boolean delay source with ordered named
occurrences. An admission appends an occurrence, prevention removes that
occurrence, and an effective publication consumes the head with the previous
source state as its output. Confirmation and local commitment do not advance it
again. The executable `observedSource` checker returns a kernel-checked
`DelayRun` certificate when successful. `DelayStep.erase` connects its steps to
the existing independent pending-delay source without erasing any native
session's delayed callbacks.

`execute_source_refinement` in the consumer-local `Refinement` module
proves the independent `DelayRun` for every finite command list, from either
backend kind. It has no successful-checker premise. Its inductive invariant
relates the complete native accepted history to the stable frame, retains the
actual command that produced each outstanding append, authenticates terminal
receipts and queued traffic, and bounds every peer identity below the next fresh
name. The actual atomic peer publication advances the independent source;
confirmation and durable tick commitment preserve that already selected state.

The resumed-delay and stale-reply examples instantiate this theorem with
arbitrary continuations. The active native backend's continuation requires an
additional agreement invariant; the source refinement alone does not establish
that representation property. This remaining obligation and complete cost
review are tracked separately from the checked source result.

## Executable coverage

`Examples.PendingCrashRecovery` contains the frozen ten separating families:

1. A lost publication reply, crash, query and retained-output commit, followed by
   a second input with the resumed delay output.
2. Five admission, confirmation, tick and migration cuts spanning invocation,
   prepare, write, persistence and root publication; interrupted reconstruction.
3. Lost admission status without a new request identity.
4. Failed preparation, old-kind recovery before publication, new-kind recovery
   after publication, and a retained former owner blocking acknowledgment.
5. Prevention before publication versus too-late cancellation after publication.
6. A stale publication after slot reuse and a stale current reservation receipt.
7. Two effects for the deliberately weaker non-atomic peer.
8. Peer cancellation followed by crash before local cancellation publication.
9. Duplicate publication receipts and repeated evaluate/commit before and after
   restart, preserving selected output, state and committed frame count.
10. Failed preparation or interrupted second-admission persistence while an
    existing computed request retains its identity, outcome and order.

The examples also check independent source traces for resumed delay and lost
cancellation, cost categories for persistence/publication/reconstruction, failed
conversion work and release, former-owner overlap, and journal/table growth.
They use `decide` or `decide +kernel`; no native-decision axiom or raised resource
limit is introduced.

## Costs and scope

`Costs` keeps source-event work and flattened storage separate. Work reports
actual emitted table/cell probes, record checks, writes, persists, root cuts,
frame validations, message checks, reconstruction, conversion, attempted work,
allocation, copying and release. Its allocation-event occupancy records a peak
before subsequent releases. These are modeled source operations and cells,
not elapsed time or physical allocator measurements.

Storage reports the journal, durable peer table, cached history, pending before
and after copies, buffered cell, reconstruction accumulator, current frame,
active/target/former backends, local messages, external messages and controls.
Natural-number names have growing binary widths. The flattened encoding charges
shared payloads again; it does not assert physical pointer sharing or a durable
byte format. Retained bits and allocation-event cells are distinct units.

The journal and peer table grow with service lifetime. The two-slot and
four-owned-message bounds do not imply bounded lifetime storage. Progress
requires an external schedule that eventually processes the relevant submitted
message, delivers a terminal receipt and finishes local persistence/recovery.
Repeated crashes, permanent loss or indefinite starvation can prevent progress
without violating the safety properties.

The composition remains local to this consumer. It adds no universal recovery
scheduler and does not change the crash-free #515 contract. A physical durable
peer adapter and a lifetime-bounded retention/replay-fencing variant remain
separate work. Final #540 acceptance still requires native backend agreement, complete cost
and retained-witness review, full exact-candidate build and axiom audit,
and independent Standards and Spec review.
