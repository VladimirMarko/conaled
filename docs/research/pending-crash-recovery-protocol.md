# Pending requests across migration and crash recovery

Protocol proposal for [#540](https://github.com/VladimirMarko/conaled/issues/540).
Code inspection baseline: `c214fb0720ffc998951255a7e4b5f2e80a299186`.
This is the specification-stage deliverable. Its transitions, simulations and
cost obligations require review before formal implementation. It establishes
no new checked theorem or physical storage guarantee.

## Selected composition

Use the initialized Boolean-delay consumer and two live request slots from
[PendingMigration](../../Applications/FRP/PendingMigration.lean), with its two
Circuit backends and selected checkpoint conversion. Use the typed,
append-only realization in
[Durability.Protocol](../../Applications/Durability/Protocol.lean),
`appendPlan` in [Storage](../../Applications/Durability/Storage.lean), and
[Executions](../../Applications/Durability/Executions.lean) for the local journal.
A record payload is a complete stable protocol frame. Reconstruct the last
committed frame after recovering the ordered journal.

The two-slot bound applies to active requests and the local four-entry message
queue. The retained local journal and peer receipt table grow with service
history. This proposal does **not** preserve #480's lifetime-independent storage
bound. Keep their sizes in the cost contract. A fixed-memory variant needs a
separate expiry and retirement contract; it cannot discard the history that
`Durability.Related` promises to recover.

`RetentionBanks` is an alternative for a later bounded retained-window service.
Its present `Snapshot` stores Boolean items, position and parity, and its
retention contract deliberately restricts historical observations. It is not a
drop-in durable store for the complete pending-request frame or full accepted
history. Do not generalize it merely to make this first composition smaller.

## Peer and failure contract

The peer is a specified durable state machine, independently surviving a local
adapter crash. Its table is keyed by a lifetime-unique natural-number request
identity. A table entry is reserved(input), published(input, output), or
cancelled(input). Identities are never reused during this service lifetime;
reusing a physical Boolean slot does not reuse its request identity. This does
not assert a constant metadata bit width.

A peer publication atomically installs the published receipt and produces the
one modeled external effect. A matching retry returns that retained receipt
without producing another effect. Conflicting input or output rejects; neither
publication nor cancellation overwrites a terminal entry. Cancellation of a
reservation atomically records prevented; cancellation after publication returns
too-late. Reservation itself is idempotent for an equal identity and input.

That atomic effect/receipt step is an explicit peer premise. Local durability
alone cannot implement it for an arbitrary external recipient. A peer whose
effect can survive while its receipt is lost does not satisfy this contract.
The first realization should implement this modeled peer transition and prove
its once-per-identity property; it should not claim a network or filesystem
implementation of the premise.

Messages can be delayed, duplicated, or lost. Returned receipts retain identity,
input, output where present, and terminal status. The environment can replay
actual receipts but cannot forge them. The local queue admits at most four
messages; excess delivery is refused and does not erase the peer receipt.
A local crash loses queued traffic and volatile preparations. It does not
cancel external messages already submitted or erase the peer table.

Only one local adapter incarnation may mutate or publish after recovery. The
crash transition ends the previous incarnation; a concurrent old process is
outside this crash-stop contract. Progress requires a sufficiently long
crash-free interval, successful storage operations, and scheduled delivery or
reconciliation. These are separate from safety.

## Stable frame and local commit point

A stable frame retains the active backend kind and Boolean delay state, the
ordered occupied slot indices, each slot's lifetime identity, input, selected
output when computed, phase and route status, and the next fresh identity.
The queue and prepared backend allocation are volatile. Full Circuit values
are reconstructed from the stored kind and logical state through the existing
realization/observation laws; this requires an explicit reconstruction lemma.

Each journal append has a separate fresh journal key. Request identity and
journal-record identity are different: several records describe one request.
The stable frame is accepted only if it passes the frame invariant and is the
permitted successor of the previous frame. Recovery does not accept an arbitrary
well-typed record as a valid protocol history.

Local frame publication is exactly `Durability.Step.publish`, after its cells
are persisted. Before this publication, recovery selects the previous frame;
after it, recovery selects the new frame. An adapter status acknowledging a
new durable phase is sent only after this local commit point. A lost status
leaves the caller uncertain; inspection/reconciliation reports the retained
phase without admitting a new request as an implicit retry.

## Operations and required ordering

| Operation | Before external action or status | Durable result and restart behavior |
|---|---|---|
| Admit | Reserve a free local slot and choose a fresh identity in a proposed frame. Persist and publish it before returning accepted or contacting the peer. | An accepted frame survives; an unpublished proposal was not accepted. Recovery idempotently reserves the retained identity at the peer before further work. |
| Evaluate | Compute the selected output and next state using the current head and backend. | Publish computed(input, output) before any publication request can leave the adapter. A crash may repeat pure computation, not the external effect. |
| Publish/retry | Require the durable computed phase and matching selected payload. | Peer effect/receipt publication and local confirmation are distinct. A lost reply leaves computed intact. Query or retry reconciles the same identity. |
| Confirm | Validate the returned identity and full payload against the live slot. Ignore nonterminal or stale receipts that would regress phase. | Persist confirmed before reporting confirmation. A crash before that local commit repeats reconciliation. |
| Tick commit | Require a retained published receipt for the head. | Publish one frame installing the input as next active state and marking the request committed. Recovery therefore cannot install that tick twice. |
| Cancel | Query/reserve the retained identity if necessary, then call peer cancellation. | Persist cancelled only on a prevented receipt. Too-late does not imply local confirmation; retain computed until the published receipt is reconciled. |
| Close/release | Permit only committed or cancelled requests. Close the local route, drain owned local callbacks, then persist release. | Peer terminal receipts remain retained. Late messages for the released identity cannot match a later slot occupant. Slot reuse allocates a fresh identity. |
| Prepare migration | Freeze business operations; copy and validate the selected active checkpoint with existing preparation events. | Preparation is volatile. Failure or cancellation leaves the last durable owner authoritative. |
| Commit migration | Require successful preparation. Persist a frame with the target kind and the same logical checkpoint. | Publish that frame before releasing the old allocation or returning migrated. A crash chooses old or new kind according to local publication; reconstruction preserves the same continuation. |

At most one frame append is in flight. Business operations are frozen during
that append and during migration preparation. A failed append leaves the old
committed frame authoritative. Dirty target allocations and incomplete journal
cells still require cleanup/accounting; failure is not zero work.

Recovery first runs the existing journal reconstruction. It validates the
history, reconstructs the active backend from the last frame, clears volatile
preparations and queue, and reconciles occupied identities in admission order.
It must not inspect the peer table directly as executable evidence. Reconciliation
uses returned peer receipts. Later pending requests cannot publish ahead of an
unresolved head.

## Separating traces

These are required formal fixtures, not claims of tests already executed.

1. Admit true, compute false, publish at the peer, lose its reply, crash, recover,
   query the same identity, confirm and commit. The external output is false
   once and the recovered active state is true. Then admit false and obtain true.
2. Crash after each local write, persist and root-publication cut in admission,
   confirmation, tick commit and migration. Only the root publication changes
   the recovered frame. A crash during reconstruction restarts reconstruction.
3. Lose an admission status after local publication. The retained request is
   visible on recovery; recovery must not silently allocate another identity.
4. Prepare migration, then fail validation or crash before owner publication.
   Recover the old kind. Crash after owner publication but before releasing the
   old copy; recover the new kind and account for cleanup of both copies.
5. Cancel before peer publication and recover the prevented receipt. Separately,
   publish first and lose the reply; cancellation is too-late, not prevented.
6. Release a terminal slot, reuse it for a different identity, and deliver an old
   published reply. It cannot confirm the new request. A delayed reserved reply
   for the current identity cannot undo a published confirmation.
7. Omit effect/receipt atomicity: let an external effect happen, lose the receipt,
   crash the peer, and retry. Two effects are possible. This rejects the weaker
   peer contract rather than proving exactly-once behavior from local storage.
8. Fail preparation or admission persistence while another accepted request is
   pending. Its identity, selected outcome and order remain in the old frame.

## Proof and cost handoff

The implementation must construct a relation from durable journal history and
peer receipts to the independent pending-delay source, including accepted
occurrences, prevented occurrences and effective output order. Local journal
commit and peer effect are different labeled events. Reuse
`PendingMigrationSource.step_refines` and `execution_refines` where an actual
native command can be projected; prove the new crash/recovery and keyed-receipt
cases separately. A projection must not forget a delayed reply merely to make
its validity premise hold.

Reuse `Durability.Related`, its per-step simulation, accepted-history prefix
lemmas and `acknowledged_survives` for journal records. Derive the protocol's
accepted-request history from valid frames. A durability acknowledgement of a
frame does not by itself acknowledge a peer effect or commit a logical tick.
Retain the old and target checkpoints in the migration proof, and identify the
exact comparison with #480's `prepare_commit` and suffix results.

Cost events must count each cell write/persist, root publication, recovery read,
frame validation, message check, peer table lookup/update, failed attempt,
checkpoint conversion, allocation, copy and release. Count the stored journal,
peer table, active/target backends, local queue, reconstruction accumulator and
old/new copies while they coexist. Use actual list traversals for this first
realization; indexed lookup is not constant-time by declaration. Record how
fresh-name ownership and identity widths grow. The two-slot and queue bounds
remain separate from these lifetime-dependent costs. No physical allocator,
network fairness, wall-clock latency or durable-byte encoding claim follows.

The initial implementation should use direct composition of these native
contracts. Extract a helper only if both its proof obligations and a second
consumer justify it. A universal recovery scheduler is outside #540.

## Acceptance gates and residual work

Independent Standards and Spec review must accept this protocol before Lean
composition begins. Formal completion still requires the successful and
rejecting traces, retained-witness statement review, full isolated candidate
build and axiom audit, and both review axes on the final candidate.

A lifetime-bounded storage variant would need an admitted expiry policy,
peer receipt retirement, replay fencing, finite identity reuse and an appropriate
retained-history observation contract. The current #225/#234 retention owners
should receive that gap if it is not already assigned. An external durable peer
adapter needs evidence for the selected effect/receipt premise. Neither gap is
silently discharged by the first modeled composition.
