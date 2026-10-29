# Accepted-history recovery across storage representations

Implementation for [#240](https://github.com/VladimirMarko/conaled/issues/240),
following [#226's contract experiment](durability-contract-experiment.md).
This is a semantic experiment with explicit target primitives. It does not
implement an operating-system adapter, database or crash-safe FRP driver.

The [storage layer](../../Applications/Durability/Storage.lean) has immutable
linked record cells, flat checkpoint records, and index cells containing their
ordered addresses. A root contains an optional checkpoint-index address and
an independent suffix tip. A log has no checkpoint. Checkpoint creation copies
the entire current history, creates a fresh index and starts an empty suffix.
Later append nodes link only within that suffix. The old log can therefore be
reclaimed without leaving links into its old prefix. Partial-prefix copying
with suffix relinking, studied in #227, is a different construction.

`Chain`, `Array`, `Prefix` and `Represents` describe the contents of actual
reachable cells. Their uniqueness proofs establish one decoded ordered history.
The append and checkpoint builders prove their layout certificates from the
cells they construct. A `Plan` carries this construction proof, not a permission
to publish. Publication separately requires every planned cell to be durable.

## Primitive assumptions and protocol

The [protocol](../../Applications/Durability/Protocol.lean) distinguishes request
invocation, volatile planning, buffered cell writes, individual cell persistence,
atomic durable root installation, acknowledgment, crash and recovery. Persistence
can stop after any subset of the written cells; each completed cell operation
survives. A crash erases the pending plan, buffered writes, active request,
query cache and recovery cursor. It leaves retained cells and the durable root.
A crash on either side of the atomic publication transition gives the old or
new root. No atomic multi-cell write is assumed.

These primitives exclude media corruption, rollback of completed writes and
torn roots. The root itself remains a typed atomic target primitive in both
interpretations. This is a substantial trusted capability, not a consequence
of the codec. The `used` set records allocation ownership and prevents address
reuse across crashes and reclamation. A target must supply fresh identities
with that property; the mathematical set is not an implemented allocator.
Finite-space targets must establish the builders' fresh-address and sufficient
space premises. No bounded-space or fixed-width address theorem is claimed.

There is one active request and one pending plan. Acknowledgment is enabled only
when the requested record occurs in the current cache and no plan is pending.
A committed retry returns the same record without appending. Conflicting payload
reuse rejects. Keys are `(session,id)`, with no wraparound assumption. Record
position is retained by the full-history prefix law, rather than carried as a
separate receipt wire field. Recovery and ordinary operations do not overlap.
Reclamation may remove only cells outside the root's pointer closure and runs
without concurrent readers. Removing one old cell at a time models interrupted
reclamation; crashes can leak unreachable cells but cannot lose reachable ones.

## Shared observations and proof reuse

`SpecStep` is an independent history specification with no cells, codecs or
checkpoint operations. Commitment requires an invoked fresh identity.
Acknowledgment requires the invoked record already to be committed. Queries
return the ordered history. Recovery returns that same history; safety does
not require eventual recovery.

The [simulation](../../Applications/Durability/Simulation.lean) proves that every
primitive protocol step preserves the representation invariant and simulates a
source step. It does not assume the desired history-preservation conclusion in
a transition guard. `Related` ties the root, online cache and any active cursor
to one abstract history. Its pending-plan component retains the source snapshot
until the cells are complete. `script_simulation` uses the existing
`Interaction.Events.interpret_simulation` to compose those primitive proofs.

The [client laws](../../Applications/Durability/Clients.lean) use
`Interaction.Refines.property` for history observations and
`Interaction.Refines.trans` for the encoded boundary. They preserve key
uniqueness, ordered folds and acknowledged records across arbitrary finite
failure/recovery histories. The source prefix theorem preserves payload and
position, not just a count. A fresh commit cannot repeat an existing key.
`acknowledged_client` is applied to a connected append, acknowledgment,
checkpoint, reclamation, crash and recovery execution.

The log and checkpoint/tail share these client proof bodies unchanged. Their
local obligations are the linked-node construction and flat-prefix/index
construction proofs. Encoding contributes round-trip and primitive simulation
proofs; it changes no history or ordered-fold client. No representation-specific
client proof remains in the worked two-record fold. The common expectation is
49, obtained from payloads 4 then 9 under `n ↦ 10*n + payload`.

## Recovery and encoding boundaries

The [recovery cursor](../../Applications/Durability/Recovery.lean) reads the
index, then each prefix cell, then follows the suffix backwards while restoring
chronological order. Each read is a separate transition. A crash discards this
cursor and restarts from the root. `Read.preserves` proves agreement of each
intermediate cursor with the authoritative history. `CursorRep.completes`
constructs a finite fault-free read path; it supplies no scheduler fairness or
latency guarantee when faults or delays continue.

The [encoded interpretation](../../Applications/Durability/Encoding.lean) stores
encoded blocks in both the write buffer and retained heap. Its write transition
encodes a cell, persistence copies that encoded cell, and recovery decodes the
actual retained block. `EncodedStep.simulation` proves these operations preserve
the typed protocol; `Step.encode` proves that typed executions are realizable
in the encoded model. Neither direction assumes a whole-run simulation law.
Malformed reachable blocks cannot satisfy the representation invariant or be
used as successful recovery reads.

`wordCodec` is a concrete tagged, length-framed natural-word format for natural
payload records and descriptor addresses. It checks exact record shapes and
rejects an incorrect descriptor length. Natural words and addresses are
unbounded; this is not a byte codec, finite-sector adapter or proof of physical
capacity. Pointer validity is supplied by the reachable-cell invariant, not
inferred from decoding a natural number. The direct typed interpretation needs
no encoding assumption for its payload type.

## Checked cases and statement review

[Examples.Durability](../../Examples/Durability.lean) retains the following
applications of the public results and actual transition constructors.

| Claims | Intended meaning and checked cases |
|---|---|
| Layout construction, uniqueness and pointer preservation | A fresh linked node appends exactly one record. The checkpoint stores full ordered records and a descriptor. The old root remains usable while a copied cell has persisted but its index has not. Reclamation preserves pointer closure; deleting the old log before changing its root fails. |
| Primitive and script simulation | Arbitrary finite protocol traces, including crashes between buffer/persist/publish/acknowledge phases, preserve a source history. Successful `append_execution` constructs an inhabited trace. Freshness is discharged for the two distinct example keys, not assumed inconsistent. |
| Retry, identity and acknowledgment | The first append commits once, identical retry acknowledges without another append, conflicting payload rejects. `early_acknowledgment` rules out an acknowledgment from the precommit cache. A postcommit crash can lose the response while retaining the record. The full connected recovery trace consumes `acknowledged_client`. |
| Recovery cursor correctness and conditional completion | Checkpoint record reads, suffix ordering and completion are separate steps. The retained case crashes after a prefix read and successfully reruns recovery. The generic completion statement requires an existing finite representation and a fault-free scheduled path, not perpetual progress. |
| Both layouts and both boundaries | One two-record client is instantiated for the log and for a recovered checkpoint with a newly appended disjoint suffix. Both executions lift to encoded transitions through the same word codec. The ordered-fold expectation distinguishes reversal. |
| Encoding | Exact round trips are proved for each cell constructor. Tagged node/flat layouts and descriptor length distinguish framing; malformed length rejects. Primitive write/persist/read simulation is separate from physical storage trust. |
| Composition failures and positive root | Independently persisting debit leaves balances `(9,0)`. The positive example constructs retained old/new joint balance objects and derives sum preservation from root choice plus representation uniqueness. Exclusive atomic publication and complete prior persistence remain explicit assumptions. Two individually acyclic single-edge relations form a cycle under union. |
| Missing target capability | With no retained or external evidence, one reboot observation cannot return both empty history and an acknowledged singleton correctly. Publishing a root before its cell persists has no representation witness. |
| Resource events | Storage annotations connect buffered writes, persistence, root installation, record/link/descriptor reads, single-cell reclamation and crashes to actual protocol steps. Weights remain separate and compose by list concatenation. |

Statement review checked quantifiers, implicit payload types, equality direction,
freshness premises, active-request requirements and nonvacuity. The initial
copy-array proof attempt incorrectly required preservation of all heap cells
when overwriting an unrelated address. Restricting the congruence obligation to
addresses actually read by the array corrected that proof interface. No
mathematical expectation was weakened. The representation certificates and
source fresh-key invariant are separate; the former do not alone establish
at-most-once admission.

## Resource accounting, validation and remaining trust

[ResourceEvents](../../Applications/Durability/ResourceEvents.lean) records
storage primitives and uses existing `Resources.reweight`. These annotations
are deliberately a storage-event interface, not a complete algorithm cost
model: volatile planning/copy computation, admission lookup, payload sizes,
codec work, allocation and synchronization tariffs need target-specific models.
No runtime, asymptotic or retained-space improvement is inferred. The selected
checkpoint writes every prefix record and its descriptor; it retains all
history, with temporary copies until publication and reclamation. Interrupted
attempts contribute their own executed operations.

The public entrypoint imports the connected cases. Acceptance requires the
README candidate build, exhaustive proof audit, final receipt verification and
independent Standards/Spec reviews. Candidate identities and command evidence
are retained in the orchestration record, rather than predicted in this note.

Deployment still needs compiler/runtime, storage-driver and device compliance
with the primitive model. Real byte formats, sector capacity, concurrent
readers/writers, address reuse, schema migration, replication and FRP delivery
remain outside this experiment. #241 owns the separate diagnostic-projection
extension. This implementation adds no diagnostic cache, SQL engine or graph
admission algorithm, and does not select a canonical persistence representation.
