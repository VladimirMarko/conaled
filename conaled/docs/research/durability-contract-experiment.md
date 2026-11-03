# Durability contracts and the first recovery experiment

Assessment for [#226](https://github.com/VladimirMarko/conaled/issues/226),
2026-10-29. **Proceed with a bounded semantic experiment**: one sequential
accepted-history contract, a log and a checkpoint with a tail, and explicit
crash transitions. Compare typed retained-state primitives with an encoded
block boundary. Neither representation is selected for production. This note
specifies proposed results; it adds no Lean declarations or measured costs.

The [preliminary survey](compositional-durability.md) supplies broader context.
The new decision is to retain the complete ordered history in both realizations,
separate acknowledgment from commitment, and test recovery and reclamation
against the same client observations. This fits the append/query case shared
with [#238](https://github.com/VladimirMarko/conaled/issues/238) and
[#177](https://github.com/VladimirMarko/conaled/issues/177). Crash recovery is an
additional contract, not a consequence of having an in-memory data structure
or keeping old versions of it.

## What the repository already proves

The following inventory comes from reading the declarations at commit
`52751e27aef9c4d4ced7eaf697e2c5d16cc9500e`. These are existing checked
library claims; this documentation task did not rebuild them.

| Declaration | Reuse and limit |
|---|---|
| [InteractionContracts.Safe, Stable, safe_interference_seq](../../SquareKit/InteractionContracts.lean) | Endpoint safety composes when the intermediate assertion survives the permitted interference. Crashes inside a component must be included in its relation; the theorem does not insert them. |
| `Refines.trans`, `Refines.property` in the same module | Compose behavior relations and transfer only properties respected by the observation relation. Suitable for connecting storage, recovery and client observations once those relations have been proved. |
| `Run.invariant` in the same module | Preserves a stable predicate along an infinite run; supplies no fairness or eventual response. |
| [Interaction.Events.interpret_simulation](../../SquareKit/InteractionEvents.lean) | Primitive simulation lifts to finite scripts. Use crash and recovery microsteps as explicit events if this interface suffices. It cannot interrupt an opaque handler or branch on replies. |
| [Evidence.no_effect_decision, retry_duplicates, interrupted_no_ack](../../Applications/Interaction/Evidence.lean) | Missing acknowledgment cannot distinguish an absent effect from an already completed effect. Retrying can duplicate it; arbitrarily interrupted recovery can remain safe without finishing. Publication in this model is explicitly not durable. |
| [Evidence.coarse_loses_publication](../../Applications/Interaction/Evidence.lean) | A count-only observation can conceal lost publication. Retain identity, order and acknowledgments in the proposed observation relation. |
| [Obligation.tryAccept_iff, script_bound, delayed_attempt](../../Applications/Interaction/Obligation.lean) | Admission establishes receipt/intent together, identity survives scripted operations, and a lease counter does not fence delayed effects. No physical persistence or downstream exactly-once guarantee follows. |

The missing layer is a transition system with volatile and retained state,
crash points inside operations, recovery-mode transitions, and an observation
relation preserving durable commitments. Start there rather than introducing
a universal effect syntax. This respects the distinct relational contracts in
[ADR 0002](../adr/0002-relations-and-synchronization.md).

## Primary-source comparison

Versions below identify the publications assessed, not current repository tips.
No upstream proof artifact was rebuilt.

| Source | Failure and acknowledgment/recovery contract | Composition and trusted boundary |
|---|---|---|
| [FSCQ / Crash Hoare Logic, SOSP 2015, §§3, 5–6](https://adam.chlipala.net/papers/FscqSOSP15/FscqSOSP15.pdf) | Fail-stop crashes discard execution state; the disk model permits asynchronous writes and assumes atomic sector writes. Normal and crash postconditions differ; recovery may itself crash repeatedly. Completed synchronous operations survive; interrupted filesystem calls recover atomically. The system lacks deferred durability. | Crash conditions, recovery specifications, separation and logical address spaces support layered proofs. Atomicity comes from a proved logging layer. Coq checking, extraction, Haskell compiler/runtime, driver/FUSE path and compliance with the modeled disk assumptions remain trusted. |
| [Perennial, SOSP 2019, §§3, 5–9](https://pdos.csail.mit.edu/papers/perennial:sosp19.pdf) | Concurrent recovery refinement matches concrete executions to abstract transitions. A crash followed by repeatedly interrupted recovery matches an abstract crash step. Mailboat specifies durability of delivered messages and complete-message reads. Its Goose filesystem model does not support deferred durability. | Recovery leases/helping and versioned memory handle concurrency and lost volatile ownership. The 2019 framework explicitly lacks abstraction-layer composition and proves safety, not liveness. Trust includes Coq, the Goose translation, Go execution and the modeled filesystem/environment boundary. |
| [GoJournal / Perennial 2.0, OSDI 2021, §§2–5](https://www.usenix.org/system/files/osdi21-chajed.pdf) | A concurrent journal provides atomic persistence for client transactions under its storage model. Crash specifications distinguish completed operations from permitted crash outcomes. | Crash framing, predicate lifting and logically atomic crash specifications support modular clients and implementation layers. Clients must use the journal's transaction contract; independently durable components do not thereby become jointly atomic. The runtime and disk model remain deployment obligations. |

These are precedents for the proposed proof boundaries, not imported Lean
proofs. In particular, use a storage primitive's *specified durable completion*
as the local commit observation; a function return or emitted response is not
universally such an observation.

## Contract and observations

The worked example is a single-writer accepted history `H` of records
`(session, id, payload)`. Identity is the pair `(session,id)`, with no reuse
within the experiment. The abstract interface has append-if-fresh, lookup by
identity, ordered-history query, and a deterministic fold of the payloads.
A retry with identical identity and payload returns the prior receipt; reuse
with a different payload is rejected without mutation. Only one request is
active at a time, and operations are disabled during recovery. This contract
is narrower than an arbitrary concurrent service.

Observe invocation, durable commitment, external acknowledgment, crash,
recovery completion and query result. Commitment may be hidden from the external
client, but remains in the semantic history used to explain observations.
A fresh append commits at most once. Each acknowledgment identifies its
committed record and position. Every completed query sees the full current
committed history; a fold result agrees with that history. Committed records
form an append-only sequence and remain after every completed recovery.
An interrupted, unacknowledged request may have committed or may be absent;
its later retry determines which by retained identity, without another append.
Uninvoked records cannot appear. The observation relation must preserve these
constraints, not merely a final count.

Safety applies to every finite prefix, including any number of crashes during
recovery. Recovery exposes no query results until reconstruction completes.
Eventual recovery is a separate proposed conditional theorem: finite reachable
storage, terminating primitive reads, scheduled recovery steps, and an interval
without faults long enough for reconstruction imply completion. Indefinite
faults permit no completion, consistently with `Evidence.interrupted_no_ack`.
A retrying client additionally needs request/reply delivery assumptions.

## Capabilities before representations

Use the following *hypothetical target model*, not an assertion about ordinary
RAM, a filesystem API, or a particular persistent-memory device:

- Immutable cells have stable identities and values after successful persistence.
  Reads of retained cells survive reboot. The fault model excludes corruption,
  device loss and rollback of successfully persisted cells.
- A persistence operation can be interrupted. Its completion guarantees that
  its specified cells are retained. Before completion, any subset may survive.
- A distinguished root can be installed atomically and durably. Interruption
  permits the old or new root; successful completion guarantees the new root.
  Every referenced cell must be persisted before installation begins.
- Crashes erase volatile cursors, caches and in-progress computations. They
  preserve the root according to the installation rule and all committed
  reachable cells. Recovery reads the root and reachable objects; a further
  crash restarts this reconstruction without mutating authoritative state.
- There is one writer, no live readers during replacement/reclamation, no
  address reuse in the first experiment, and enough space for old and new
  reachable objects during replacement. Allocation failure rejects before
  commitment; it must not acknowledge success.

These assumptions intentionally make the first proof small. Atomic durable
root installation is a substantial assumed capability requiring later
refinement, not a result derived from serialization. If root writes can tear,
or a root can persist before its children, the new root can name an unreadable
history after a crash. That history refutes the proposed contract.

| Target boundary | Additional obligations | Result under this model |
|---|---|---|
| Typed retained cells and root | Stable typed values, referent lifetime, atomic publication, persistence ordering | Direct semantic realization; no byte codec is required. A hardware/runtime mapping remains unproved. |
| Encoded cells in persistent blocks | Encode/decode round trip for admitted records, unambiguous framing and lengths, valid root/offset decoding, capacity bounds, rejection of malformed reachable objects; root atomicity and ordering as above | Same semantic contract if these obligations and primitive refinement hold. Decoding success alone says nothing about survival. |
| Volatile memory only, with no retained or external witness | Two executions, empty history and an acknowledged append, both restart to identical state | Cannot answer the fresh postcrash history query correctly for both executions. Additional external evidence or a weaker contract is necessary. |

The impossibility case assumes the query supplies no missing history and the
environment provides no distinguishing information after restart. A stateless
worker consuming an externally retained history is a different target boundary.
Bounded storage also requires admission/capacity restrictions or a weaker
retention contract; keeping every accepted record is not indefinitely bounded.

## Log and checkpoint with a tail

The log consists of immutable linked records and a root naming its committed
tip. An append persists the new record, then installs the new tip, then may
acknowledge. Recovery follows the committed chain, reconstructs its order and
identity table, and ignores unreachable partial appends. This deliberately
uses a root publication step rather than assuming arbitrary record appends are
failure-atomic.

The second representation has a root descriptor naming a checkpoint of an
ordered prefix and a disjoint suffix chain. The descriptor includes the split
position. Recovery concatenates the prefix and suffix and checks identity and
position consistency. Checkpoint creation copies the prefix into fresh cells,
persists them and the descriptor, and installs the root only after all of them
are retained. It may then reclaim objects unreachable from the new root.
Reclamation itself must leave that reachable closure untouched. With no reader
concurrency or address reuse, interruption during reclamation only leaks space.

A checkpoint retains the complete logical prefix. Keeping only a count or
monoid summary would lose the ordered-history and retry observations. This
experiment therefore does **not** promise reduced asymptotic retained history
or faster total reconstruction: it compares layouts and publication obligations.
Later #227 may assess weaker diagnostic observations or indexed checkpoints
without silently changing the authoritative contract.

Checkpointing exposes a recovery obligation absent from a Boolean persisted
flag: an old acknowledged prefix must remain recoverable while the replacement
is incomplete. If the old prefix is deleted before the new root is durably
installed, crashing at that point leaves neither usable representation.

## Proposed statements and checked applications

The follow-up should state and prove these results, with mathematical source
relations written independently of executable handlers:

1. **Reachability invariant.** Every permitted primitive step and crash leaves
   the active root's reachable closure complete and representing exactly the
   committed history. Recovery restart preserves this invariant.
2. **Acknowledgment and retry safety.** Every acknowledgment names a unique
   committed record; arbitrary later crashes and completed recoveries preserve
   its identity, payload and position. Retrying a committed request does not
   append; conflicting reuse rejects. Include absence before commitment.
3. **Representation refinement.** Both the log and checkpoint/tail transitions
   refine the same history contract, including intermediate crash points and
   repeated recovery interruption. Checkpoint publication and safe reclamation
   preserve the history observation.
4. **Boundary refinement.** Under explicit codec and storage hypotheses, the
   encoded realization simulates typed retained primitives. Instantiate a
   small concrete codec in checked applications; leave device compliance as
   an explicit premise. Direct typed use requires no codec hypothesis.
5. **Client reuse.** Prove once that a query fold equals the ordered committed
   payload fold and that a named acknowledged record survives recovery. Apply
   those exact client theorems to both representations and both boundaries
   through existing `Refines.property`/`Refines.trans` where applicable.
   Record which proof bodies stay unchanged, which simulation premises differ,
   and any remaining representation-specific client steps. Zero such steps is
   a design target, not an already established result.

Checked examples must cover success; crash before cell persistence; crash after
root commitment but before acknowledgment; identical retry; conflicting reuse;
crash during checkpoint creation, root installation, recovery and reclamation;
and the early-acknowledgment and early-reclamation counterexamples. Include a
noncommutative payload fold or the full history so reversed order cannot pass
because a count happens to agree. Recovery progress may remain a separately
stated obligation; no safety theorem should imply it vacuously.

For #177/#227, count logical records separately from encoded bytes, cell writes,
persistence completions, root installations, checkpoint copying, retained and
transient space, recovery reads, and query work. Compare explicit numbers of
appends, queries and failures, including repeated interrupted reconstruction.
Any cost bound assumes sufficient storage and the declared primitive weights;
none estimates wall-clock latency without a target measurement.

## Composition counterexamples and obligations

A hypothetical transfer starts with independently durable balances `(10,0)`
and must preserve their sum. Persist debit to `(9,0)`, crash before credit,
then recover each component correctly. Both local durability contracts hold,
but the joint sum invariant fails, even without a joint acknowledgment.
Acknowledging the transfer early would additionally violate its receipt.

To exclude this history, require an atomic shared commit decision and compatible
recovery across both updates, or allow an explicit intermediate obligation in
a different specification. A positive bounded construction puts both new
balances under one root and publishes it after both persist. Its proof needs
exclusive update authority, joint-invariant preservation, root ordering, and
recovery that chooses both old or both new. Independent roots without a shared
protocol do not discharge those premises. Compensation also requires a contract
allowing the intermediate state and assumptions under which it can finish.

For distribution, use the hypothetical acyclic graph from the survey. Replicas
starting from an empty graph separately admit `a → b` and `b → a`. Each local
graph is acyclic and each update can be durable, yet union creates a cycle.
[Bailis et al., extended invariant-confluence paper, §§3–4 and Appendix B](https://arxiv.org/pdf/1402.2237)
characterizes coordination freedom relative to transactions, invariants,
merge, availability and convergence assumptions. This case fails closure under
merge. Preventing it requires coordination, restricting admissible operations
(for example edges following a fixed order), or weakening the invariant or
availability requirement. Disk persistence alone cannot supply that choice.

## FRP publication and session boundaries

The existing [lifecycle](../../Applications/FRP/Lifecycle.lean) stores an engine
and optional last accepted ID; `init` resets that mark. Its
[at_most_once and marks_monotone](../../Applications/FRP/LifecycleSafety.lean)
theorems quantify over its own transitions, which contain no crash/restore
operation. An internal emitted response precedes external receipt; restoring
an older accepted-ID mark can permit a replay. Neither history contradicts
the existing theorems. [#233](https://github.com/VladimirMarko/conaled/issues/233)
retains ownership of driver acceptance.

A proposed durable adapter must bind `(session,id)` to accepted intent before
acknowledging acceptance, and bind response contents plus completion identity
before publishing a replayable response. These bindings must be recovered
together with sufficient engine/source information to justify the response, or
with a retained response that can be retransmitted without recomputation.
Persisting the ID mark alone prevents neither loss of accepted work nor
incorrectly reconstructed output. Restoring a consumer fold also needs a commit
position so replay does not apply its contribution twice.

If publication succeeds and the reply is lost, retain the completion and permit
retransmission. Exactly-once *external receipt/effect* additionally requires a
receiver deduplicating the same stable identity, or a jointly specified protocol;
a local log cannot establish it. This is the concrete ambiguity already proved
by #194's `Evidence.no_effect_decision` and `retry_duplicates`.
Restart with a new session requires an environmental nonreuse/isolation guarantee
and a rule for old messages. Resetting a finite counter or inventing a fresh
session label without such evidence is insufficient. The bounded experiment
uses mathematical nonreused identities; fixed-width reuse and crash-safe FRP
runtime integration remain follow-ups to #232/#233, not a second driver here.

## Trust, exclusions and recommendation

The intended proof chain is client observation, history refinement,
representation invariant, optional codec refinement, then retained-cell/root
primitives. A deployment must still establish atomicity, flush/order semantics,
address lifetime and power-failure behavior through its actual runtime,
compiler, operating system and device. The typed model moves that obligation
to its primitive boundary; it does not remove it. The encoded model adds codec
laws without strengthening the underlying storage guarantee.

Representation evolution across software versions is excluded: one fixed
record interpretation, root format and recovery algorithm per run, including
restarts. Future migration must preserve the observation relation across old
and new formats, retain a recoverable version through interrupted conversion,
and gate acknowledgments on the new durability obligations. Concurrent writers,
replication, real I/O, media corruption and address reuse are also excluded.

Proceed because the shared history client distinguishes ordering, retry,
checkpoint publication and reclamation failures while allowing client-proof
reuse to be assessed. Narrow the implementation to the above semantic models
and checked examples; defer production adapters and a general concurrent
crash logic. #227 should reuse these observations and failure laws when
assessing diagnostic projections. #238 owns cross-target applicability; #177
owns general resource contracts. No whole book or upstream logic port is a
prerequisite.
