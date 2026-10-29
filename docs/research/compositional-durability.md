# Compositional durability: preliminary research

Research date: 2026-10-29. This note supports the
[durability research direction](../durability-direction.md). It records primary
literature, connections to existing code, and proposed experiments. It does not
select a storage architecture or establish a new durability theorem.

The research question is whether a program's durability requirements can be
realized by reusable, verified components whose representation and coordination
choices remain specific to the program. A relational database would be one
possible specialization with additional query, transaction, administration,
and runtime flexibility requirements. Recovering that specialization is a
research test, not an established result or a claim that all databases impose
the same requirements.

## Existing foundations and the missing storage contract

The repository already distinguishes specifications, observations, and
realizations. This direction should extend the interaction work coordinated by
[#196](https://github.com/VladimirMarko/conaled/issues/196), whose concrete
investigation is [#194](https://github.com/VladimirMarko/conaled/issues/194).

| Existing code | Reuse and boundary |
|---|---|
| [InteractionContracts](../../SquareKit/InteractionContracts.lean) | `Safe` expresses endpoint partial correctness; `Stable` and `safe_interference_seq` expose stability under boundary interference. They do not model interruptions inside an operation unless its relation includes them. |
| [InteractionEvents](../../SquareKit/InteractionEvents.lean) | `interpret_simulation` lifts a primitive simulation to arbitrary finite scripts. Storage events could be a specialization, but a finite script theorem does not supply concurrent crash semantics or progress. |
| [Evidence](../../Applications/Interaction/Evidence.lean) | `no_effect_decision`, `retry_duplicates`, and `interrupted_no_ack` demonstrate observation ambiguity, duplicate effects, and safe recovery without progress. The model explicitly does not claim durable publication. |
| [Obligation](../../Applications/Interaction/Obligation.lean) | Acceptance, execution, and observation have distinct contracts. Atomic admission is not a physical persistence theorem. |

The [external interaction research](external-interaction-contracts.md) and
[optimization and recovery research](optimization-transport-and-recovery.md)
already identify storage and recovery obligations. The new contribution to
investigate is a persistence realization that discharges some of those
obligations, together with reusable composition and replacement rules. Existing
endpoint preservation must not be described as crash refinement without an
appropriate execution model and proof.

Representation choices coordinate with the data-structure effort
[#174](https://github.com/VladimirMarko/conaled/issues/174); comparisons of their
costs coordinate with [#177](https://github.com/VladimirMarko/conaled/issues/177).
The present proposal does not change the module boundaries of
[ADR 0001](../adr/0001-modules-and-proof-dependencies.md) or the distinct
relational contracts in [ADR 0002](../adr/0002-relations-and-synchronization.md).

## Crash recovery is already a semantic verification problem

**FSCQ and Crash Hoare Logic.** Chen et al. extend Hoare-style specifications
with crash conditions and recovery procedures, including crashes during
recovery. Their file-system proof reaches below a database interface to a
modeled disk. This supplies a direct precedent for specifying normal and
recovered behavior together and proving layered implementations. The 2015
system does not support multiprocessors or deferred durability. Its executable
path also trusts extraction-related infrastructure, the Haskell compiler and
runtime, and drivers. The result therefore supports extending verification
through persistence while retaining explicit environmental assumptions.
[Paper, §§3, 5–6](https://adam.chlipala.net/papers/FscqSOSP15/FscqSOSP15.pdf).

**Perennial.** Chajed et al. define concurrent recovery refinement using
implementation and specification transition systems with crashes. Concrete
executions must match permitted abstract observations; recovery, including
repeated interruption, is related to an abstract crash. Their logic builds on
Iris and addresses concurrent ownership and recovery. The 2019 paper explicitly
limits its results to safety and identifies abstraction-layer composition as
a limitation of that version. Its Go translation and modeled environment are
part of the connection to executable code, not a proof about arbitrary Go
programs or physical hardware.
[Paper, §§1, 3, 6](https://pdos.csail.mit.edu/papers/perennial%3Asosp19.pdf).

**GoJournal and Perennial 2.0.** The later GoJournal work provides a verified
concurrent journal and specifications usable by storage clients. Crash framing
and logically atomic crash specifications make modular reasoning possible
across its layers. This is particularly close to the proposed component idea:
a reusable persistence mechanism can hide internal interleavings behind a
proved contract. It supplies an atomicity mechanism, not a universal rule that
arbitrary independently durable components compose into an atomic operation.
Nor does its verification establish the proposed Lean framework or remove the
need to validate the runtime and storage assumptions of a particular deployment.
[Paper, §§2–5](https://www.usenix.org/system/files/osdi21-chajed.pdf).

These results rule out novelty claims based merely on verifying recovery or
packaging durability in a library. The proposed investigation concerns how
such contracts fit the repository's general realizations, how requirements
vary between programs, and which proofs survive a representation change.

## Distributed invariants determine coordination obligations

Bailis et al.'s invariant confluence characterizes when transactions can
preserve an invariant with coordination freedom, transactional availability,
and convergence in their replica-and-merge model. The condition checks whether
valid states reached from a common ancestor can merge to a valid state.
Theorem 1 is relative to these definitions and the chosen transactions,
invariant, and merge operation. It is not a universal decision procedure for
distributed requirements and does not establish disk durability.
[Extended paper, §§3–4 and Appendix B](https://arxiv.org/pdf/1402.2237).

For our direction, the inference is that coordination belongs among the
requirements of composition. It cannot be erased by replacing a database with
components. A hypothetical graph example makes the obligation concrete:
replicas independently add `a → b` and `b → a` to an empty graph. Each local
graph is acyclic, but their union is not. Any proposed acyclicity contract must
account for that execution through coordination, restricted operations, or a
different explicitly accepted behavior.

There is also a useful correction to the motivating discussion. Relational
systems can express recursive reachability: PostgreSQL documents recursive
queries and cycle handling. Expressing a query is distinct from enforcing a
global invariant across every admitted update and failure. The research should
compare those contracts, rather than assume relational storage cannot express
transitive relations.
[PostgreSQL 18 recursive queries](https://www.postgresql.org/docs/18/queries-with.html#QUERIES-WITH-RECURSIVE).

## Specialization and diagnostic queries

**Fiat** refines declarative abstract data types into functional programs with
Coq-checked derivations. Its query-structure case study derives implementations
of SQL-like queries and inserts from relational specifications, using selected
indexes. This is evidence for separating a data specification from its
specialized representation and implementation. Its refinement framework and
case study do not establish crash recovery or distributed durability; those
observations and transitions would need their own semantics and preservation
proofs.
[Delaware et al., POPL 2015, §§2–4](https://adam.chlipala.net/papers/FiatPOPL15/FiatPOPL15.pdf).

**DBSP** gives an algebra of stream computations and a compositional
incrementalization transformation. Its query examples include relational
operations and recursive computations such as transitive closure; the paper
reports Lean-checked theory. It is a candidate reference for a diagnostic
projection whose incremental result must agree with recomputation. The
mathematical stream and query theorems do not alone establish crash-safe
delivery, a consistent snapshot of a distributed source, or an end-to-end
verified query engine.
[Budiu et al., PVLDB 2023, §§2–6](https://www.vldb.org/pvldb/vol16/p1601-budiu.pdf).

Our proposed separation is to give a diagnostic view a contract of its own:
which authoritative snapshot or history prefix it represents, how lag is
reported, and whether it is reconstructible. A view consulted to authorize
operations becomes part of functional correctness; calling it observability
does not weaken that obligation. Rebuilding a diagnostic view is safe only
when its declared contract permits the missing or stale observations.

Neither Fiat nor DBSP establishes that a conventional database is exactly the
composition of the proposed components. They give bounded comparisons for
representation derivation and query semantics. Runtime query admission,
schema evolution, isolation, and administrative recovery remain separate
requirements to investigate before claiming that specialization.

## External effects and the remaining trust boundary

RIFL provides reusable machinery for exactly-once RPC execution under explicit
conditions. Its completion records must be durable and atomically coupled to
the operation's mutations; retries must find those records, and reclamation
must respect possible retries. The paper's basic guarantee assumes clients
do not crash and the storage system reliably retains its metadata. This is
evidence for carrying operation identity and retry behavior into a contract,
not for obtaining arbitrary external exactly-once effects from a local log.
[Lee et al., SOSP 2015, §§2–4 and 9](https://web.stanford.edu/~ouster/cgi-bin/papers/rifl.pdf).

For this project, a useful proof boundary would expose the following chain:
program observations; protocol and recovery transitions; encoded persistent
records; storage primitives; runtime and device assumptions. Each arrow needs
its own preservation contract. Removing a process boundary may remove some
communication overhead, but it does not prove that a persistent encoding,
flush ordering, or software migration preserves meaning. Performance claims
need a workload and measurements as well as a semantic theorem.

## First bounded experiment

Start with a hypothetical single-writer service accepting uniquely identified
commands into an ordered history. Acceptance means that, after any modeled
crash and completed recovery, the command remains in the recovered history.
An operation interrupted before its reply may either appear or be absent;
retries with the same identifier must not create another logical acceptance.
No external effect, replication, or general transaction engine is required.

Compare two realizations of this same contract: an append-only record history,
and a checkpoint plus a suffix of records. Explicitly model volatile state,
persistent bytes or blocks, and a primitive persistence boundary. If the first
model assumes atomic record writes, name that assumption and make tearing and
flush ordering a later refinement obligation. Do not infer physical durability
from a Boolean `persisted` field.

The design test would contain:

- A history observation preserving accepted identifiers and their order,
  including missing replies and crashes during recovery.
- Primitive simulations reused through existing event interpretation where
  its finite sequential scope fits, with any additional crash rule stated
  separately.
- A positive execution, a crash before persistence, and a crash after
  persistence but before acknowledgment. Prove that acknowledging before
  persistence admits a violating execution.
- Checkpoint replacement and record reclamation obligations: recovery must
  retain every accepted command before the old representation is discarded.
- A reconstructible diagnostic count indexed by a history prefix. State its
  lag contract without placing it on the acknowledgment path.
- A composition counterexample: two independently durable updates do not
  imply atomic survival of a joint operation. Add a positive composition
  only after identifying the shared persistence decision it requires.

Any eventual-completion result needs its own assumptions about storage progress
and a sufficiently long interval without crashes. The first safety result
should remain meaningful even when those assumptions fail. A formal follow-up
must use checked specializations, statement review, and the repository's build
and proof audit; this research note introduces no Lean declarations.

## Questions left open

1. Which observations must a replacement preserve so client proofs survive
   changes from logging to checkpoints, replication, or specialized layouts?
2. Can a useful composition rule expose shared commit, interference, and
   ownership obligations without forcing every client into one transaction
   language?
3. Which assumptions permit independent progress, and which invariants force
   coordination under the chosen failure and availability model?
4. How should cost contracts account for recovery, writes, retained history,
   and diagnostic reconstruction without mistaking modeled cost for latency?
5. How far can the implementation-to-storage proof be carried, and which
   compiler, operating-system, device, and migration assumptions remain?
6. Which additional requirements recover a useful relational database
   specialization, and which require genuinely different semantics?

This is a preliminary selection of primary sources, not a systematic survey
or a novelty determination. No upstream proof artifacts were rebuilt, no
performance experiment was run, and no storage backend was selected. The
first experiment is intended to constrain the abstraction before a broader
library or runtime commitment.

The direction is tracked in
[#225](https://github.com/VladimirMarko/conaled/issues/225), coordinated with
#196. Follow-up research remains open in
[#226](https://github.com/VladimirMarko/conaled/issues/226) for contracts,
composition, and the bounded recovery experiment, and
[#227](https://github.com/VladimirMarko/conaled/issues/227) for specialization,
diagnostic views, and cost. This survey does not complete those investigations.
