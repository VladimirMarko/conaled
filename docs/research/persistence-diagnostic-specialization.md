# Persistence specialization and diagnostic query contracts

Assessment for [#227](https://github.com/VladimirMarko/conaled/issues/227),
2026-10-29. Extend #226's accepted-history experiment with a versioned diagnostic
projection. Keep its log/checkpoint comparison and failure model. The first
extension should prove that a delayed view identifies the committed prefix it
represents, and that a synchronous query sees one current snapshot. It should
not build a second recovery framework or select a production database.

The comparison below is a proposed model and implementation specification, not
new Lean proof or measured performance. Local declarations were inspected at
`db6102660070bb0b73f2b5b7e0cff3275f4f2291`. The
[durability contract experiment](durability-contract-experiment.md) owns the
storage and retry model; the [resource assessment](data-structure-resource-contracts.md)
owns general cost laws, and [target capabilities](data-structure-target-capabilities.md)
owns availability across settings. Keeping old data-structure versions does not
establish recovery after a machine crash.

## Sources and what they justify

| Primary source inspected | Useful construction or contract | Boundary for this work |
| --- | --- | --- |
| [Fiat, POPL 2015](https://adam.chlipala.net/papers/FiatPOPL15/FiatPOPL15.pdf), §§2–4 | Refine declarative abstract data types and SQL-like query/insert specifications into implementations with selected indexes, retaining Coq proof trails. | Representation derivation does not itself supply crash recovery, concurrent transaction semantics or arbitrary runtime schema evolution. |
| [DBSP, PVLDB 2023](https://www.vldb.org/pvldb/vol16/p1601-budiu.pdf), §§2–6 | Compositional incremental view maintenance over streams, including relational operations and recursion; the paper reports Lean-checked mathematical results. | Agreement with batch queries needs correct inputs and stream positions. It does not establish that updates and progress markers survive a crash together, or that a multi-source input is one snapshot. No upstream artifact was rebuilt here. |
| [FSCQ, SOSP 2015](https://adam.chlipala.net/papers/FscqSOSP15/FscqSOSP15.pdf), §§3, 5–6 | Crash conditions and recovery procedures extend normal postconditions; logging supports layered crash-safe filesystem behavior. | Its disk assumptions and extraction/runtime boundary remain explicit. A client value-refinement proof is not a substitute for these recovery obligations. |
| [SQLite overview](https://www.sqlite.org/about.html) and [atomic commit](https://www.sqlite.org/atomiccommit.html), §§2–5, 9 | An embedded in-process relational engine can provide transactions without a separate server. The rollback protocol accounts for journals, flushes, locking and recovery. | In-process operation removes neither the file representation nor the operating-system/device assumptions. Rollback-mode documentation is not the WAL protocol. |
| [DuckDB's design overview](https://duckdb.org/why_duckdb), accessed 2026-10-29 | Default in-process embedding and an analytical relational workload offer another existing combination of database functionality and local execution. | This is capability evidence, not a recommendation, benchmark, verified adapter or claim that all deployments avoid process boundaries. |
| [Invariant confluence, extended paper](https://arxiv.org/pdf/1402.2237), §§3–4 | Coordination freedom depends on closure of reachable valid states under the specified merge and transactions. | The criterion is relative to that availability/convergence model. It does not supply disk durability or certify the concrete graph checker below. |

Serialization and remote requests are separate choices. An embedded engine may
read its own persistent encoding directly while accepting typed host-language
arguments; a typed retained-cell model can omit a byte layer entirely. Neither
choice eliminates the need to justify storage primitives and observations.

## A dependency-history application with a transitive invariant

Consider a hypothetical single-writer dependency registry over a finite vertex
set `V`. Reuse #226's ordered history `H` of accepted `(session,id,payload)`
records. Here a payload is an edge `(u,v)`, meaning that `u` depends on `v`.
Distinct request identities may propose the same edge; history preserves both
accepted requests, while graph membership has set semantics. Exact replay of
one identity returns its prior receipt; conflicting reuse rejects. This keeps
identity/order observations separate from the graph quotient.

Let `E(H)` be the edges in the committed history and `Reach(H)` their nonempty
transitive closure. Require acyclicity: no `v` satisfies `Reach(H)(v,v)`.
For a new identity, admit `(u,v)` only if `u ≠ v` and `v` cannot already reach
`u`. Append the record and its receipt atomically under #226's root protocol.
These are proposed mathematical requirements. A finite algorithm still needs
termination and a proof that its computed reachability agrees with closure.

Five obligations must stay distinct:

- **Specification:** the graph invariant and the identity/ordered-history
  contract describe accepted states and replies independently of storage.
- **Query expression:** recursive relational queries can compute reachability.
  SQLite documents recursive CTEs and graph examples; relational storage does
  not exclude recursion. A finite `UNION` query over pairs removes duplicates;
  a path-enumerating `UNION ALL` query needs a separate termination argument.
  [SQLite recursive queries](https://www.sqlite.org/lang_with.html).
- **Incremental maintenance:** for insertion-only acyclic graphs, a proposed
  closure update adds pairs from predecessors of `u` (including `u`) to
  successors of `v` (including `v`). It requires a correct prior closure and
  the admission premise. Its agreement with recomputation must be proved.
  Deletion or arbitrary recursion is outside this slice; removing one witness
  path cannot simply remove a reachable pair that has another witness.
- **Concurrent enforcement:** two writers reading the empty graph can separately
  approve `a → b` and `b → a`. Their individually valid commits form a cycle.
  Rechecking in one serialized admission/commit region, or a proved concurrency
  protocol, is required. The first experiment retains one writer.
- **Recovery:** the recovered history must still be an accepted prefix, with
  its receipts and invariant. A volatile closure can be rebuilt before use;
  a persisted closure needs version agreement with its history. Neither a
  successful query nor its incrementalization proves crash safety.

A concrete recursive query can express the intended relation as follows. This
is explanatory SQL, not a validated SQLite adapter or a newly proved compiler.
`edges` is the distinct-edge relation derived from one fixed committed snapshot.

```sql
WITH RECURSIVE reach(src, dst) AS (
  SELECT src, dst FROM edges
  UNION
  SELECT reach.src, edges.dst
  FROM reach JOIN edges ON reach.dst = edges.src
)
SELECT src, dst FROM reach;
```

## Functional observations and two diagnostic contracts

The functional observer sees acceptance/rejection, identity lookup, ordered
history and its fold. These continue to use the authoritative committed history
from #226. A diagnostic observer returns reachability, counts or explanatory
paths through a separate projection `D(H)`. If an admission checker uses that
projection to authorize an edge, it becomes part of functional correctness and
must satisfy the stronger current-state obligation.

Let the authoritative commit position be `j = length H`. Views carry a generation
identifier and position `i`; generation distinguishes incompatible histories or
schemas. In the first experiment, history grows without truncation and one
fixed schema/generation is used. The general interface must not infer identity
of histories from equal counts.

| Obligation | Delayed reconstructible diagnostic | Immediate snapshot-consistent diagnostic |
| --- | --- | --- |
| Returned meaning | `(generation,i,D(take i H))`, with `i ≤ j` and the prefix identified exactly. | `D(Hj)` for one commit position selected between query invocation and response; every returned field uses that same snapshot. In the sequential experiment this is the current history. |
| Freshness | Stale answers are permitted and labeled. No finite lag guarantee is implicit. A lag bound needs scheduling/input-rate assumptions or explicit blocking. | A query after an acknowledgment must not select an earlier prefix than that acknowledged record. Concurrent later commits may be absent if the selected snapshot precedes them. |
| Retained information | Full authoritative history permits reconstruction. Persisted cached results need their matching position and interpretation; an incomplete rebuild is unavailable or leaves the old published view. | Full history plus synchronous computation suffices. A maintained cache must catch up before answering; persisting it is optional if recovery blocks queries until rebuild. |
| Publication | Build an unpublished candidate from one pinned prefix, then atomically publish the view together with its position. | Select/pin one committed snapshot, compute or validate its matching view, and return only that view. Publishing a new cache is atomic with its position. |
| Rebuild | Restart from a known complete snapshot and replay a suffix once, or rebuild from all history. Coupling the cursor with updated view prevents duplicate application. | Recovery remains unavailable until enough state exists to answer current-snapshot queries; no fixed response deadline is promised. |
| Authoritative-storage effect | None when a view is disposable and full history is retained. Retention of old inputs may be needed if a rebuild pins them. | No new durable cache is required by a synchronous API alone. Nonblocking postcrash availability or an acknowledgment promising view publication would impose additional obligations. |

For an incremental view, a crash after applying record `i+1` but before retaining
its cursor can replay the update twice. A set-valued closure may mask the error,
while a count exposes it. Persist the view/cursor atomically or discard both and
rebuild. Retain a non-idempotent diagnostic in checked applications so that
idempotent set insertion does not hide faulty replay.

Cross-component capture also needs a snapshot rule. The existing
[`Snapshot.individually_observed`, `never_coexisted`](../../Applications/Interaction/Snapshot.lean)
prove that individually observed fields can form a pair that never existed.
`Seal` seals an already collected value; it does not atomically collect live
sources. Therefore a diagnostic combining graph state and component metadata
must pin a common generation/root or prove a consistent-cut contract. A scan
followed by a version tag read is not such a proof.

## Storage assumptions before comparing representations

Use exactly #226's hypothetical target: immutable typed cells with stable
identities; explicit persistence completion; atomic durable root installation
only after all referenced cells persist; crashes erase volatile state but do
not corrupt or roll back completed durable writes. A partial persistence can
leave a subset of new cells. Recovery can crash repeatedly and restarts read-only
reconstruction; no query is served before it completes. One writer is active,
no reader overlaps replacement/reclamation, address reuse is excluded, and
sufficient space is an admission premise. Allocation failure cannot acknowledge
success. These are modeled primitive assumptions, not properties of ordinary
RAM or automatically of a filesystem API.

Compare under the same full-history, retry, acyclicity and diagnostic contract:

| Representation | Publication/recovery | Additional information |
| --- | --- | --- |
| Immutable linked log | Persist new record, install committed tip, then acknowledge. Recovery follows the committed chain and restores order/identity data. | Reconstruct graph and diagnostic view from the complete accepted history. Unreachable partial appends are not accepted history. |
| Full checkpoint plus linked tail | Copy an ordered prefix to fresh sequential cells and copy/relink the suffix into a disjoint chain; persist all new cells and the descriptor, then install its root. Recovery concatenates prefix and tail. | Keep full prefix records and identities. A summary-only checkpoint would violate ordered-history and retry observations. Any optional graph index must carry the same split/version. |

Both have a direct **typed retained-state** interpretation. For an **encoded
block** interpretation add record/tag/length framing, position/offset validity,
codec round trips on admitted records, decoder rejection of malformed reachable
objects, capacity checks, and a storage simulation preserving the root protocol.
Include schema version in the interpretation when evolution is allowed. No byte
codec is assumed for the typed interpretation. The encoded adapter adds proof
obligations; it does not create persistence or ordering guarantees.

A root may not outlive its referenced cells. Old checkpoint cells remain until
the new root is durably installed; post-install reclamation must preserve its
reachable closure. Reader concurrency or address reuse would require lifetime
and reclamation rules not present in this experiment. Recoverability depends on
reachable valid data, not a Boolean persisted flag.

## Explicit workloads and cost comparison

Use #177's `Resources` composition and reweighting, retaining each primitive
count separately. Consider `n` successful fresh appends followed by one checkpoint with a
sequential prefix of `k ≤ n` records and a copied linked suffix, `q` diagnostic
queries after recovery, and `r` completed
reconstructions at final length `n`. No retries or interrupted reconstructions
are charged in this initial comparison; adding them requires their actual trace.
Graph admission, deduplication, query traversal and view computation are shared
costs only when both candidates really use the same algorithms. Let `A(n)`
record that admission work and `G(n)` the work to rebuild the chosen graph view.
Do not call `G(n)` linear merely because history replay is linear.

The checkpoint is constructed after the complete original log of length `n`.
Traverse that log once, reading each record and following each link, and retain
its order in volatile construction state. Copy the first `k` records into the
sequential prefix and the remaining `n-k` into a fresh linked tail whose boundary
is the new descriptor's split, not an old-prefix cell. Write the descriptor,
persist all `n+1` new cells in one batch, then install the descriptor root.
Only after root installation completes, reclaim all `n` old log cells. There
are no later appends in this workload. This trace permits the old log to remain
recoverable throughout construction and leaves no new tail link into it.
Copying only the prefix of an immutable log would not justify its reclamation:
the retained tail would still reference that prefix.

The following counts define a proposed structural model. Root installation
includes its own durable completion and is counted separately from cell-batch
persistence. A record read excludes link-follow work. Sequential checkpoint
addressing is included in its read primitive. Metadata and payload sizes are
explicit parameters in a later encoded interpretation. Volatile staging and
record-field computation are outside this structural count, not assumed free
in a runtime cost model; encoded framing has its own additional costs.

| Count | Linked log | Checkpoint of `k` plus tail |
| --- | ---: | ---: |
| Append record writes | `n` | `n` |
| Append persistence completions / root installations | `n / n` | `n / n` |
| Checkpoint record reads / link follows / cell writes | `0 / 0 / 0` | `n / n / (n+1)` including copied suffix and descriptor |
| Old-cell reclamation operations after publication | `0` | `n` |
| Extra checkpoint persistence / root installation | `0 / 0` | `1 / 1` |
| Per-reconstruction record reads | `n` | `n` |
| Per-reconstruction link follows / descriptor reads | `n / 0` | `(n-k) / 1` |
| Graph-view reconstruction | `G(n)` | `G(n)` unless an additional index theorem changes it |
| Steady reachable record cells | `n` | `n+1` including descriptor |
| Peak retained cells during the one copy, excluding common root and volatile staging | `n` | `2*n+1` before old log reclamation |

After both recover into the same in-memory graph representation, their `q`
queries have equal chosen query work; that cancels in this comparison. If queries
scan persistent storage instead, charge the respective reads and traversals for
each query. Encoding adds record/descriptor byte writes and reads plus codec
work on every boundary actually crossed. Flush counts are not byte counts or
latency: weights depend on the target and batching protocol. Coordination is
one exclusive writer admission/commit region per append and one replacement
region for the checkpoint; there are no distributed messages in this model.

A worked arithmetic example uses `n=10`, `k=8` and unit weights for the displayed
read/write/link/descriptor/reclamation/persistence/root counts. Common `A(n)`, `G(n)` and
postrecovery query costs are excluded from both totals. Base append work is 30.
The checkpoint costs 43 extra: ten record reads, ten link follows, eleven cell
writes, ten reclamations, one persistence and one root installation. Each reconstruction costs 20 for the log and 13 for the
checkpoint/tail. One reconstruction gives totals 50 versus 86; seven give 170
versus 164. These are hypothetical model calculations, not timings. If link
following has zero weight while sequential reads remain unchanged, checkpoint
copying cannot pay for itself in this workload. No target-independent winner
follows. The checkpoint also retains an extra descriptor and has higher peak
storage, so lower weighted work need not dominate the multiobjective comparison.

Repeated incomplete recovery adds the reads/view work of every attempted prefix;
`r` successful recoveries alone does not bound that cost. With unbounded crashes
there is no finite completion-cost guarantee. Repeated checkpointing adds every
copy, synchronization and reclamation charge; the one-copy peak formula cannot
be silently reused. The reclamation count is a primitive model charge, not measured physical
reclamation work. Allocator behavior, cache locality,
codec throughput and device timing remain unmeasured.

## Optimizations blocked by observations and composition

1. **Dropping the old prefix after producing a summary.** Histories with the
   same edge count can have different identities, order and reachability.
   Keeping only that count breaks retry lookup and diagnostic paths. Even a
   correct full checkpoint cannot replace the old root before its referenced
   cells are durable. These are different failures: information loss and
   premature reclamation.
2. **Using a delayed view for admission.** Start with committed edge `a → b`
   but a published diagnostic for the empty prefix. Checking only that stale
   closure accepts `b → a` and violates acyclicity. A freshness label diagnoses
   this mismatch; it does not authorize using stale data as current evidence.
3. **Persisting independent components.** Suppose a dependency registry and a
   worker-assignment table require every assigned job's dependencies to exist
   in the registry generation named by the assignment. Persist and acknowledge
   the assignment before its referenced registry update; a crash retains the
   assignment but loses the dependency. Each component's local durability can
   hold while the joint invariant fails. A joint root/transaction, a durable
   dependency-before-assignment protocol with compatible recovery, or a weaker
   explicit pending-assignment contract is required.
4. **Acknowledging before the root commit.** A fresh edge can disappear after
   crash despite its acknowledgment. Batching acknowledgments is permissible
   only after the batch's durable decision; announcing eventual persistence
   changes the API. If acknowledgment additionally promises that a diagnostic
   is published, finishing the history append alone is insufficient.
5. **Reading fields independently for a faster query.** Joining a graph from
   generation `i` with assignment metadata from generation `i+1` can report
   an impossible combination. An immediate view needs snapshot capture or a
   proved retry/validation protocol, not only correct individual reads.

## Bounded relational-database specialization

A useful specialization is one embedded database for the same dependency
registry, not a derivation of a complete DBMS. Start with finite relations
`Accepted(session,id,position,src,dst)` and `Vertices(vertex)`, a unique request
key, and a distinct `Edges` view. The ordered history is ordered by `position`,
not by unspecified table iteration. Keep accepted duplicate-edge requests even
when `Edges` removes duplicate pairs. A retry compares the retained payload.

| Semantic requirement | Bounded specialization | Remaining work |
| --- | --- | --- |
| Query meaning | Finite set semantics for edges/closure; explicit order for history, optional results for missing identities; count accepted records separately from distinct edges. | SQL bags, NULL, collation, overflow, path enumeration and general query-language preservation. |
| Constraints | Key uniqueness, valid endpoints and acyclicity checked against the transaction's own authoritative snapshot. | A recursive query is not automatically a declarative constraint. Prove the admission procedure, including error/rollback behavior. |
| Transactions | Admission check, accepted record and receipt are one serialized durable commit. Queries observe one committed snapshot; retries after uncertain commit use retained identity. | Concurrent writers need conflict/revalidation proofs. External side effects or separate databases require a cross-component protocol. |
| Diagnostic views | Delayed versioned projection or synchronous snapshot query with the chosen API; recomputation remains the specification. | Persisted incremental indexes need view/cursor atomicity and replay laws. |
| Runtime evolution | Fix vertex/record types and query family initially; explicit version tags and compatible readers if a format change is later admitted. | Crash-safe schema migration, runtime query admission/planning, mixed-version writers, index rebuild publication and rollback compatibility. |
| Runtime/storage realization | State journal mode, synchronization policy, locking and filesystem/device assumptions; connect actual API success/error events to the model. | No SQLite/DuckDB backend, FFI proof, device compliance test or performance comparison is delivered here. |

SQLite's isolation documentation describes serialized writers and WAL snapshot
reads. These can supply an implementation route, subject to selecting the
right transaction boundaries and handling failed upgrades/retries. They are
not evidence that two separately issued check/write transactions enforce the
invariant. [SQLite isolation](https://www.sqlite.org/isolation.html).
Durability must also be configured: SQLite documents that WAL with
`synchronous=NORMAL` can lose committed transactions after power loss, whereas
`FULL` adds synchronization for durability. Verify the complete selected
configuration and environment, rather than treating SQL `COMMIT` as a universal
physical promise. [Synchronization settings](https://www.sqlite.org/pragma.html#pragma_synchronous).

## Local reuse and proposed follow-up

[`Interaction.Refines.trans` and `Refines.property`](../../SquareKit/InteractionContracts.lean)
compose observation relations once the storage, recovery and projection
relations are proved. `safe_interference_seq` requires stability under permitted
interference; it cannot insert a crash inside an opaque handler.
[`Interaction.Events.interpret_simulation`](../../SquareKit/InteractionEvents.lean)
lifts primitive simulation to finite scripts, but does not provide a scheduler,
concurrent transaction engine or crash-safe publication by itself.
[`Evidence.coarse_loses_publication`](../../Applications/Interaction/Evidence.lean)
is an existing warning against forgetting receipt/publication observations.
These are inspected declarations; this research did not rerun their build.

**Follow-up: add versioned diagnostic projections to the accepted-history
recovery experiment.** Depend on #226's semantic implementation rather than
forking it. Reuse both persistence representations and both typed/encoded
boundaries. The extra scope is projection correctness and client-visible
freshness, with the finite dependency graph as its connected application.

Acceptance:

1. Give a finite independent graph/closure specification and single-writer
   cycle-rejecting admission adapter over accepted history. Preserve identities,
   order, conflicting-retry rejection and durable acknowledgment laws.
2. Prove a delayed `(position,view)` publication invariant and a synchronous
   snapshot-query contract. Implement recomputation first; incremental closure
   is optional only if its exact-prefix agreement is proved. Include a count
   diagnostic to expose duplicate replay and a path/reachability diagnostic to
   distinguish histories with equal counts.
3. Reuse one projection client proof across log and full checkpoint/tail and
   both storage boundaries. Check crash before/after publication, repeated
   rebuild interruption, stale admission rejection, and the mixed-snapshot
   counterexample. Do not promise a fixed freshness or response bound.
4. Instrument the specified storage trace or supply exact counting functions
   linked to its transitions. Prove the one-checkpoint arithmetic model, with
   copy/transient storage and interrupted attempts explicit. Preserve primitive
   weights; no measured speed or physical space claim is required.
5. Check an explanatory relational snapshot interpretation with set edges and
   ordered accepted records. A SQL engine integration, concurrent admission,
   schema migration and production rollout remain excluded. New formal claims
   require statement review, checked applications, independent Standards/Spec
   review and README's candidate build/exhaustive audit.

This is an extension of the same experiment. #225 retains the broader durability
program; #177/#238 retain cost and target generality. Runtime evolution,
concurrency and real storage adapters remain named gaps rather than implied
consequences of the relational specialization.
