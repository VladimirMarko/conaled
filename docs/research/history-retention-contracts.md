# Observation-preserving history retention and durable reclamation

Research for [#247](https://github.com/VladimirMarko/conaled/issues/247),
2026-10-29. Code audit baseline: `826a76272e414af16d98797403655aef1ddae45f`.
The [implementation record](retained-history-implementation.md) describes the
checked #251 realization and its target/driver premises.

This note specifies a bounded experiment; it adds no Lean theorem or production
storage guarantee. The proposed laws and resource bounds below remain proof
obligations. Existing unrestricted history clients keep their contracts.

## Recommendation

Implement an opt-in, finite-lifetime retained-window service with explicit query
and retry expiry. Compare its summary observation with a smaller summary-only
service. Preserve the complete history as a specification witness, not as an
implementation field. Start with Boolean payloads and one sequential client so
that information loss, crash recovery, and memory ownership can be checked
without introducing a general retention framework.

Forgetting records changes the observations a service can promise. Reclaiming
an obsolete copy does not. The current durability implementation establishes the
second operation; its public history contract prohibits the first. A future
adapter must publish its retention boundary together with the data and retry
state that justify the admitted observations.

## What the existing code actually requires

| Code and declarations | Requirement and reuse boundary |
|---|---|
| [Storage.lean](../../Applications/Durability/Storage.lean): `Record.key`, `Represents`, `Plan.shape`, `checkpointPlan` | Identity is `(session,id)`. Representation reconstructs every record in order. A plan produces the same history or appends one record; a checkpoint copies the full history. Dropping a logical prefix does not satisfy this plan contract. |
| [Protocol.lean](../../Applications/Durability/Protocol.lean): `Fresh`, `SpecStep`, `Related` | Freshness checks all historic keys; exact retries acknowledge existing records, conflicting payload reuse rejects. `query` and `recover` expose the whole history. Both root and ready cache relate to that history. These statements cannot be instantiated with a truncated cache. |
| [Clients.lean](../../Applications/Durability/Clients.lean): `SpecStep.prefix`, `acknowledged_survives`, `history_client`, `Related.fold` | Histories only grow; acknowledged records remain members at their original positions. Arbitrary history predicates and ordered folds transport because full histories agree. These client conclusions remain available on the unrestricted service. For a retained service, transport only predicates determined by its admitted observations, through a new relation. |
| [Recovery.lean](../../Applications/Durability/Recovery.lean): `CursorRep`, `Read.preserves`, `CursorRep.completes` | Recovery rebuilds full ordered history. The traversal pattern and fault-free completion argument are useful, but new descriptor and summary semantics require new invariant statements. Completion does not promise progress under endless crashes. |
| [DiagnosticProjection.lean](../../Applications/Durability/DiagnosticProjection.lean): `Agrees`, `agrees_extend`, `ProjectionInv`, `projection_preserves` | A delayed view denotes a prefix of the same append-only history. Rebuild state stores `seen` and `todo` lists. Truncating the authoritative list breaks this invariant; resetting positions makes stale views ambiguous. The new contract needs explicit base/end positions and pinned snapshot ownership. |
| [DiagnosticGraph.lean](../../Applications/Durability/DiagnosticGraph.lean): `allows`, `AdmissionStep`, `closure_correct` | Cycle admission inspects current authoritative history, never a delayed view. An old edge can still forbid a new edge after leaving a query window. Window-local acyclicity would be a different contract. |
| [Storage.lean](../../Applications/Durability/Storage.lean): `RootNeeds`, `KeepsRoot`, `Represents.keep`; [Protocol.lean](../../Applications/Durability/Protocol.lean): `Step.reclaim`, `Machine.used` | Reclamation preserves cells reachable from the current root and runs with no active request or plan. Recovery is offline. There are no concurrent external readers. `used` prevents address reuse forever, even after freeing a cell; bounded live cells therefore do not establish bounded allocator metadata or addresses. |
| [DiagnosticStorage.lean](../../Applications/Durability/DiagnosticStorage.lean): `reclaim_cells`, `copy_peak`, `interrupted_space` | Existing reachability and explicit event accounting are useful patterns. Their full-copy counts and accumulated garbage model do not prove a bounded recycling allocator. |
| [Encoding.lean](../../Applications/Durability/Encoding.lean): `Codec`, `encoding_refinement` | Decoding preserves the current cell machine under codec laws. A retained descriptor needs its own encoding instance and step simulation; a codec is not a substitute for a persistence/publication law. |

The reusable architectural route is
[`Interaction.Refines.property`](../../SquareKit/InteractionContracts.lean),
plus relational execution composition, not a claim that the current
`history_refinement` already covers logical forgetting.

[#237](https://github.com/VladimirMarko/conaled/issues/237) owns the concrete FRP
adapter. Its lower query boundary `q` admits `q ≤ t < frontier`, keeps records
at `q`, and refuses to invalidate pending work. This agrees with the actual
[Frontier.lean](../../Applications/FRP/Frontier.lean) definitions:
`State.Completes` quantifies below the frontier, `advance` appends batches, and
`observeMerge` has an upper-frontier check but no lower-retention check.
[The request-identity assessment](frp-request-identity.md#history-reclamation-requires-a-query-contract)
explains why advancing completeness alone cannot authorize deletion. This
investigation shares the admission/preservation obligations, but does not
implement or redefine that timestamp adapter.

## A precise bounded candidate contract

Fix `1 ≤ W ≤ K`, Boolean payloads, one fixed service incarnation `E`, and one
sequential client. There are at most `K` accepted requests in this incarnation.
The fixed incarnation has a bounded encoding. Accepted request IDs satisfy
`i < K`; the request field also admits the sentinel `K` to report exhaustion.
The next fresh ID is exactly `n`, the number
already committed. Positions and counters range from zero through `K`, with
checked overflow. No operation resets `n`, reuses an ID, or creates a new
incarnation. Exhaustion is observable. This finite lifetime is deliberate:
indefinite service, arbitrary clients and reusable names need additional laws.

The independent reference state has ghost history `H`, `n = length H`, lower
boundary `q = max(0,n-W)`, one optional pending request, online/offline status,
and at most one snapshot pin. The stored state has `q`, `n`, the ordered suffix
`L = H[q:n]`, and prefix parity `b = xor(H[0:q])`. All retained records carry
their implicit position, incarnation and Boolean payload. Neither the entire
`H` nor an ever-growing set of allocated addresses is stored.

The following are proposed externally observable rules, not checked results.
Ordinary requests while offline return `Unavailable`; reads and summaries while
a mutation is pending return `Busy`. A synchronous read acquires and releases
the same pin around its bounded response construction.

- `read(a,z)` returns the ordered records `H[a:z]` when `q ≤ a ≤ z ≤ n`.
  A well-formed range with `a < q` returns `Expired(q)` even if empty. Invalid
  bounds return `InvalidRange`; results never substitute an empty list for
  expired history. The boundary record at `q` remains queryable. A synchronous
  `summary` returns `(E,n,xor(H))`, computed from `b` and `L`.
- With no pending operation or pin, `append(E,i,p)` checks the incarnation,
  then classifies the ID. `i < q` returns `Expired(q)` without deciding whether
  the payload matches. For `q ≤ i < n`, matching payload returns the original
  acknowledgment `(E,i)` without committing; a different payload returns
  `Conflict`. `i > n` returns `OutOfOrder(n)`. Only `i = n < K` may append.
  At `n = K`, requesting `i = K` returns `Exhausted`; retained retries still work.
  An incarnation mismatch returns `WrongIncarnation`. The wire interface must
  reject out-of-domain IDs rather than wrap them.
- Invocation reserves one pending request. Other appends, retention changes and
  snapshot acquisition return `Busy` until it terminates. Publication atomically
  installs the new suffix, `n+1`, its derived boundary and prefix parity.
  Acknowledgment follows durable publication and clears pending work. The
  newest record remains retained because `W ≥ 1`; no intervening append can
  expire it before this acknowledgment. Rejected operations leave state intact.
- A lost acknowledgment is ambiguous to the caller. Crash before publication
  leaves the old state; crash after publication leaves the committed state.
  Restart restores the durable descriptor, including `q`, `n`, retry payloads
  and parity, before serving requests. Retrying the current ID then either
  commits or acknowledges once. A client that lets later accepted requests
  advance past its ID gets `Expired`, not evidence of nonexecution. Exactly-once
  delivery of acknowledgments is not promised.
- An acknowledged effect survives as part of cumulative parity and the ghost
  history; the service promises payload retrieval and conflict discrimination
  only while the ID is retained. Returning `Expired` after eviction is an
  explicit weakening of the old `acknowledged_survives` *observable membership*
  guarantee, not a proof of that theorem for smaller storage.
- `pin` captures `(E,q,n,L,b)` and blocks mutation until `release`. An attempt
  to acquire a second pin returns `Busy` without changing the first. It admits
  one streaming read or one diagnostic rebuild. No public raw address escapes.
  Rebuild scans this bounded snapshot and publishes `(E,n,parity)` as one tuple,
  then releases the pin. A completed delayed tuple may remain after later
  commits; its position must be exposed. It cannot answer current-summary,
  current-retention or admission queries. Asking for a minimum position above
  its position returns `NotReady`; asking for a historical range below current
  `q` still returns `Expired`.
- Within a connection, a pin is an affine, scoped capability supplied by the
  driver, not a replayable numeric token. Only its current owner may use it;
  `release` consumes it. The driver must prevent aliases, delayed uses and
  duplicated releases after consumption, including after reacquisition at the
  same position. Such calls are outside the admitted client contract, not
  requests for which this service promises an `InvalidHandle` response. Repeated
  release/reacquire cycles are allowed under that ownership premise and need
  no growing generation counter. A raw network-handle API requires a separate
  freshness/exhaustion protocol; a single recycled slot ID cannot implement it.
- Pins and unfinished rebuilds are volatile. Crash cancels them and clears
  published delayed tuples. External handles are scoped to a connection that
  restart closes; old handles return `InvalidHandle`, never regain access by
  reusing a slot number. This requires a driver that actually fences old
  connections. This restart rule is separate from the within-connection affine
  ownership premise. If handles survive process restart, durable incarnation/token
  freshness is an additional requirement outside this candidate.

The boundary advances only as the published append policy already disclosed to
the client. It cannot be changed by a completeness frontier, elapsed wall time,
or a background collector. A stuck pin can prevent progress indefinitely;
constant storage is obtained by backpressure, not by invalidating promised work.

## Summary and window observations

A second candidate implements only `summary` and sequential appends, using
cumulative parity plus the *last* accepted `(id,payload)` for exact retry or
conflict checking. Older IDs return `Expired(n-1)` when `n > 0`. Its restart
and acknowledgment rules otherwise match the window service. It exposes no
historical range query. The matching specialization of the window service is
`W = 1`, restricted to these operations; both can share this explicit trace
contract and its client proofs after simulation is established.

For `W > 1`, a parity accumulator without `W` retry payloads cannot share the
window's retry contract. Adding those payloads recovers retry behavior, but also
recovers the information represented by the Boolean window. This example does
not promise a space saving while preserving identical observations.

The window's prefix summary is a useful hybrid: it forgets old payload order
while preserving a chosen cumulative observation. A summary must come with an
update law and a statement of which observations factor through it. Arbitrary
ordered folds do not follow from parity. Likewise, cumulative graph closure can
retain old reachability without old edge records, but it cannot recover record
multiplicity, ordered provenance, or arbitrary prefix views. Adding a cumulative
count also requires bounded arithmetic or an overflow policy. These are separate
client contracts, not optional omissions hidden behind one interface.

The following hypothetical cases specify distinguishing tests:

| Case | Required distinction |
|---|---|
| `W=2`, payloads `[true,false,true]`, `q=1` | `read(1,3)` returns `[false,true]` in order; `read(0,1)` is expired. Cumulative parity is false, whereas suffix parity is true. Dropping the prefix without updating its summary changes the answer. |
| `[true,false]` and `[false,true]` | Equal length and parity, different ordered observations. Summary-only state cannot implement the unrestricted ordered query. |
| Same ID once with `true`, once with `false`, then discard its retry evidence | A later retry with `true` must distinguish acknowledgment from conflict while the ID is admitted. Classifying an unknown old key as fresh would duplicate a prior effect. Expiry must apply to both histories. |
| Publish view at position 1, then commit position 2 | The old tuple remains a valid delayed result, but cannot be labeled position 2 or combined with a new count to claim one snapshot. Crash discards a partial rebuild. |
| Accept graph edge `0→1`, forget its record, then propose `1→0` | A current-window graph might accept; the cumulative acyclicity contract must reject. A preserved cumulative closure can supply the missing evidence. |
| Pin a boundary record while an append would evict it | Append returns `Busy`. After release the append may publish the new boundary; the old query then expires. |
| Acquire, release, then reacquire at the same `n` | The new scoped owner can read and release. A second acquisition while pinned returns `Busy`. A delayed release of the first capability is excluded by the driver ownership predicate; a negative trace must show why recycling a raw token without this premise could release the new pin. |
| Crash immediately before/after publication, then retry; exhaust `K` | Recovery selects old/new coherent state respectively; retry never creates a second commit. Exhaustion never wraps counters or IDs. |

## Publication, reclamation and resource bounds

The proposed concrete target uses two fixed banks, each with `W` record slots
and one descriptor, plus an atomic durable selector. A mutation blocks new pins,
waits for the existing pin to release, and writes the inactive bank. It persists
all new record and descriptor contents before switching the selector. The
selector is the publication/commit point. Only after it is durably switched may
the old bank be erased or reused. Restart ignores the inactive bank, invalidates
volatile handles, reconstructs from the selected bank and restarts an interrupted
copy from scratch. No write after a crash may use a stale pre-crash plan.

This is a proposed capability contract: stable cells, ordered completion of
persistence, atomic durable selector replacement, single writer, fenced readers,
affine within-connection pin ownership, and no corruption or rollback. RCU
documents the separate live-reader problem:
removing references precedes waiting for old readers, which precedes freeing
storage. Its grace-period rule supplies a useful analogy, not a crash-durability
proof ([Linux RCU overview](https://www.kernel.org/doc/html/latest/RCU/whatisRCU.html#rcu-overview)).

Reusing the two bank addresses is incompatible with current `Machine.used`.
The new allocator invariant must prove that no root, cursor, plan or admitted
reader can refer to a bank while it is overwritten. Descriptor position `n`
serves as a nonwrapping generation within the fixed lifetime. It does not
distinguish repeated pin acquisitions at the same `n`; those rely
on the affine driver premise, not a generation comparison. A selector that
only stores the bank bit is sufficient only with the stated persistence ordering
and fencing; it is not a general ABA defense. The existing `KeepsRoot` reasoning
must be extended to reader ownership before any concurrency is permitted.

A proposed accounting target is:

| Resource | Bound and assumptions |
|---|---|
| Durable records | `2W` fixed slots including interrupted copies; no append-only garbage. |
| Durable metadata | Two fixed descriptors and one selector. Descriptors contain bounded counters, parity, validity/shape data; no variable list of historic IDs. |
| Volatile records | At most `W` cached records, `W` staging records, `W` output records and one pending payload: `3W+1` slots. The pinned reader shares the frozen cache; a scan uses an index and Boolean accumulator. No additional copied snapshot or full-history recovery list. |
| Volatile metadata | A fixed number of counters/flags, one delayed tuple and one scoped-owner slot, with no per-acquisition counter. Counters encode `0..K`; addresses encode the finite banks. |
| Output and inputs | One bounded outstanding response and one pending request. The driver backpressures further work. Caller-retained copies and transport queues are outside this service bound and must have their own contracts. |
| Work | Each replacement copies at most `W` records. Retries can scan at most `W`; recovery scans at most `W`. Repeated crashes can cause unbounded total work even though reserved space stays bounded. |

These counts are intended layout invariants, not measurements of Lean's `List`
implementation or a whole-process allocation theorem. Boolean payloads avoid
unbounded payload sizes; finite `K` bounds metadata bit widths. A finite *time*
window would additionally need an event-density/burst bound, bounded timestamps
and bounded batch lengths. Even one timestamp may contain arbitrarily many
events in the existing FRP model. A bounded number of logical entries says
nothing by itself about encoded payload size, outstanding outputs or temporary
copies. Progress requires released pins and a sufficiently long scheduled,
fault-free interval; the service does not promise continued acceptance after
`K` or under a permanently stalled reader.

## Primary-source comparisons

External sources motivate obligations; none certifies the proposed service.
Sources were accessed on 2026-10-29.

- Ongaro and Ousterhout, [*In Search of an Understandable Consensus Algorithm*,
  extended version](https://raft.github.io/raft.pdf), §8: clients use serial
  numbers and servers remember the latest processed serial and response to avoid
  reexecuting retries. This supports separating request evidence from log layout.
  Our payload-conflict rule and expiry policy are additional local requirements;
  we are not adopting Raft or inferring arbitrary retry retention from it.
- [PostgreSQL 15 logical decoding, §49.2.2](https://www.postgresql.org/docs/15/logicaldecoding-explanation.html#LOGICALDECODING-REPLICATION-SLOTS):
  slots retain resources even while clients are disconnected; restart can resend
  changes because the persisted position can lag. This is a concrete example of
  consumer/retry obligations preventing reclamation. Our fixed pin and explicit
  expiry choose a different contract; no PostgreSQL integration is proposed.
- [Linux RCU overview](https://www.kernel.org/doc/html/latest/RCU/whatisRCU.html#rcu-overview):
  reclamation waits until preexisting readers drop references. The proposed
  blocking pin is a small ownership mechanism for that obligation, without
  claiming Linux memory-ordering machinery or its performance.

## Preservation obligations and implementation handoff

| Obligation | Proposed evidence and owner |
|---|---|
| Observation sufficiency | New relation from ghost `H` to `(q,n,L,b)`; prove admitted ordered ranges and cumulative parity agree. Bounded durability implementation under #225. |
| Retry and acknowledgment semantics | Per-step simulation including expiry, conflicts, lost replies and restart. Prove no duplicate commit and retained-interval acknowledgment retrieval, not perpetual retrieval. Same implementation owner. |
| Coherent publication and recovery | Relate every primitive write/persist/switch/crash/recover step to the independent spec; exhibit every cut in a replacement. Same owner. |
| Reader ownership and recycling | Prove pin exclusion, affine ownership preservation, restart handle invalidation, safe bank reuse and constant slot bounds under explicit driver capabilities. Same owner; external fencing is an assumption until realized. |
| Projection consistency | Preserve position-tagged delayed parity and atomic tuple publication; separate stale valid results from current queries. Coordinate #241's established distinctions. |
| FRP query admission | #237 owns timestamp-boundary specialization, pending-request preservation and density assumptions; reuse the observation restriction principle without duplicating its adapter. |
| Shared preservation architecture | #235 owns assessment of whether observation restriction plus state simulation fits existing `Interaction.Refines` composition, where admission/ownership assumptions belong, and recovery of established specializations. Do not require a new universal interface before this experiment. |

The next implementation issue should require all of the following:

1. Add a separate namespace for the fixed `E,W,K` specification above; preserve
   all existing unrestricted APIs. Make ghost history a proof-side reference,
   not runtime storage. Define every rejection and lifecycle transition.
2. Implement the two-bank window realization and summary-only realization.
   Show their shared `W=1`, summary/retry trace specialization and distinguish
   the richer window contract. Include direct typed cells; add encoding only
   if needed for the chosen target, with explicit laws rather than a universal
   serialization requirement.
3. Prove per-step and finite-execution refinement, admitted query order and
   multiplicity, parity preservation, retry safety, crash recovery, pin
   ownership under the explicit affine driver premise, safe address reuse, and
   the stated storage bounds. Relate costs
   to actual modeled transitions. State progress and driver premises separately.
4. Check all distinguishing cases above, including a recovery crash, restart-
   stale handle, release/reacquire at the same position, exclusion of a replayed
   release by the affine ownership predicate, second-pin rejection, rejected
   mutation while pinned, delayed-view minimum position,
   `W=1`, and lifetime exhaustion. Review every new formal statement and run the
   applicable build/proof audit and independent Standards/Spec review.
5. Record the #235 applicability findings and the #237 boundary. Report any
   repeated adapter work, encoding friction or stronger assumptions with their
   mathematical, interface, elaborator or author-capability cause. A current
   author's difficulty alone does not reject an elegant abstraction; retain
   useful specializations and compare refactoring cost as required by the
   [language direction](../language-direction.md#elegance-author-capability-and-language-constraints).

Indefinite bounded service remains an owned question under
[#225](https://github.com/VladimirMarko/conaled/issues/225), coordinated with
[#234](https://github.com/VladimirMarko/conaled/issues/234): it requires an
explicit policy for finite identifier reuse, client/session retirement, reader
fencing and external queues. This experiment must not quietly replace its
finite lifetime with unbounded naturals and call the result bounded memory.
