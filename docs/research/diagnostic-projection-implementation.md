# Versioned diagnostic projections over accepted history

Implementation of [#241](https://github.com/VladimirMarko/conaled/issues/241),
extending the accepted [recovery implementation](accepted-history-implementation.md)
under the [diagnostic specialization](persistence-diagnostic-specialization.md).
The storage protocol, representation relation, codec simulation and client
refinement are reused. No new persistence framework or database engine is added.

## Graph specification and admission

[DiagnosticGraph](../../Applications/Durability/DiagnosticGraph.lean) uses
vertices `Fin N`, ordered accepted records, and a separate set-valued edge
relation. `Reach` is the independent nonempty transitive closure `TransGen`.
`closure` computes the intersection of all finite transitive supersets of the
edge relation. `closure_correct` proves agreement with `Reach`: transitive
closure itself supplies one such superset, and induction on paths establishes
membership in every such superset. This finite exhaustive algorithm terminates
without a path-enumeration bound. It is deliberately expensive; no efficient
closure or incremental-maintenance claim follows.

`admit` recomputes acyclicity of the proposed appended history. This is stronger
work than an optimized back-edge lookup, but `admit_no_cycle` proves that an
accepted edge is neither a self-edge nor the reverse of an existing path.
`AdmittedStep` wraps the existing protocol and checks this guard at commit
against its authoritative ready cache. It leaves request identity, freshness,
ordered history, exact retry, conflicting reuse, publication and acknowledgment
rules in the underlying protocol. It does not check a delayed view and later
commit without revalidation. The model retains one writer.
`AdmissionStep.cycle` returns an explicit rejection for a fresh cyclic proposal
before invocation and leaves the ready machine unchanged. Existing request
identities remain subject to the protocol's retry/conflict rules.

`admitted_step_safe` and `admitted_script_safe` lift local graph safety through
the existing source simulation. `admit_execution` connects concrete storage
traces to the adapter when their constructed final graph is acyclic. Its final
acyclicity premise is proof evidence for those examples, not a runtime oracle:
the actual transition guard still recomputes from the current cache.

The checked application accepts two distinct request identities proposing the
same edge. Both records remain in history while edge membership deduplicates
them. A stale empty view would approve the reverse edge; the current-history
adapter rejects it. Exact retry and conflicting reuse retain the original
protocol behavior. A separate three-vertex example proves a two-edge path
through `closure_correct` and the independent path constructors.

## Publication and synchronous snapshots

[DiagnosticProjection](../../Applications/Durability/DiagnosticProjection.lean)
defines one observer-parameterized projector. A published result contains its
position and value. `Agrees` identifies an actual prefix of the authoritative
history; `agrees_exact` derives the required `view = observe (take position H)`
and the position bound. Equal lengths of unrelated histories are never used
as evidence of snapshot identity. This experiment has one fixed generation and
schema and never truncates history.

A rebuild pins a ready history, advances separate seen/todo lists, then
recomputes the observer and atomically installs its position/value tuple.
`ProjectionInv` connects both the published result and the unfinished rebuild
to prefixes of the source history. `projection_preserves` covers storage
steps, concurrent-in-the-model append progress by the sole writer, rebuild
scanning, publication and crash. Append-only growth preserves pinned prefixes.
This is interleaving of modeled steps, not a multithreaded reader-lifetime proof.

The projector is disposable volatile state. Crashes discard its published
view and unfinished rebuild, while the underlying storage retains its root and
cells. Both crashes immediately before publication and immediately afterward
therefore make the diagnostic unavailable until rebuilt. The retained example
performs a rebuild scan, crashes, reads the retained record through the actual
recovery protocol, and restarts. Its allowed cycle can repeat. No finite lag or
response deadline is promised. Persisting a projection would require another
storage realization with tuple/version atomicity; it is not silently assumed.

`synchronous` derives all fields from one ready cache in one sequential query.
`synchronous_correct` identifies that cache with the authoritative source
history. `synchronous_ack_fresh` proves that a completed query after an
acknowledgment cannot select an earlier position and retains the acknowledged
record. A delayed result at position zero can remain valid while the current
snapshot is at position one; its freshness label does not authorize admission.

`projection_client` transports one ordinary client through the existing
`history_refinement`. `encoded_projection_client` transports that same result
through `encoding_refinement`. [DiagnosticProjection examples](../../Examples/DiagnosticProjection.lean)
construct a log and a full checkpoint with a later independent tail, crash and
recover each, and realize both traces through the encoded primitive protocol.
The same position/count/path client covers all four combinations. Concrete
traces establish the client premises; the theorem is not justified only by
uninhabited representation assumptions. The existing acknowledgment client is
also applied to the graph's typed and encoded recovered histories.

`recompute` returns accepted-record count and reachability. Replaying a record
twice leaves the set-valued closure unchanged but increases count, exposing the
non-idempotent error. Equal-count singleton histories with opposite edges have
different reachability. A graph/metadata pair collected from two different
points in a three-snapshot history never coexisted, matching the existing
`Interaction.Snapshot` counterexample. Pinning one history avoids that mixture.

## Relational and encoded interpretation

[DiagnosticRelational](../../Applications/Durability/DiagnosticRelational.lean)
defines `Accepted` by record position and a distinct existential edge view.
`relational_edges` proves its set interpretation equals the graph specification;
`relational_reach` connects relational closure to the diagnostic. `ordered_rows`
reconstructs the original list from position-indexed rows. Unspecified table
iteration is not treated as history order, and duplicate-edge requests remain
distinct accepted rows.

`edgeCodec` encodes cell tags, record/session identifiers, finite endpoints,
links and length-framed descriptors as lists of natural words. Its decoder
checks endpoint bounds and exact framing. Round trips are proved for every
cell constructor and malformed endpoints reject. This specializes #240's
optional codec interface, with its primitive simulation and realizability
theorems. Typed storage needs no codec premise. Natural words and addresses
remain unbounded; this is not a byte codec or finite-sector capacity theorem.

## Structural storage counts

[DiagnosticStorage](../../Applications/Durability/DiagnosticStorage.lean) attaches
read counts to actual node/flat/boundary/finish constructors. Its soundness
maps these traversals to the existing `Read` relation and machine transitions.
`chain_read_count` derives one record read and link follow per log record;
`checkpoint_read_count` derives one read per prefix record and one read/link
pair per tail record. The descriptor/root read has its own storage annotation.

The list-driven persistence loop performs a buffered write and per-cell
persistence for every cell. `PersistenceTrace` ties each list entry to those
exact `StorageStep` transitions; its erasure uses their existing soundness.
`replacement_execution` proves preparation, all cell operations and root
publication. `BatchComplete` is a separate logical observation requiring all
plan writes to be retained. It does not assert one physical flush. An
interrupted prefix lacking its descriptor cannot complete the batch.

The [storage examples](../../Examples/DiagnosticStorage.lean) construct all ten
original appends from empty storage. The checkpoint copies eight flat records,
two relinked tail records and a descriptor into eleven fresh cells. The tail
ends at the new split, with no reference into the old log. Publication follows
all eleven actual write/persist pairs. `current_needs` proves that every current
pointer is outside the old allocation; `reclaim_execution` then performs ten
actual reclamation transitions. The old and new allocations are disjoint,
with ten and eleven cells and a union of twenty-one cells.

`connected_checkpoint_cost` sums the witnessed ten-record traversal, eleven
write/persist pairs, root installation and ten reclamations.
`connected_recovery_cost` sums the concrete descriptor read and the eight/two
split traversal. The generic split equation covers any `k ≤ n`. Primitive
weights stay separate, including cell persistence in addition to batch
completion. To reproduce #227's declared count model, `assessmentTariff` gives
cell persistence weight zero and logical batch completion weight one; the
other listed structural primitives have weight one. Root reads, crashes and
volatile control are outside that structural objective. This is an explicit
projection of counts, not a claim that omitted operations are free physically.

The checked totals are 50 versus 86 for one final recovery and 170 versus 164
for seven. `zero_link_no_payoff` proves that copying cannot beat the log under
zero link-follow weight. `common_work` permits cancellation of admission,
view-rebuild and query work only when the same chosen algorithms supply those
costs. No linear bound on graph recomputation is claimed. Queries here operate
on the same recovered in-memory view; persistent-storage query algorithms would
need their own read counts.

The two-cell interrupted copy retains the old complete history and incurs its
actual write/persist charges without a completion charge. Repeated interrupted
read prefixes add their own charges, with no bound determined by the number
of completed recoveries alone. Prior incomplete allocations remain garbage
until explicitly reclaimed; `retainedAfterCopy` includes them. The twenty-one
cell one-copy peak excludes volatile staging and common root storage, and
cannot be reused unchanged for repeated abandoned copies. These are modeled
cell counts, not allocator or physical-space claims.

## Statement review and remaining boundaries

The initial worked cases required a transitive path, rejection of a reverse
edge after its forward edge committed, distinct counts for duplicate replay,
and the checkpoint arithmetic above. Missing connections were finite closure
to `TransGen`, projection tuples to exact history prefixes, and counts to
read/write/reclamation transitions. The retained proofs supply those connections
without an incremental-closure assumption or an assumed history-preservation
postcondition on storage writes.

Statement review covered all new claims: finite domains and decoder bounds;
nonempty rather than reflexive reachability; source/target simulation direction;
current-cache admission; inhabited log/checkpoint and encoded traces; old/new
cursor and publication states; exact prefix identity; acknowledgment freshness;
ordered rows versus set edges; actual copied/reclaimed addresses; independent
primitive tariffs; and separate retained/transient storage. Examples preserve
their expected values through the public lemmas. No `sorry`, new axiom or
unchecked numerical evaluator is used for acceptance.

The public entrypoint imports both example modules through the storage example.
Acceptance uses README's candidate build and exhaustive proof audit, with exact
candidate receipts and independent reviews retained by the orchestration record.
There is no SQL adapter, concurrent admission, schema migration, production
rollout, incremental closure, physical flush theorem or measured speed claim.
#225 owns the broader durability program, #177/#238 the general target/resource
work, and #235 the wider preservation-interface program.
