# Data-structure realizations under target capabilities

Assessment for [#238](https://github.com/VladimirMarko/conaled/issues/238),
2026-10-29. Code baseline: `52751e27aef9c4d4ced7eaf697e2c5d16cc9500e`.

Proceed with a bounded append/query comparison using plain and cached storage.
Keep full ordered sequence observation in the common contract. Separately test
when a summary-only consumer permits eliminating sequence storage. Restrict the
first executable target model to finite payloads and capacity; do not infer an
unbounded implementation from a Lean `List` or `Nat` definition. This note
specifies an experiment, not new checked theorems or runtime measurements.

The objective is compositional realization of specifications where target
capabilities permit it. A book, tree representation, or general induction
framework is useful only when it discharges a demonstrated obligation. The
accepted [source survey](functional-data-structures.md) and
[architecture assessment](data-structure-architecture.md) remain inputs;
this note does not reopen their whole source scope.

## Client and independent contract

The existing client is
[`Sequences.Symmetric.prefixLengths`](../../Applications/Sequences/Symmetric/Observation.lean).
It constructs prefixes and observes their lengths through composed relational
squares. `prefixLengths_correct` and `lengths_inits` identify its output with
`List.range (xs.length + 1)`. Thus its observation can be computed without
materializing the prefixes, provided the input length is available. That is a
concrete elimination opportunity, not evidence that every sequence client can
discard its elements.

The proposed extension is an interactive batch builder with append, summary
query and full sequence query. Its mathematical state is an independently
specified ordered sequence `xs`; append `a` changes it to `xs ++ [a]`, summary
returns `S xs`, and sequence query returns `xs` unchanged. Here `S` is the
ordered monoid fold of `measure : A → M`. This contract preserves order,
duplicates and empty input. The primary finite instance uses `A = Bool`,
`S xs = xs.length`, and at most `N` successful appends. An ordered word summary
is a diagnostic specialization, with its size and computation charged rather
than treated as a constant-size cache.

A pure batch invocation receives all of `xs` as input. An interactive service
receives one command at a time, and a later query has no history argument.
Those are different execution contracts even when both are specified using
finite lists. The interactive contract is the one used in the capability
comparison below. Returning the whole sequence may be a sequential output
stream; a bounded target need not allocate a new host List to emit it, but the
emitted order and termination require a proof.

## Existing code and missing obligations

| Evidence at the baseline | What can be reused | Gap for this experiment |
| --- | --- | --- |
| [#175 survey](functional-data-structures.md), [#176 assessment](data-structure-architecture.md) | Source selection, ordered observation/invariant separation, reachable fusion and explicit cost criteria | Their proposed ordered-summary adapters are not implementation evidence. |
| [`Symmetric.Observation`](../../Applications/Sequences/Symmetric/Observation.lean), [`Prefixes`](../../Applications/Sequences/Symmetric/Prefixes.lean) | `prefixesSquare`, `lengthsSquare`, `prefixLengths_correct`, `scanl_snocSL_refinement` | A new append/query executor and target adapter; prefix elimination must preserve the chosen observation, not claim full prefix values. |
| [#210 implementation](abstract-fifo-client.md), [`AbstractFIFO`](../../Applications/Sequences/AbstractFIFO.lean) | Operation-only `Ops`, separate `Simulation`, `client_eq`, `run_append`, `run_flatMap`; one word client for List and symmetric lists | FIFO commands lack summary and full sequence queries. Reuse its separation and existing squares; do not claim its theorem already covers the new commands. Its optional syntax is not mandatory for ordinary callers. |
| [#211 implementation](modular-fifo-costs.md), [`FIFOContracts`](../../Applications/Resources/FIFOContracts.lean) | `Instrumentation.erases`, public `client_bound`, `sequential_bound`, `reobserved_bound`, existing actual list/symmetric instrumentation | Only enqueue/delete costs are charged; head observation is explicitly uncharged. It supplies neither summary-query costs nor physical storage guarantees. Branching cannot reuse initialization credit twice. |
| [`Resources.Workload`](../../Applications/Resources/Workload.lean), [`ListFusion`](../../SquareKit/ListFusion.lean) | `run_value_fusion`, `run_invariant`, `run_append`, `reweight_run`, `scanl_reachable` | Local operation simulation, measurement erasure and capacity preservation still need proofs. Peak live storage is not automatically an additive observation. |
| [`Optimization.Basic`](../../Applications/Optimization/Basic.lean), [`Transport`](../../Applications/Optimization/Transport.lean) | Admissible candidates, Pareto comparison, workload pullback and minimizer transport | Need target eligibility and common objective; value equality alone does not transport costs or candidate coverage. No executable global optimizer follows. |
| [`Dijkstra.Store`](../../Applications/Dijkstra/Store.lean) | Vector-backed `lookup_write` and ordered `accum_lookup`; indexed update precedent | A capacity-checked append buffer, finite element encoding, allocation-free backend and physical cost model are not supplied by the Vector laws. |
| [#185](https://github.com/VladimirMarko/conaled/issues/185), still open in the inspected issue snapshot | Owns List/DList ordered-summary and cache semantics, connected clients, Set/presheaf reassociation | Do not duplicate that implementation or report it complete. Its word-valued diagnostic cache has no constant-space claim. The resource/capability extension must consume its accepted laws or explicitly stage that dependency. |

The #175 survey's statement that measured random-access work remained archived
is dated: #176 already records the later #181 integration. Likewise the final
future-tense paragraph of the #210 note is superseded by the implemented #211
note and declarations. Findings here follow current code, not those older
planning paragraphs.

## Capability and contract matrix

Rows are proposed target models, not claims about any particular device.
All require deterministic command interpretation and reliable observation while
running. A mathematical monoid supplies equations; it does not supply a physical
representation, primitive latency, unbounded words or crash survival.

| Target | Construction and operations actually required | Common contract and limitations | Local proof obligations |
| --- | --- | --- | --- |
| Manageable growing memory | Plain sequence or sequence plus cache; allocate element storage, read it in order, append/link or copy, store/read summary. Reclaim unreachable storage if a bounded-live-space claim needs it. | Full contract for finite histories within available resources. No finite device is asserted to admit arbitrary history length. | Decode/append and cache laws; allocation failure policy or admitted capacity; bounds for traversal, maintenance and reclamation. Sharing is optional, not assumed. |
| Fixed-capacity retained state, no allocation | `N` slots for finite payloads, bounded length, indexed slot write, ordered slot read, optional bounded cache. No pointer identity, element equality or heap allocator needed. | Same full contract on histories whose every prefix has length at most `N`. A total overflow-rejecting operation is a separately stated API; it must leave state unchanged and report failure. | Bounds-safe write/read, initialized-prefix invariant, exact capacity check and output order. A symbolic `Vector N Bool` is only the semantic adapter until its implementation is related to this machine model. |
| No state between calls, no external retained witness | Current command alone; combinational/local temporary computation permitted. | Cannot implement the interactive full contract, even for capacity one. A pure bounded batch function can be realized if all required input arrives in the same call and output capabilities suffice. | Impossibility below; batch specialization must explicitly change the calling contract, not claim state elimination for the service. |
| Summary-only observer with retained bounded state | Store one length in `0..N`; increment with checked bound, read summary. | Supports length queries on admitted histories; does not support full sequence query. For arbitrary monoids, summary storage itself may grow without bound. | Fusion/observation factorization and count bounds; caller must not observe discarded elements. |

No equality on payloads is needed for append or fold. Equality or lookup becomes
necessary if a later durability service deduplicates request identifiers; that
is an additional operation contract. Nor do append-only clients require
branching versions. Immutable host values allowing old references do not by
themselves provide a physical sharing or retention bound.

Changing from heap storage to slots changes execution capabilities within the
same ordinary mathematical model. #185's nonconstant presheaf example changes
the mathematical setting and interprets one relational reassociation argument.
Neither change establishes the other: this matrix supplies no interpretation of
Lean induction in an arbitrary setting.

## Construction, replacement and composition

For a representation `R`, let `D : R → List A` and `Inv : R → Prop` be its
observation and validity. The proposed cached representation `(r,m)` satisfies
`Inv r ∧ m = S (D r)`. Cache construction traverses existing data once; append
updates `r` and multiplies `m` by `measure a`. The proof uses the actual append
law `D (append r a) = D r ++ [a]` and the summary homomorphism law. Erasing the
cache preserves full sequence meaning. Replacing a plain buffer with its cached
counterpart preserves every append, summary and sequence observation on admitted
traces. Conversion work and temporary overlap of old/new storage are charged.
These are intended theorem statements; #185 owns the ordinary summary laws.

Connect the builder to the existing prefix-length consumer. After construction,
the existing square observes `xs.inits.map List.length`; the alternative emits
`List.range (S xs + 1)` when `S` is length. `lengths_inits` is the connecting
law. Relational composition reuses the representation proof; reachable fold or
scan fusion reuses the induction over updates. Producing `n+1` output lengths
still incurs output work. The experiment must distinguish a scalar final count,
a streamed prefix-length sequence, and materialized full prefixes.

Ordinary callers should write commands and use a theorem over their supplied
operations, relation and local preservation evidence. They should not construct
internal syntax or mention a backing array's indices in the client proof.
Representation authors discharge slot bounds, decode laws and cache validity.
Adding a shared public structure is justified only if both adapters remove the
same repeated caller obligations; existing `RelSquare` and `run_value_fusion`
may suffice.

The exact-to-summary step is lossy: `[false]` and `[true]` both have length one
but different sequence observations. Thus a client allowed to request full
history cannot replace a sequence by its length. This is the negative
composition case. #235 owns any proposed shared interface that incorrectly
requires reflection through this summary map, or forces all observations into
one equality. Keep forward preservation and reflection separate using existing
relations; no new universal preservation interface is proposed here.

## Missing-capability arguments

For the stateless interactive target, compare histories `append false` and
`append true`, then issue the same sequence query. Without retained state or an
external history/witness, the target has identical input and internal state at
that query. Determinism forces the same output, but the contract requires
`[false]` and `[true]`. Even capacity one is impossible. The count-only service
also fails without state: compare zero and one append followed by the same
count query. An external store or a history carried in each request changes
the capability contract and must be counted, not renamed stateless execution.

More generally, a machine with `K` reachable retained configurations cannot
represent every Boolean sequence at a fixed length `n` with `2^n > K` and
answer full sequence queries exactly: two histories reach the same configuration.
This is a finite-state counting argument for the specified service, not a claim
that every useful program needs general memory. Bounded history, externally
supplied input, or a smaller observation quotient can make a different contract
realizable. Proposed checked cases should include `N=0`, exact capacity,
overflow, duplicate values, and the indistinguishable histories above.

## Resource comparison and durability handoff

Coordinate the experiment with #177's resource assessment. For a history with
`n` admitted appends and `q` summary queries, record the current length `n_j` at
each query. Plain storage computes the summary by visiting `n_j` elements;
cached storage reads a summary but pays for its update on every append and for
any initial conversion. Both retain the elements for full sequence queries.
For length on the bounded target the extra cache is a bounded counter; if the
buffer already needs a length field, reuse it rather than charge a fictitious
second copy. That special case may make the uncached length baseline artificial:
the meaningful generic comparison uses an independently maintained summary,
while length remains the capability and prefix-composition test.

Use exact counters for element visits, summary operations, reads/writes and
conversion; then explicit nonnegative tariffs. State live storage and maximum
capacity separately, with sequential composition through actual intermediate
states. Query-heavy and update-heavy traces can prefer different realizations;
zero queries need not justify cache maintenance. Ordered word summaries may
cost linear space and nonconstant concatenation. Neither DList function
composition nor List equations prove allocation-free or constant-time execution.
No machine timing or compiler correspondence has been measured here.

#226/#227 extend this client toward ordered accepted histories of
`(session,id,payload)` with append-if-fresh and summary queries. They must add
identifier equality/deduplication and decide which history observations survive
failure. Retained process state, accessible old immutable versions and durable
state are separate capabilities. A cache-validity proof alone establishes none
of recovery, atomic publication or flush ordering. A candidate durable target
can use immutable committed cells and an atomic root, with referenced cells
persisted before the root is installed; those are explicit target assumptions
for #226, not consequences of serialization. Checkpoints must retain full
history when the public contract exposes it. A scalar checkpoint cannot recover
an ordered-history query. Serialization is one possible representation adapter
where a byte-oriented storage boundary requires it.

## Exact source choice: induction versus this experiment

Ghani, Johann and Fumex, [*Generic Fibrational Induction* (2012)][johann],
Theorem 4.11, gives sound induction for an inductive functor with a
truth-preserving lifting in a comprehension category with unit. Definition 4.7
requires a right adjoint to the truth functor; §4.3 constructs liftings under
additional structure, including left adjoints to reindexing. This concerns
which induction arguments a setting validates, not memory management or latency.

Our assessment: it is a candidate method for the missing recursive-proof
interpretation identified by #176. A local application would first exhibit the
base/total categories, truth/comprehension structure, initial algebra and
lifting, then connect the resulting rule to an actual consumer. For this
finite append/query experiment, existing Lean list induction and reachable
fusion already discharge that obligation. Defer a fibrational formalization
until a second mathematical setting or datatype needs it; do not make it a
prerequisite for bounded buffers. This decision assesses one precise paper,
not Johann's whole body of work. No new assumption that all target settings
have initial algebras follows.

The [#175 survey](functional-data-structures.md#sources-and-techniques) already
assigns Okasaki's thesis to persistent representation design, Nipkow's text to
explicit running-time functions, and Appel's ADT development to representation
invariants. Those remain useful sources when their assumptions match the
selected obligations. The present experiment needs no whole-book port and no
new claim about their full coverage.

## Bounded next scope

Proceed with one implementation issue coordinated with #177: compare plain and
cached append/query realizations under an explicit fixed-capacity contract,
connect prefix-length elimination, and prove the stateless impossibility
boundary. Stage it after the relevant #185 ordinary semantic laws, without
waiting for #185's entire setting-interpretation deliverable if the semantic
portion is accepted separately. Reuse #177's exact resource model and avoid a
second competing workload experiment.

Acceptance must name the executable operations and two actual representations;
prove capacity/invariant preservation, full observation refinement, measured
erasure and workload cost equations; test full versus summary-only observation
and the no-state negative case; expose ordinary clients; and complete statement
review, checked applications, applicable build/audit and independent reviews.
Start with a finite summary distinct from the buffer's mandatory length field
(such as Boolean parity), alongside length and an order-sensitive semantic
case. General monoid laws can be reused without claiming every monoid is a
bounded machine value. The issue must explicitly charge summary evaluation,
construction, conversion, output and maintenance, or mark an excluded operation
outside the compared workload.

Remaining scope: physical backend correspondence, arbitrary branching retention,
reclamation/ownership, crash recovery, general recursive interpretation,
unbounded or nested structures, search/splitting and finger-tree fit. #177 owns
resource methodology, #185 ordered-summary semantics, #178 the finger-tree
assessment, #226/#227 durability, and #235 preservation-family mismatches.
This recommendation supplies a bounded capability experiment; it does not close
those broader scopes or claim global optimality.

[johann]: https://arxiv.org/pdf/1206.0357
