# VFA, FDSA and PFDS integration

This integration receives the three textbook developments into the existing
`conaled` library and connects selected results through its shared contracts.
Library coherence takes priority; useful mathematics, including unfinished
proofs and counterexamples, keeps an explicit disposition. Receiving a source
branch or proving a shared client does not establish whole-book acceptance.

The [repository preservation record](../history/textbooks/README.md) owns the
already received historical material. Current paper mathematics belongs in
normal research owners; [CTB](../textbooks/README.md) owns the authorized
continuation and its [inbox](../textbooks/inbox/README.md) identifies unprocessed work.
[Issue #558](https://github.com/VladimirMarko/conaled/issues/558) owns current
coverage and follow-up, with concrete interface tasks #559 through #564. The
historical checkpoint-local INT issues remain provenance. This note owns the
source and interface correspondence; current acceptance uses the receiving
repository's build and independent review procedure.

## Presentation review at acceptance

For each incoming CTB receiving slice, apply the
[complementary-presentation and recovery criteria](../language-direction.md#complementary-presentations-and-reconstruction)
alongside the existing preservation, build/audit and independent-review gates.
Compare the supplied definitions and axioms with current shared interfaces and
checked clients. Record which source capabilities are retained, which maps or
reconstruction theorems justify reuse, and which observations or assumptions
prevent equivalence. Preserve computational and cost contracts separately from
extensional mathematical agreement.

Give each assessed overlap a disposition: integrate through a checked shared
construction, retain a connected alternative presentation, or preserve the
source mathematics with a scoped follow-up for the missing connection. State
why a connection is inapplicable when that is the finding. Recover established
clients under their original contracts when changing interfaces; importing a
theorem or wrapping an assumed comparison alone does not establish recovery.
Record the assessment and evidence in the receiving slice's acceptance record
and reconcile its residual owners in [#558](https://github.com/VladimirMarko/conaled/issues/558).
This review does not require unrelated library redesign or whole-book completion
before accepting a bounded slice.

Use the [interface-search inventory](reconstructible-presentations-search.md)
from [#634](https://github.com/VladimirMarko/conaled/issues/634) when comparing
receiving interfaces. Feed newly discovered opportunities to
[#235](https://github.com/VladimirMarko/conaled/issues/235) and the experience
of applying these criteria to
[#636](https://github.com/VladimirMarko/conaled/issues/636). The latter should
identify a concrete receiving slice as evidence rather than wait for the entire
continuing CTB workstream.

## Current CTB continuation: accepted receiving integration

The integration baseline is
`8ff71395e9841760c4e240c4e8b8741b355bda68`; the saved donor is
`1f6ee5dd25ba633deb807b8d2240bec5e5cf96af`, with common prerequisite
`c796ab0bf270bdf76ea4e980d1d606d8b6a9286e`. The receiving slice is published: R2
`99a2974c93e556088af814f033540eb36ba2d3a6` passed the clean whole-library build,
exhaustive audit, applicable executable checks and both independent review axes.
`3ac996cc42ec4a57bb5c7052714052cca87c97ff` records that acceptance in the
[CTB evidence index](../textbooks/CTB.json). The
[build run](https://github.com/VladimirMarko/conaled/actions/runs/44670389911)
checked 3,922 modules and verified the exact R2 receipt; the
[runtime run](https://github.com/VladimirMarko/conaled/actions/runs/44700642536)
retains the separate extraction observations. The later documentation commit
claims no new execution. Historical donor checks retain their original scope.

The user-authorized [CTB continuation](../textbooks/CTB.json) preserves CTB-79
through CTB-122 and their complete requirements. Earlier CTB identities retain
their existing canonical owners; no new numbering series is introduced.
**CTB-78 receiving integration and checkpoint074 retention/save are complete.**
The later CTB-24 slice was accepted at
`a5ce55a05aca5c0738cd1877841b906ce9b4e547` under
[#659](https://github.com/VladimirMarko/conaled/issues/659), preserving donor
`cfa205a4e08d38c8e75048213126decad5d31f1c` in its ancestry. C05-085 is qualified;
C05-090 remains partial. Its full build/audit, final verification and independent
Standards/Spec reviews passed. This is source acceptance, not certification of
a final checkpoint075 archive. The 20 November instructions allow continued
local authoring and distinct checkpoint deliveries alongside receiving work,
and supersede older perpetual-retention, Page-only and 32 MiB process
requirements. Dated ticket text does not reinstate them. The R2 inventory below
retains its original receiving scope.

The donor contributes 261 selected paths: 159 production Lean files, 70 clients,
28 research notes, the public aggregate, one Lake executable declaration and
two runtime files. Only `SquareApplications.lean` is changed on both sides;
retain all 20 upstream and 70 donor import additions. Toolchain, Mathlib and Nix
lock inputs are unchanged. The 229 changed production/client modules have a
320-module project dependency closure disjoint from upstream's changed Lean
modules, excluding the aggregate. This static result does not discharge the
combined receiving build or the separately built executable.

| Slice | Existing construction and retained observations | Receiving disposition |
|---|---|---|
| Sorting, CTB-79/82 | `Sorting.Specification` connects indexed, bounded-indexed and pairwise observations without order laws; adjacent order needs transitivity. `Sequences.Multiplicity` and `Sorting.Multiplicity` connect lawful counts to permutation and existing uniqueness. | The #560 bridge is implemented, including the public FDSA sorter consumer and separating controls; retain direct indexed proofs, stability distinctions and separate costs. |
| Ordered sets and cached trees | `AbstractSet.Refinement` derives laws and mixed-history transport from primitive operational equations and auxiliary validity. Height-balance/AVL clients reuse this construction; interval updates reuse ordered-tree/list proofs through cache erasure. | Preserve cache, ordering and balance hypotheses. Reconcile #588 against these concrete capabilities without inferring closure of all map or graph follow-ups. |
| Maps and decoded keys | Existing map/table contracts, tree folds and ordered enumeration connect raw lookup, valid structural meaning and sorted entries. | Keep absence distinct from a stored default and preserve malformed-tree controls. Map deletion alone does not establish every #587 `Modify` round trip. |
| Queues and graphs | Binomial queues reuse `ExactQueue` on valid states with occurrences and native meld. Finite coloring supplies Mathlib `SimpleGraph.Coloring` while retaining the stored vertex domain. | Retain the native execution contracts. The graph adapter does not settle #589's arbitrary valid-graph composition requirement. |
| Resources | Actual measured source recurrences reuse `Measured`, `Workload`, `Potential` and binary-counter laws. The measured right fold recovers the shared runner on reversed inputs and the earlier tariff. | Preserve execution order, state trajectories and cost observations independently of extensional semantics. |

Two bounded reuse repairs are included. `Search.OrderedTree.contains_iff_mem_setTree`
again composes `contains_iff_mem_entries` and `Trees.mem_inorder_iff_mem_setTree`,
preserving its original statement and assumptions. Ordered-map enumeration now
exposes `kvsInsert_split_of_left`, whose right suffix is arbitrary: the proof
requires only the left separator. The original `kvsInsert_split` signature is
retained as a wrapper, and enumeration correctness uses the weaker public law.
The connected SearchTrees cases exercise an arbitrary suffix, a concrete
unsorted suffix with duplicate keys, and the failure when the left separator is
dropped. The recovered Chapter 6 observation has this shared interface owner;
its full source exercise remains open.

The accepted receiving checks cover these clients, the generalized set/map
universes, weaker raw map comparisons and extracted `Search.SharedTree.Branch`
declaration. No computation or source qualification changes merely from exposing
the weaker map theorem.

The new upstream classification/descent, Lawvere, matroid and rational-kernel
work supplies no demonstrated direct replacement for this slice. Rational-kernel
recovery may help later probabilistic work, but forgets random tapes, paths and
costs. No blanket migration is proposed without a concrete preserved contract.

The R2 slice left Chapter 5 at 90/94. After the separate C05-085 acceptance,
published coverage is 91/94 with C05-090/092/093 open; Chapter 9 remains 57/110.
Remaining book requirements stay in CTB and the canonical coverage ledgers.
Completed mathematics and source correspondence belong in normal repository
owners. The [unprocessed inbox](../textbooks/inbox/README.md) retains unfinished
preparations. Checkpoint074's later retention and durable-save closure is recorded
in the [current continuation](../textbooks/README.md#retention-and-inbox); it is
separate from the later C05-085 acceptance. These accepted slices supply evidence for
[#636](https://github.com/VladimirMarko/conaled/issues/636). Its comparative
synthesis and guidance reassessment remain open.

## Tree, cache and resource integration assessment

This bounded first pass for [#658](https://github.com/VladimirMarko/conaled/issues/658)
inspected source and existing public clients at
`a5ce55a05aca5c0738cd1877841b906ce9b4e547` on 21 November 2026. It follows the
actual definitions, premises and selected client derivations below; it is not
an exhaustive statement review of every imported theorem or a new book-source
comparison. No Lean code changed. The accepted build/audit at that source commit
covers these retained declarations. Documentation validation checks the new
assessment and its links; it does not claim a fresh execution or usability trial.
Other #658 families remain outside this pass.

### Shared constructions and retained clients

**Complete caches and height-balanced sets.**
[Cached](../../Applications/Trees/Cached.lean) already separates `read`,
`smartNode`, `Valid`, `erase` and `annotate`. `read_eq_fold` derives the cached
observation from an independent fold under recursive validity;
`erase_annotate` recovers the whole unannotated tree. A root equation alone does
not establish descendant validity. These contracts need no equality decision,
order or inhabitant for the label type. They do not identify an arbitrary
malformed annotated tree with its reconstruction.

[HeightAnnotation](../../Applications/Trees/HeightBalance/Basic.lean) adds only
an empty summary, combining operation, height projection and its two algebra
laws. Its `height_fold` uses the existing `Trees.fold_fusion`; balance is a
separate predicate on actual shape. The
[set refinement](../../Applications/Trees/HeightBalance/SetRefinement.lean)
supplies primitive operational equations and auxiliary closure to
[AbstractSet.Refinement](../../Applications/Search/AbstractSet/Refinement.lean),
which derives set laws and mixed-history transport. `setLaws` changes the
observer through `mem_inorder_iff_mem_setTree`; it does not repeat the update
induction. `member_inorder` needs a linear key order and strict inorder but no
cache or balance premise. Full update closure additionally needs `1 ≤ d` and
complete `ValidD`. Annotation and key universes remain independent.

The [height-set clients](../../Examples/HeightSetRefinement.lean)
`ordinary_history_contract`, `generic_history_contract` and
`independent_representations` consume these public results for arbitrary valid
initial states and mixed words. Different positive tolerances and annotation
carriers preserve inorder/query observations without recovering equal concrete
states. [HeightRebalance](../../Examples/HeightRebalance.lean) supplies maximum
and word summaries through `maximum_fold_fusion` and `word_fold_fusion`;
`word_reader_eq_inorder` consumes cache validity rather than assuming its final
comparison. Its `plain_mirror_keeps_the_wrong_word` and
`mirror_derived_right_is_wrong` reject transporting a noncommutative word cache
by plain mirroring. Retain the complete-annotation construction and these
specializations. Equal projected heights cannot replace their full invariants.

**Balanced intervals and a geometric consumer.**
[Balanced intervals](../../Applications/Search/IntervalTree/Balanced.lean)
specialize that same algebra to height/maximum pairs and reuse the actual
local updates at tolerance one. `maximumTree` is a proof projection;
`search_eq` connects a direct one-branch query to the existing maximum-only
query even on malformed trees. It does not execute that projection or assert
that updates commute with it: the older interval tree uses successor deletion,
whereas the selected balanced implementation uses a predecessor.

`search_sound` requires no validity premise. Completeness in `search_correct`
requires valid maxima and weak low-endpoint order, without height validity or
strict key order. Full `intervalSetLaws` uses linear keys, linear endpoints with
bottom, complete validity and the explicit compatibility
`a < b → (iv a).low ≤ (iv b).low`. The interval map need not be injective.
[BalancedIntervalTrees](../../Examples/BalancedIntervalTrees.lean) connects
`weak_query_contracts`, `indexed_delete_preserves_other_occurrence` and the
closed-boundary/duplicate rectangle cases to these laws. Its stale-cache and
reverse-projection false negatives show why valid heights alone and arbitrary
key-to-interval maps do not suffice.

[The balanced sweep](../../Applications/Search/RectangleSweep/Balanced.lean)
passes the derived interval-set laws directly to the existing
`sweep_eq_true_iff_hasIntersection`. This is a checked ordinary client of the
shared abstraction; it requires no compiler wrapper or repeated geometry proof.
The distinct occurrence IDs survive in complete keys even when interval images
agree. Retain the maximum-only and balanced implementations as connected
alternatives with their own shapes and execution contracts. C05-085 is complete;
no operation-cost equality or whole-pipeline complexity follows.

**Older shape and traversal clients.**
[Rotation bounds](../../Applications/Trees/Rotations/Bounds.lean)
`connect_equal_inorder` recovers an actual target tree by a right-rotation
schedule followed by a reversed left schedule, given equal inorders. The raw
contracts have no ordering hypothesis and retain duplicate labels. The
[rotation clients](../../Examples/TreeRotations.lean)
`inorder_does_not_determine_raw_shape`, `set_does_not_determine_multiplicity`
and `three_connection_is_not_shortest` separate semantic preservation, exact
recovery using a retained target/schedule, and optimality. Do not infer a
canonical inverse of inorder or a shortest mixed route.

[TreeBalanceSearch](../../Examples/TreeBalanceSearch.lean) already composes
`rebalanceSquare` with the existing insertion square and membership law.
`member_insert_rebalance` needs a linear order and a valid starting BST;
`ordered_balanceTree_iff` needs only a preorder. The underlying prefix balancer
remains order-free and retains the unconsumed suffix.
[TreeBalancePipeline](../../Examples/TreeBalancePipeline.lean) binds actual
literal, direct-suffix and staged traversal outputs into that balancer.
`same_result` includes failure, while its cost formulas retain the successful
request premise `n ≤ t.numNodes`. `nil_staged_not_le_literal`,
`failed_nil_executions` and `empty_payload` keep empty inputs, failure and empty
label carriers visible. Retain the alternatives: direct invocation has the
smallest declared count for this already-available suffix function; staged
execution separately pays construction. This supports that bounded modeled
representation decision, not a claim about physical sharing or wall-clock speed.

**Resource interpretations.**
[TreeCache.nodeRun](../../Applications/Resources/TreeCache.lean) binds both
root reads and the callback's returned summary. Its value theorem needs only
the callback equation at the reached arguments; its cost theorem is independent
of that equation and child validity. [TextbookTreeTariffs](../../Examples/TextbookTreeTariffs.lean)
reuses it for size and height, with two declared primitive charges and total
cost five. [TreeCache](../../Examples/TreeCache.lean) instead passes actual
measured append: `chain_node_cost` is `n + 4`, and `chain_node_exceeds` rules out
a uniform constant even on valid prepared children. A complete summary algebra
therefore cannot promise constant-time combination without a separate tariff.

The [measured scan](../../Applications/Search/RectangleSweep/Measured.lean)
uses `Resources.bind`, with callbacks supplying the next actual state. Its
value erasure needs only `Zero`/`Add`; additive reweighting requires additive
monoids and a homomorphism, not commutativity. The
[scan clients](../../Examples/MeasuredRectangleSweep.lean)
`sentinel_update_order`, `sentinel_query_before_insert` and
`sentinel_ordered_observation` exercise state dependence and noncommuting token
observations. A hit skips insertion and the suffix; only exhaustion pays the
terminal charge. Replacing this executor with an unconditional whole-list fold
would change the contract.

[MeasuredEvents](../../Applications/Search/RectangleSweep/MeasuredEvents.lean)
reuses `ListIndex.run`, `ListCalls.mapRun` and `ListReversal.appendRun`, binding
one indexed list into both event maps before sorting and scanning. The
[generation clients](../../Examples/MeasuredRectangleEvents.lean)
`generate_ids`, `id_priced_triple`, `forged_constructor_not_erasing` and
`discarding_sorter_control` distinguish occurrence identity, input-dependent
charges and the actual returned callback values. `pipeline_geometry` connects
value erasure to the existing intersection theorem. Its sorter charge of 17 is
explicitly a fixture, not a measured sorting bound.

### Caller obligations and remaining decisions

The inspected clients demonstrate reuse without strengthening the generic APIs
to decidable annotation equality or commutative observations. Some setup remains
intentional: an annotation author supplies its algebra/projection laws; an
interval adapter proves low-order compatibility; a measured realization proves
callback value correspondence and its chosen tariff. Library consumers then
reuse histories, prefix validity and geometry instead of repeating their
inductions. This is evidence of shared proofs, not measured author-time savings.

There is also concrete repeated fixture setup. Both `HeightSetRefinement` and
`BalancedIntervalTrees` define local recursive decision procedures for balance
and complete-cache validity. These support finite `decide` cases and do not
enter the public contracts. #658 retains a bounded maintenance opportunity to
share that fixture support if another client or change needs it; such extraction
must preserve local instance scope and avoid adding `DecidableEq` to the public
annotation interface. No new abstraction is needed to use the current clients.

The next mathematical connection belongs to **CTB-24/C05-090**, under
[#558](https://github.com/VladimirMarko/conaled/issues/558), alongside the measured
height-update obligations described in [their owner](fdsa-height-updates.md#unqualified-preparation-for-measured-operation-costs):

- Supply measured balanced insertion, predecessor extraction/deletion and direct
  overlap query, with actual callback costs and value erasure. Reuse the
  complete-cache and height results; a cache invariant alone does not price a
  callback. Keep these implementation obligations distinct from #659's completed
  source receipt.
- Discharge the premises of `scanRun_events_cost_le`: bounds apply to every
  admitted key and invariant state, and measured updates must preserve that
  invariant. [ActiveCardinality](../../Applications/Search/RectangleSweep/ActiveCardinality.lean)
  supplies cardinalities for mathematical full-schedule prefixes, including
  prefixes beyond an early hit. Its strict-key node-count bridge is checked,
  but those prefix results alone do not prove closure and bounds for arbitrary
  states admitted by the scan theorem. A finite input-key support invariant
  together with full tree validity is a prospective route, still unproved here.
- Complete the actual sorter's tariff and length-sensitive bound, then compose
  generation, sorting and scan with the admitted support/height bounds and the
  empty/small cases. Natural-number generation/pipeline counts coexist with the
  more general ordered scan observations; no trace-preserving theorem for the
  complete pipeline is claimed.

Retain these missing connections in [the measured-sweep owner](fdsa-measured-rectangle-scan.md#remaining-c05-090-work-and-acceptance-boundary),
not as assumptions asserting the desired whole-pipeline bound. The checked
`balanced_duplicate_full_prefix_nodes` and `repeated_complete_key_counts`
show why complete-key strictness, rather than interval-image cardinality, is the
relevant node-count condition. They do not supply the missing measured update
contracts.

[#561](https://github.com/VladimirMarko/conaled/issues/561) still owns the wider
historical FDSA capability dispositions; this pass does not close that inventory
or its separate chapter coverage. #658 keeps the other family assessments and
any fixture-sharing follow-up. [#588](https://github.com/VladimirMarko/conaled/issues/588)
retains its specifically requested function-Boolean and metadata-bearing
realizations; the generic tree histories do not discharge all of that issue.
For #174 and #636, adopt the demonstrated complete-cache/refinement/consumer
connections, retain the raw shape and measured execution alternatives, and
prioritize the missing C05-090 cost composition over a new universal wrapper.
No interface migration or general productivity conclusion follows from this
bounded assessment.

### Reuse for remaining textbook obligations

The following existing owners preserve useful routes from the earlier reuse
inventory. Each future textbook client still needs its actual source bridge,
original assumptions and separate resource contract. These routes add no source
qualification or receiving acceptance.

| Remaining use | Existing owner and boundary to retain |
|---|---|
| FDSA randomized sorting/selection, CTB-21/22 | [Prepared-row optimization](optimized-prepared-rows.md), [executed initialization](initialized-producer.md), and [retained dependent draws](operational-sampler-substitution.md) supply operational laws. Connect the actual recursive textbook runner, preserving duplicate occurrences, rank/failure domains, joint laws and returned cursors; price sampling separately. Fixed-row selector replacement preserves execution, while denominator normalization preserves the law without general same-tape equality. Initialization and final eager loading still cost work; almost-sure productivity is not termination on every tape. |
| Shared priorities, state changes and random-game observations | [State-change sampling](state-change-sampler.md) applies to finite rational positive-exit tables and retains suppressed work, actual cursors and altered invariant weights. It observes changed states, not latent proposal-acceptance flags. Keep its charged deadlines distinct from expected work. Treap clients under CTB-29 need a shared-priority experiment; CTB-46 first needs its own random-game/query model. Three retained draws alone do not implement arbitrary recursive runners. |
| Aggregate and cache clients | [Mapped aggregates](compiled-mapped-aggregate.md) share compiled scalar laws, retained indexed sums and stateful composition, including repeated writes and initialization. Use their public output laws and complete repair/recomputation comparison. The carrier is an additive commutative group with fixed-size indexed storage; arbitrary-monoid repair, insertion/deletion, physical sharing and uniform speedup do not follow. |
| Ranked loops and tree annotation | [Measured loops](measured-loop-comparison.md) connect native and compiled seed/test/body/post execution. Retain guard agreement, decrease, source invariants and separate value/cost transport. The bill includes the final successful guard. This bounded interface does not supply a general recursion architecture or physical-performance equality. |
| Numerical and representation clients, CTB-58/68 | [ExecutableTransport](../../Applications/Representations/ExecutableTransport.lean) requires a genuine equivalence with forward/backward value laws; its prepared recipe scan is charged each time. Non-injective observations and redundant numerals need suitable relational contracts. [FixedPoint expressions](../../Applications/FixedPoint/Expressions.lean) demonstrate explicit range, enclosure and partial-failure contracts, not machine-word/compiler guarantees. Use [native package paths](../../Examples/CubicalAuthorTransport.lean) only when the client requires their admitted discrete proof-bearing packages and exact native equivalence witness; they supply no executable conversion or allocation cost. |
| PFDS persistence and laziness, CTB-51/53/55 | The [persistent FIFO client](pfds-library-client.md) connects one executed prefix and actual branches to potential, histories and debit realization. Its workload-dependent representation comparison is already preserved there. The 77 later exercise headings, complete suspension-work correspondence and physical allocation/sharing remain separate obligations. |

Current coverage and source availability come from
[coverage.json](../textbooks/coverage.json), including the exact PFDS book/thesis
identities and the remaining Cambridge-book source boundary. Earlier
next-Extract, Chapter 5 and checkpoint-incorporation status descriptions do not
replace this current state. No second active reuse log is needed.

## Source provenance and merge decisions

The original full-spec review base is
`9175737c2b14ef738cfb6c2cdc68d885c0805ddd`. On 14 November 2026, merge
`6a4fb245642e31dea42e3bc56c413000caa3ce45` received the user-authorized pin
`983d0b6b602b71541f182737011621a8805be27b`. The subsequent pinned master is
`04514fc144dcebdd2b6d4aea5faf2f9cbf229362`, three commits later. Its receipt
retains the original review base, incoming ancestry and all public imports.
The three incoming textbook candidates share the older source base
`7c1b4a3fd55f9aeeab3fe7850e2d20000836bfcd`.

The upstream updates add operational bounded sampling, rational finite kernels,
sequential execution and explicit work accounting, then a persistent rational
table producer with coherent same-tape prefixes and joint finite-block
stationarity. Existing finite row and stopped-suffix laws are prospective owners
for relating FDSA's occurrence-index random selection and quicksort PMF runs to
actual tape sampling. That future correspondence must retain duplicate/rank
behavior, returned-cursor freshness and joint cost observations; sampling work
is a separate obligation. These terminating algorithms do not require a
stationary infinite stream. Receiving the probability developments establishes
no additional textbook obligation by itself. Their `TableSampler` models a
different concern from the partial maps below. The updates change no agent
instruction, validation policy, toolchain or dependency pin. The checkpoint
owns the exact comparison and the subsequent build evidence.

| Source | Received candidate | Integration merge |
| --- | --- | --- |
| FDSA | `e61bb6f6eaf6fd93b1b072eb3e5563b40f16defe` | `7d9cf6f091e11d24721184706e8c9f6d067bfa09` |
| PFDS | `3cf3de4fbc24c1a144353ae64b13b72f5ead54a5` | `3fe0ef512e6bae67eb4a99a414689ba0c20657fd` |
| VFA | `eae9e110adc7ba1cc28386448a6deef23e406c13` | `f5441b0e52cceea6efe825f823925319731f4c69` |

These merges preserve the incoming ancestry. Subsequent shared clients and
potential reconciliation extend this union. FDSA's mapped-potential work also
uses retained donor `12cb14fc98b8617b3b625620da8e60936daba340`, which was absent
from the FDSA candidate. The [preserved ref catalog](../history/textbooks/checkpoint-012/source/refs.json)
owns all original reference identities; the three candidate heads are not its entire mathematical
inventory.

The FDSA merge combines both theorem families in
[Resources.Growth](../../Applications/Resources/Growth.lean): master's
asymptotic carrier/cast bridges and FDSA's binary ceiling-log bounds. All
nonblank, non-import lines from each parent remain in order. The three merges
also retain both parents' public imports in `SquareApplications.lean`.

Seven PFDS and nineteen VFA conflicting files receive the pinned-master
versions. Direct comparison with the common source base shows that those
incoming modifications change only imports and blank lines; comments,
declarations and proofs are unchanged. The resolved blobs equal the receiving
parent and pinned master exactly. The compact `merge-resolutions.json` receipt
records each path, source/receiving/resolved blob identity and comparison. This
import-only decision does not describe the substantive potential reconciliation
or the new integration proofs. The receiving repository's architecture, Nix environment and GitHub workflow
govern current work; the checkpoint's local-tracker and native-toolchain
exceptions describe its producing session.

## Shared owners and connected clients

### Sorting: full values, permutations and a common specification

[TextbookSorting](../../Examples/TextbookSorting.lean) connects VFA's
[FirstPair](../../Applications/Sorting/FirstPair.lean) permutation theorem to
the ordinary sorting uniqueness results used by FDSA. Its
`sort_after_compareSwap` applies to any correct sorter for an antisymmetric
relation on the actual values. The Boolean first-pair comparator is arbitrary:
the proof needs its permutation property, not a claim that one comparison sorts
the whole list.

`preprocessedQuickSquare` and `floorSquare` give two implementations the same
`sortOn id` specification through the existing exact representation. Their
`jointSquare` uses the existing `synchronize` construction and its
`synchronized` representation, rather than introducing a textbook-specific
implementation interface. `paired_outputs` obtains equality of the two
outputs from that construction's agreement theorem; `mixed_duplicates`
transfers an existing expected result through this public relationship.

The boundary is full-value antisymmetry. Sorting records by a noninjective key
does not make equal-key records interchangeable. `equal_key_order_matters`
exhibits the stable-sort distinction after reversing two Boolean records with
the same key. Output equality also makes no claim about equal comparison
counts, allocation, sharing or runtime. The more general VFA specification
draft remains separately owned below.

### Sequences: relational full-list behavior before summaries

[TextbookSequences](../../Examples/TextbookSequences.lean) reuses
[AbstractStack](../../Applications/Sequences/AbstractStack.lean)'s separate
`Ops` and relational `Laws`, the FDSA
[DifferenceListCosts](../../Examples/DifferenceListCosts.lean) materializer,
and [OrderedSummary](../../Applications/Sequences/OrderedSummary.lean).
`append_materialize_correct` relates an actual successful abstract-stack append
to the materializer's full output list. It preserves order and repeated
occurrences without imposing a total decoder on every stack representation.

The theorem retains two explicit observations: stack append makes
`4 * xs.length + 1` primitive calls, while materialization records
`4 * xs.length + 2` closure creation/application events. These are different
tariffs, not a runtime comparison. The successful stack result also requires
enough fuel for the left list.

For the concrete stack, `custom_summary_materialize` and
`custom_summary_append` transport the full-list result to an arbitrary monoid
summary. Multiplication retains sequence order; neither commutativity nor an
injective summary is assumed. `append_head_materialize` separately connects
the actual optional result's head observation. Equal summaries are never used
to infer equal lists.

The connected cases include repeated tagged values with an ordered free-monoid
summary, successful empty input over the uninhabited `Empty` payload, and
insufficient fuel. In the last case the stack computation returns `none`
although the total materializer still returns its list and observation. Thus
failure, successful empty output and ordinary successful output remain distinct.

### Maps: shared partial meaning, valid states and weaker observations

The existing [OrderedMap.Interface](../../Applications/Search/OrderedMap/Interface.lean)
owns operations, independent partial meaning and their laws. Its ordinary
algebra now allows independent universes for keys, values and representations.
`Laws.bindAll_observation_agrees` proves agreement after every chronological
binding list from arbitrary initial states with equal meanings. Repeated keys
are allowed. The Square specializations retain the existing common-universe
requirement of that framework.

[OrderedMap.Invariant](../../Applications/Search/OrderedMap/Invariant.lean)
recovers the valid-state portion of FDSA-34 donor
`20a5b5537a704be016d09e4eb31db0dad8a12d61`. `Laws.restrict_iff` relates raw laws
on valid states to the existing unconditional laws on the valid subtype.
Empty-state validity and preservation by binding are explicit. The existing
ordered-tree implementation uses this adapter with its actual operations,
whole-tree observation and proved invariant. It gains no equation about an
invalid raw tree.

[OrderedMap.AssociationList](../../Applications/Search/OrderedMap/AssociationList.lean)
connects FDSA-34's actual Mathlib `AList` insertion and VFA's shadowing list
to this same contract. A third realization uses partial functions. An `AList`
insertion erases an earlier binding, whereas the raw list retains shadowed
entries; agreement concerns observations rather than equality of stored states.
`bindAll_lists` and `listObserve_reverse_append` establish the reversal needed
between chronological last-write bindings and raw first-match list entries,
including an arbitrary initial suffix. The adapted source notice is retained.
The function model has no finite-support or enumeration requirement.

[OrderedMap.Observations](../../Applications/Search/OrderedMap/Observations.lean)
recovers the partial-map observations of the VFA table draft, identified by
SHA-256 `0233781d210056e9a61ae9a355120429e55007e72713434d25a5338aa6489b57`.
`meaning_eq_iff` proves that presence and default-valued lookup jointly determine
partial meaning; `forget_default_not_injective` shows why default lookup alone
does not. The underlying map interface requires no default or payload equality.
`Laws.defaultBindAllSquare` uses existing vertical pasting to transport a full
binding-list client to default-valued function updates.

[TextbookMaps](../../Examples/TextbookMaps.lean) consumes these public laws.
It proves AList/list and AList/function agreement from corresponding arbitrary
starting states. `jointWrites` uses existing synchronization to relate raw
lists and ordered trees, and `alist_tree_from_empty` connects all three concrete
representations through that relationship. Its checked cases distinguish
absence from a stored optional `none`, expose repeated-key precedence and
shadowed entries, instantiate an empty payload type and type-valued payloads,
and exhibit the lookup/observation disagreement of a malformed raw tree.
The default-valued client uses the vertically pasted square itself.

[TotalTable](../../Applications/Search/OrderedMap/TotalTable.lean), delivered
under #559, recovers the weaker generic total-table contract. Its separate
operations and validity-relative laws require total lookup, not a partial
observation. `setAll` executes an arbitrary chronological update list;
`observe_setAll` relates it to function updates, and `setAll_agrees` transports
the same client between corresponding valid initial states. These laws retain
independent key, payload and representation universes. Pointwise laws and
agreement need no key equality decision; the function realization states that
requirement explicitly.

`ofPartial` specializes current map operations by applying the supplied default
at lookup. `ofPartial_laws` reuses the raw-validity/subtype bridge;
`setAll_ofPartial` proves execution is the existing `bindAll`, and
`observe_partial_setAll` retains the existing default-observation specification.
[TotalTables](../../Examples/TotalTables.lean) uses one query-after-writes client
with native functions, existing shadowing lists, raw ordered trees and a tagged
total table. Cases retain repeated keys, arbitrary initial contents, empty
updates, stored defaults versus absence, and an invalid raw-state failure.
No reverse presence reconstruction is supplied. The original partial-map
empty-payload examples remain meaningful; a total table instead needs its
explicit default value.

The representation choice belongs with #174. These contracts let callers
change implementations while preserving observations, but do not rank their
costs. The remaining FDSA-XA01 capabilities are explicitly decomposed: #587
owns map deletion and Modify round trips, #588 owns set deletion through
`AbstractSet`, and #589 owns generic valid-graph composition. Their source is
`20a5b5537a704be016d09e4eb31db0dad8a12d61`, respectively
`Applications/Collections/{Map,AList,Modify}.lean`,
`Applications/Collections/Set.lean`, and `SquareKit/ValidGraphs.lean` with
`Examples/ADTRefinement.lean`. The preserved source also includes
`Examples/SetMapContracts.lean` and `Examples/MapModify.lean`, including the
counterexamples distinguishing lookup agreement from state equality. Those
owners retain the donor's stronger laws and current integration gates. This
bounded total-table delivery does not accept those capabilities or an entire
chapter.
Lookup agreement grants no cost, allocation, physical-sharing, callback-count
or concrete-state equivalence.

### Potential accounting: one executor and a shared telescoping core

[Resources.Potential](../../Applications/Resources/Potential.lean) reconciles
PFDS's generic same-carrier and signed interfaces with the extra FDSA donor's
mapped, invariant-aware accounting. `Resources.run` remains the shared executor;
`budget` follows its actual successive states with a separately typed charge.
The same-carrier public laws specialize the mapped core through the identity
homomorphism, and existing natural-number clients remain specializations.

The ordered exact laws preserve both boundary potentials without assuming
commutativity. Inequality laws state their order and nonnegativity premises;
neither initial credit nor the observation map's meaning is implicit. The
retained signed-potential and transport clients join
[MappedPotentialAccounting](../../Examples/MappedPotentialAccounting.lean)'s
mapped, fractional, invalid-state and ordered-observation cases. The
[potential-accounting correspondence](fdsa-potential-accounting.md) owns the
precise source obligations, declarations, minimal assumptions and exclusions.

## Historical preservation families

The earlier preservation audit inspected branch tips and standalone mathematical
records, not only its three candidates. It identified 65 FDSA Lean paths absent
from that earlier candidate, plus existing-path variants, and five VFA standalone
drafts. Those counts and the INT assignments below describe that historical
inventory. They are not the current receiving scope or an additional current
work queue. Current source/paper ownership and remaining textbook requirements
are recorded by the receiving inventory above and the
[current CTB catalog and coverage](../textbooks/README.md).

The five Extract drafts now have ordinary source counterparts at their planned
paths. `Basic` and `DecodedKeys` retain their mathematical bodies; `Workload` and
`SearchTreeWorkload` retain and extend the draft programs/laws; `DecodedKeysModels`
retains its contracts with a repaired comparison-case proof and added finite
support laws. Their old uncompiled status describes the archived bytes. Their current counterparts passed R2 receiving
acceptance; the archived bytes retain their old qualification. Original source qualifications and remaining
book obligations must still be read at their actual CTB/coverage owners.

| Preserved family | Checkpoint-local owner and disposition |
| --- | --- |
| FDSA tree folds, accumulators, traversal observations, rotations, ordered search, leftmost extraction, Braun shape and Chapter 4 branches | **INT-20**, integration owner: compare capabilities with current tree owners before receiving proofs. Preserve Chapter 4's original base `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2`, 76 obligations and 11 exercises. A shared prerequisite does not close the chapter. |
| FDSA ADT refinement, priority observations, logarithm bounds, accumulated work and permutation expectation/joint-placement drafts | **INT-20**, integration owner: retain source/review evidence and give each capability an incorporation, supersession or preserved-pending disposition. Existing-path variants require capability comparison, not wholesale file replacement. |
| VFA sorting specifications, table observations, positive keys, unary comparison costs and queue-peek counterexample | **INT-21**, integration owner: preserve ordering/multiplicity hypotheses, presence versus default lookup, shifted key inverses, actual unary recursion tariff, and the reachable repeated-reversal counterexample. None is closed by the three shared clients alone. |

PFDS's wrapped historical output tree contains no additional absent Lean path
after normalizing the old `conaled/` directory prefix. It should not become a
second active library. Its coverage matrix, paper mathematics, source
obligations and forward cost contracts still constrain **INT-1**; importing
the candidate does not accept its unfinished textbook coverage.

Historical implementation work is recorded by INT-10 through INT-13 and receiving gates
by INT-90 / INT-91 and INT-SP-001 in the
[preserved review record](../history/textbooks/checkpoint-012/books/common/REVIEW.json).
The full applicable build, exhaustive three-axiom audit and independent
Standards/Spec reviews must describe the same receiving candidate and retain
the original integration base through fixes. Immediate verification and
snapshot comparison remain required. Historical approvals and focused checks
establish only their recorded scopes.

Current follow-up is owned by [#558](https://github.com/VladimirMarko/conaled/issues/558):
maps #559, sorting #560, deferred FDSA trees/resources #561, tape sampling #562,
remaining VFA drafts #563 and PFDS persistence #564. The
[repository preservation record](../history/textbooks/README.md) links the full
mathematics and book ledgers. These bounded tasks retain the outstanding wider
book scope without treating it as a prerequisite for the current public contracts.


## Checkpoint 024: tree clients and declared costs

The [curated later intake](../history/textbooks/checkpoint-024/README.md), owned
by #582, adds twelve mathematical source commits without importing the archive
or its operational payload. Its source map retains original CTB identities;
GitHub remains the live tracker.

`Examples.TreeBalancePipeline` composes measured traversal with the actual
prefix-consuming balancer. Literal, direct-suffix and staged construction routes
return the same result, including failure, but retain different complete
source-operation counts. `Examples.TreeBalanceSearch` connects rebalancing to
existing insertion and membership contracts through valid-state relational
composition. These are reusable consumers of the shared interfaces, with no
claim of physical sharing or runtime improvement.

At receipt, this intake advanced #561's tree/resource families and preserved
the Chapter 4 obligation map without completing its sibling integration tasks.
Later #559, #560 and #564 acceptance retains its own scope. #561's remaining
donor dispositions, #562's tape connection and #563's remaining drafts stay
separate, as does whole-book coverage. The bounded representation assessment
above now uses these traversal and search clients, preserving construction,
failure and observation costs; it does not claim a physical-performance result.
