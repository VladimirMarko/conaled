# VFA, FDSA and PFDS integration

This integration receives the three textbook developments into the existing
`conaled` library and connects selected results through its shared contracts.
Library coherence takes priority; useful mathematics, including unfinished
proofs and counterexamples, keeps an explicit disposition. Receiving a source
branch or proving a shared client does not establish whole-book acceptance.

The [repository preservation record](../history/textbooks/README.md) owns the
received paper mathematics, historical evidence and source recovery instructions.
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

Feed newly discovered opportunities to
[#634](https://github.com/VladimirMarko/conaled/issues/634) and the experience
of applying these criteria to
[#636](https://github.com/VladimirMarko/conaled/issues/636). The latter should
identify a concrete receiving slice as evidence rather than wait for the entire
continuing CTB workstream.

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

## Useful mathematics still owned outside this component

The preservation audit inspected branch tips and standalone mathematical
records, not only the three candidates. It identified 65 FDSA Lean paths absent
from its candidate, plus existing-path variants, and five VFA standalone
drafts. The potential donor above is one selected incorporation from that
larger set. Counts identify preservation scope, not required new public files.

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

The intake advances #561's tree/resource families and preserves the Chapter 4
obligation map. It does not complete the other #561 donors, the #559 map or
#560 sorting contracts, #562's tape connection, #563's remaining drafts, or
#564's persistence/suspension client. VFA Preface/Perm coverage qualification
and historical source-complete statuses remain distinct from whole-book
acceptance. The next integration step should exercise these contracts in a
representation decision, preserving construction, forcing and observation costs.
