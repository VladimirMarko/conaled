# XH01 source-author and root statement assessments

This record is source-only assessment inside the current implementation loop.
It is not a compiler result, an independent final review axis, an audit or an
acceptance decision. Chapter 1 session 83124 remains the sole compiler/checker.
The original base is `07e480f6ec9958d4975bb90151005b84f2907614`; the complete
581-line requirements retain SHA-256
`ea6e81e44065a8c0d7a719374cf377c1692b81672a96af71b7c92aeaf348d6ca`.
Successful pre-code checkpoint 0050 preceded root's explicit author release.

## PriorityMultiset: complete stopped author draft and root readback

The architecture author stopped after its full owned-file statement/proof
readback and a bounded inspection of the actual pinned supporting APIs. Root
read the complete published 401-line file, including every declaration and
proof, then independently checked the stopped file identity:

- Path: `Applications/Search/PriorityMultiset.lean`.
- Bytes / lines: 18,139 / 401.
- SHA-256: `f91f16d5e676526b10fbd0cbe21a6c3c69dc823f4d213bd36a71b3234263ad08`.
- No public statement changed after publication. The author reports that its
  only earlier proof-shape adjustment explicitly supplied `(a := (x, p))` to
  `Multiset.mem_map_of_mem` in direct-root leastness. That adjustment is already
  present in the complete snapshot root read; it changes no claim or premise.

The following grouped readback covers every new formal declaration, including
the private finite-minimum helper. It checks the mathematical statement and its
actual operation connection; it does not assert Lean has elaborated the proof.

### Ordinary operations and their actual branches

`Operations.insertOne`, `peekEntry?`, `peekPriority?`, `deleteMin`, and `isEmpty`
take only the existing Operations value. They retain independent payload,
priority and carrier universes and introduce no LE, observation, law, validity,
equality decision or inhabitance premise. The two peeks project the same actual
removal. Deletion's none branch is exactly identity on the input; its some
branch is exactly that result's residual. Emptiness is Option.isNone.

`views_of_none` and `views_of_some` condition all four view results on the
actual supplied removal equation; none or the actual entry/residual is kept
throughout. `Operations.isEmpty_eq_true_iff` is Boolean-to-Prop reflection, not
an equality of types Bool and Prop. No timing claim follows from these views.

### Exact observations, insertion, cardinality and raw failure

`ExactQueue.entryMultiset`, `priorityMultiset`, and `popObs` are observations
on the existing selected exact queue. The first retains full occurrences;
the second maps only priorities; the third observes the priority and actual
residual together under Option. The existing ExactQueue type supplies LE, but
these observations introduce no additional order or equality structure.

`entryMultiset_empty` / `priorityMultiset_empty` consume the actual empty
entry equation. `entryMultiset_add` / `priorityMultiset_add`,
`entryMultiset_insertOne` / `priorityMultiset_insertOne`, and
`priorityMultiset_insertOne_add` preserve multiplicities and the unconditional
raw add_exact domain. Their order in the multiset sum is observational, not a
claim to change actual batch insertion order. `insertOne_valid` separately
retains the actual input-validity premise.

`entryMultiset_card` / `priorityMultiset_card` equate the two finite multiset
cardinalities to the actual entry-list length. `entryMultiset_add_card` and
`priorityMultiset_add_card` add the complete inserted list's length, retaining
duplicates and the same raw-state domain.

`remove_none_iff_entryMultiset`, `priorityMultiset_eq_zero_iff`,
`remove_none_iff_priorityMultiset` and `ExactQueue.isEmpty_eq_true_iff` keep
the existing unconditional remove_none law. Mapping the priority projection
does not remove entries, so its zero reflection needs no injectivity premise.
`exists_remove_of_ne_zero` uses that raw failure reflection to produce an
actual some result before any validity assumption. It promises no minimum or
valid residual at this stage.

### Valid removal and atomic cross-realization agreement

`remove_spec_multiset` requires both actual input validity and the actual
successful removal equation. Its five conclusions are residual validity,
selected full-entry membership, full-entry cons decomposition, selected
priority IsLeast on the input priority support, and priority cons
decomposition. No payload equality decision is introduced. `remove_card`
and `remove_priority_card` state residual cardinality plus one equals input
cardinality; their hypotheses are exactly the same successful valid removal.

`deleteMin_valid` examines the actual Option result. On none it reuses input
validity because the chosen view returns that same state; on some it uses the
actual residual validity. Its stronger valid-empty behavior does not alter the
book's nonempty-domain law. `popObs_of_remove` is only an observation of a
supplied actual result and adds no unsupported semantic promise.

`popObs_eq Q R hantisymm q r hq hr hobs` has the fixed public call order,
independent payload/carrier universes, shared priority type/LE, both actual
validity premises, equal input priority multisets, and explicit antisymmetry.
Its conclusion compares the actual Option pair observations. Root checked all
none/some branches. Two least memberships give mutual comparison; antisymmetry
equates priorities, and same-cons cancellation equates residual multisets.
There is no hidden use of totality, transitivity, DecidableEq, shared payloads,
raw-state equality, full-entry residual equality, tie stability or a cost law.

### Realizability, empty types and the source minimum boundary

`exists_entryMultiset` selects an actual finite list representative by quotient
induction and inserts it into the actual empty queue; it carries real empty
and insertion validity. `exists_priorityMultiset` explicitly takes one payload
and maps every finite priority occurrence to that payload before using the
entry result. Neither is a raw-state inverse or uniqueness statement.

`entryMultiset_eq_zero_of_isEmpty_payload` and
`entryMultiset_eq_zero_of_isEmpty_priority` quantify over every raw state and
eliminate an impossible entry component. They do not add arbitrary defaults
or nonempty-priority realizability for an empty payload type.

`priorityMultiset_remove_sub` keeps successful actual removal and input
validity, adding DecidableEq only on priorities for subtraction. The private
`removed_priority_eq_min`, public `peekPriority?_eq_min`, and
`priorityMultiset_deleteMin_sub_min` use LinearOrder only at the source
finite-support boundary and retain nonempty observation plus actual validity.
The optional minimum result and state deletion refer to the same computed
removal, so the subtracted occurrence is the proved support minimum. These
general results supply the Unit source specialization without ordering its
payloads or requiring a total element-valued operation on empty types.

### Existing leftist carrier: raw observations and Heap-only leastness

`Search.LeftistQueue.peekQ?` directly matches the actual existing raw carrier
with no comparison premise. `deleteQ_fst` preserves only LE/DecidableLE needed
to execute the unchanged deleteQ, and its value equation covers every raw
tree. `peekQ?_eq_none_iff`, `nullQ_iff_entries_nil`,
`nullQ_iff_entryMultiset` and `nullQ_iff_priorityMultiset` likewise keep raw
structural/content reflection without constructing a stronger exactLeftist
bundle or imposing order assumptions.

`peekQ?_isLeast` consumes actual Heap and the actual root peek equation.
Its existing root_all proof needs LE and Std.IsLinearPreorder; it imposes
neither Ranked nor comparison decisions. A least root alone does not establish
cached ranks or residual validity. No direct-root statement assigns a cost.

### Assessment and limits

Root and the source author found no concrete mathematical scope/hypothesis
discrepancy in this stopped draft. The central cancellation, finite-model
domains, one-occurrence source subtraction, actual-view branches and invalid
state boundaries match the frozen requirements. The source header attributes
the companion contracts and points to the root-owned note's exact URLs and
complete applicable BSD notice.

Actual Lean elaboration, coercion/rewrite behavior and warnings-as-errors are
unrun. The public consumers and their independent expected calculations must
still be read in their completed files. Full matching candidate validation,
both final independent review axes and immediate verification remain pending.
Other source owners are still active; this is not the final candidate capture.

## PriorityMerge: complete stopped author draft and root readback

The source/merge author read the complete published 401-line PriorityMultiset
before consuming its actual API. It then completed its only owned file and
stopped. Root read all 268 lines, including every statement and proof, and
independently confirmed this exact stopped identity:

- Path: `Applications/Search/PriorityMerge.lean`.
- Bytes / lines: 13,484 / 268.
- SHA-256: `55dc0b17678ce4c647311cc4e6bcded2f9ed29ea2baa740885b5e8aa0fb954c1`.

`MergeLaws` has exactly the two frozen proposition fields, `entries_perm` and
`valid`, with the existing carrier/entries/validity/merge supplied as parameters.
Payload, priority and carrier universes are independent; the record itself
uses no order. `leftistMergeLaws` consumes actual existing combineQ_entries and
combineQ_valid without editing them. `appendMergeLaws` is genuinely order-free
ordinary append/identity/True evidence. Both preserve the same selected carrier
and observation rather than introduce a replacement representation.

`mergeInsertRemove` takes only Operations, the supplied merge, entry and two
raw input states. Its definition is precisely the frozen merge/add-singleton/
actual-remove expression; no model or evidence is passed to the operation.

`entryMultiset_merge` and `priorityMultiset_merge` convert the actual merge
entry permutation into multiplicity sums, retaining both actual input validity
proofs. `entryMultiset_merge_card` and `priorityMultiset_merge_card` take the
cardinality of those same observations. No disjointness, payload order or
equality decision is introduced.

The entry/priority pairs `*_merge_comm`, `*_merge_assoc`, `*_empty_merge` and
`*_merge_empty` are observational equalities only. Root checked that both
associativity parenthesizations use the actual intermediate merge-validity
proofs; empty identities use the actual Q.empty_valid. Nothing asserts raw
shape equality or idempotence, and persistent reuse of the same input adds
its logical occurrences again without claiming an amortized resource law.

`mergeInsert_valid`, `entryMultiset_mergeInsert` and
`priorityMultiset_mergeInsert` connect the real merged state and real singleton
insertion to both original observations, consuming the merge and insertion
laws. `mergeInsert_nonempty` instead uses unconditional exact insertion and
therefore needs neither MergeLaws nor initial validity. `mergeInsertRemove_exists`
then uses unconditional exact failure reflection to obtain an actual successful
result. These stronger raw-domain facts promise neither a minimum nor validity.

`mergeInsertRemove_spec` retains both initial validity hypotheses, the selected
MergeLaws and an equation for the actual ordinary client result. Its conjunction
contains actual merged and inserted validity, actual inserted nonemptiness,
actual residual validity, full-entry and priority one-occurrence equations,
least returned priority, and both exact residual cardinalities. Entry membership
is an immediate consequence of its full-entry decomposition; the source
requirement does not demand a separate redundant membership field. The public
existence theorem supplies an actual result to which this specification applies.

Root checked every intermediate equation: insert content is derived from the
real public add/merge facts; actual remove_spec_multiset supplies the result
equations/leastness; cardinality is cancelled only after taking the actual
remove count and actual inserted observations. The final count is the sum of
the two initial counts, without claiming the removed and inserted entries are
the same. Neither cost nor raw residual equality is inferred.

Root and the author found no concrete mathematical scope/hypothesis discrepancy.
The source header points to the exact primary provenance and applicable notice.
Elaboration, coercions, rewrite execution and warning cleanliness remain
unverified; no compiler, checker or project hash helper was run. The actual
full client conjunction and argument order were published to the case author,
whose completed connected consumers remain to be read.

## Root prose and architecture-author bounded readback

After root updated the core source-law mapping to the actual stopped public
names, the architecture author read the complete note and appended source-map
section. It reported no concrete discrepancy in the core-facing mathematics,
weak premises, universes, raw/valid distinction, Option branches, seven/eight-law
count, one-way adaptation, realizability/Empty/direct-root/cost boundaries,
license or truthful uncompiled/unaccepted status.

The assessed historical prose identities were:

- `docs/research/fdsa-priority-queues.md`: 20,705 bytes / 326 lines, SHA-256
  `54a89c49c10fbd187a88ca2be9253e4c6c854cc5d73393036493d40afd639c38`.
- Full `docs/research/fdsa-reconstruction-map.md`: 18,147 bytes / 296 lines,
  SHA-256 `3ce0347382f843e17d76c2bf1a8795f4d7a9c5d37954108f7f26cf9206a59fec`.
- Its appended XH01 section: 2,183 bytes / 33 lines, SHA-256
  `2d28f971a795a027a193631e0d3cb6b8b77f7670de3befe3b1412cc7111621e2`.

The notice's only textual normalization is removal of trailing spaces; the
cited notice SHA identifies the retained exact primary file. This bounded
readback intentionally treated merge/example descriptions as frozen intended
connections, rather than approve their then-active source drafts. It is an
implementation-side assessment, not an independent final axis.

After root's full stopped merge read, the note was refined with the actual
merge theorem names, explicit raw existence versus valid result separation,
the explanation that entry membership follows from decomposition, and exact
later primary-source links. These are prose clarifications, not changes to
the frozen scope or either stopped core file. The final prose/consumer byte
identities will be captured only after the case author finishes and root reads
the complete final files.

## Initial complete example readback and bounded connection requests

Root captured a fixed full example snapshot while the author performed its
last bounded pass, then read all 717 lines in three complete consecutive
chunks. That read snapshot was 33,108 bytes, SHA-256
`5325ecb430f12587446e9d6f58a9eeb65d7110195519fed504fdc2d4e41a99ff`.
This is a historical read identity, not a separately retained source file.
All eleven intended mathematical families are present, with the correct
actual operations, values, validity boundaries and core/client connections.
No false mathematical statement or changed expected value was identified.

Before final stop, root requested two bounded connections already required by
the frozen scope:

1. Explicit actual-state uses of public `entryMultiset_add_card`,
   `entryMultiset_merge_card`, and `priorityMultiset_card` in the existing
   A/B/M/I stage-count cases. A targeted read confirmed that the first two
   had no retained consumer in this snapshot and the priority-cardinality
   bridge had no explicit actual-state consumer. This completes the frozen
   each-public-theorem-use/stage-count requirement without a new test harness.
2. A compact arbitrary-σ `[LinearOrder σ]` Unit-payload source section that
   explicitly specializes the already sufficient generic results to all seven
   source laws and the separate eighth companion reflection. Existing Unit/Nat
   duplicate cases remain. This exposes the literal XH01-03 source contract
   directly, without a new carrier/law hierarchy or duplicated generic proofs.

These are implementation-side source-use/exposure requests, not independent
Spec findings or evidence that compilation failed. The original frozen
requirements and every existing fixture/expected value remain unchanged.
They remain to be checked in the final stopped source.

The author also reported bounded proof-shape cleanup of closed `rw; rfl`
sequences and explicit tied-payload projection/C-H-K deletion-view conclusions.
Those changes must be read in the final version and must not be described as
compiler-confirmed fixes. The architecture author began a read-only API/
assumption check on a later 734-line intermediate snapshot, SHA-256
`3648168a0bcbfe12012692dc7444e632122b981b8ba6712ce03568138c038e58`;
root notified it that the two connection requests make that snapshot historical.
Any peer report must identify its actual read version and limitations.

## Complete final example readback: both connection requests supplied

The held intermediate 734-line file was preserved exactly as
`reviews/priority-queue-examples-intermediate.lean.txt`, 34,581 bytes,
SHA-256 `3648168a0bcbfe12012692dc7444e632122b981b8ba6712ce03568138c038e58`.
This lets source-only peers refer to immutable bytes while the owner finishes
the authorized additions. Root resumed the same sole-file author after the
agent roster reported it interrupted; the owner confirmed no restart/overwrite.

The author then completed its full final readback and stopped all source writes.
Root read every final line, statement and proof in three complete consecutive
chunks, verifying the same exact hash before each chunk:

- Path: `Examples/PriorityModels.lean`.
- Bytes / lines: 38,245 / 808.
- SHA-256: `6edc9c808630a0d1c369fce033dd7e5fb6ba67e9fecd270081adbb1c55db4ae9`.
- Both core files retain their previously stopped identities.

The following covers the complete final formal content, including its private
raw-removal helper and local instance declarations.

### Explicit source specialization and actual fixtures

`SourceUnit` takes arbitrary σ/LinearOrder and an existing exact queue with
Unit payloads and independent carrier universe. `empty_content`, `empty_valid`,
`insert_content`, `insert_valid`, `delete_content`, `delete_valid` and
`get_minimum` expose exactly the seven printed laws; `isEmpty_reflection` is
separate. These are applications of the actual generic results, with actual
singleton add, Option minimum and deletion view. The original valid/nonempty
domains are retained, including intentionally unused `_hq`/`_hne` where the
generic theorem is stronger. There is no additional carrier, default getter,
contract hierarchy, or equality/order premise on payloads. This supplies the
second bounded root request at source level.

The Unit/Nat leftist and exact-list abbreviations, Bool-payload/Nat queue,
`leaf`, duplicate/input/merge/insert/residual definitions, actual list states,
two tied singleton/merged states, and corrupt/wrongOrder/corruptBelow fixtures
retain every original operation and expected value. Closed shape, entries,
removal, list-order and insertion equations use ordinary allowed kernel
proof syntax. Their calculation results are mathematically consistent with
the frozen foldr insertion and rank-aware first-tie merge, but compilation of
those calculations has not occurred.

### Duplicates, counts, source minimum and finite realization

The duplicate shape/validity/entries/removal and priority observations describe
exactly [1,1,3] and actual residual [1,3]. `duplicates_certificate` applies the
public five-part removal result to that actual removal. Residual cardinality
uses the public exact one-drop result and independently determined input count.
`duplicates_pop`, `duplicates_nonempty`, `duplicates_minimum` and
`duplicates_source_subtraction` connect actual removal, optional finite-support
minimum and deletion of one occurrence. The following examples use actual
delete validity, public minimum/subtraction, and closed [1,3] content; one
copy of 1 remains. No set deletion or total empty-type getter is substituted.

`input_cardinalities` applies both `entryMultiset_card` and
`priorityMultiset_card` to the independently computed two-entry A/B lists.
`entry_stage_cardinalities` applies `entryMultiset_merge_card`,
`entryMultiset_add_card` and the actual common-client residual certificate to
the same M/I/residual states, obtaining 4/5/4. The separate priority-stage
case consumes the corresponding priority merge/add counts. Thus the first
bounded root request has actual retained consumers, not merely extra names
or assumptions asserting the desired stage lengths.

`duplicates_from_empty` and `duplicates_entry_realization` use actual batch
insertion into empty. The two existential examples consume public finite-entry
and explicit-payload priority realization on the duplicate multiset, then use
the central atomic theorem to compare the obtained valid state to the actual
duplicate queue. They do not assert raw-state uniqueness or a default payload.

The lifted list state is actually built by add/empty with `ULift.{1} Unit`
payloads. Its validity and priority contents are proved from the actual laws.
The central call compares it with the lower-universe Unit leftist queue and
derives the same some(1,[1,3]) observation without identifying carriers/payloads.

### Actual common clients and observational algebra

`main_client_result` is the actual merge/add/remove expression, definitionally
the separately calculated inserted removal. `main_client_certificate` consumes
the full common specification with both initial validity proofs and that actual
result. Merged/inserted/residual validity and all count consequences are obtained
from this certificate. The inserted 2 is present in the residual [1,2,2,3];
the removed priority is 1, so equal input/output cardinalities do not assert
identity of inserted and removed occurrences.

The list client uses actual add/empty and append. `list_client_stages` first
uses the public actual-result existence theorem, then the common specification
to carry intermediate and residual validity and the count. The actual list
before removal is [1,3,1,2,2]. `client_input_agreement` uses the two real merge
witnesses and actual insertion observations. The final paired client example
calls `popObs_eq` with both actual inserted-state validity proofs and these
equal contents to obtain some(1,[1,2,2,3]) for both operations. It assumes no
mergeSort stability, identical input list order or common carrier.

Self-merge [1,3] yields [1,1,3,3] through the public merge law, and is explicitly
non-idempotent. Actual nonempty operands exercise entry commutativity, priority
associativity and all four full-entry/priority empty identities. The actual
merge validity needed by nested associativity remains in the public proof.
These are observations, not raw-state or amortized-resource laws.

### Ties, optional emptiness and actual malformed residuals

The Bool-payload tied queues are valid actual merges of the two valid singleton
states. Opposite merges actually remove false versus true and leave the
opposite singleton. Priority-content commutativity plus `popObs_eq` gives
equal atomic observations some(1,{1}). Separate actual-view examples prove
unequal full entries, selected payload projections, residual entry multisets
and raw merged states. This preserves exactly the central theorem's boundary.

Actual empty leftist/list views use the raw failure equivalences and public
none-branch views; Boolean reflection and direct nullQ are connected. A valid
singleton 7 actually removes to empty, and the public removal result supplies
validity of that same empty residual. No default value is used.

The private `raw_remove_entries` conditions only on the actual successful raw
deletion and directly uses the unchanged combineQ_entries theorem. It covers
C/H/K without any Heap/Ranked/Valid assumption. All raw content examples use
this result rather than applying abstract valid-removal laws to invalid inputs.
The unused node-rank case binder is `_` in the final proof; no hypothesis or
statement changed.

C has Heap but not Ranked; its actual root is least and the actual deleteMin
residual is valid empty. H is Ranked but not Heap; its actual chosen 3 is not
least because 1 occurs, while the actual singleton residual is valid. K has
Heap but invalid child rank; its actual minimum 0 leaves invalid C. Public
Heap-only root leastness, raw root/delete/nullQ correspondences and actual
some-branch deletion views retain these distinctions. Actual insertion of 0
into C yields K: the unconditional add_exact and priority insertion laws give
[0,1], while the corrupt child prevents validity. Content never repairs the
invariant by itself.

### Fixed keyed observation, Empty domains and local preorder boundary

The keyed fixture fixes actual PrioritySearchQueue.keyed, pairKey, its identity
entry observation and Unique validity. The retained old same-key/tie equation
gives one output from the two-entry batch. Actual keyed coverage and length
laws are consumed. `fixed_keyed_not_exact` derives length one versus two from
assuming ExactLaws on precisely those fixed operations/entries/validity; it
does not quantify over alternative observations or all keyed implementations.
The separate general example retains the existing forward ExactQueue.keyed
weakening, with no converse claim.

Empty-payload/Nat results quantify over all raw states of an arbitrary selected
exact queue, prove empty entries/observations and actual none/Boolean results,
then specialize to real leftist/list queues. The singleton-priority realizability
counterexample retains this exact Empty-payload boundary, while the carrier
IsEmpty example contradicts the actual Operations.empty value. Generic finite
entry realizability is not contradicted: those finite entry multisets are empty.

`Indiscrete` supplies only local LE Bool, decidability and Std.IsLinearPreorder
instances for the relation True. Actual opposite merges of valid false/true
priority singletons select different priorities with equal initial multisets.
Both actual results satisfy public leastness; explicit antisymmetry fails and
`different_popObs` refutes atomic priority equality. The local declarations
end with that namespace and do not install the relation globally.

`EmptyPriority` likewise uses local vacuous instances. Every actual leftist
tree/list with Unit payloads and Empty priorities is structurally empty; the
generic IsEmpty-priority observation theorem supplies actual failure and none.
Direct-root and semantic peek agree, and actual list deletion returns the
same raw input on failure. No Inhabited requirement is introduced.

### Final source assessment and remaining validation

Root and the author found no concrete mathematical/API scope discrepancy in
the complete stopped final file. Both bounded connection requests are supplied
at source level. The guarded tactic sequencing is authoring proof-shape cleanup,
not a compiler-confirmed fix; no warning option or assertion was weakened.
The author read both complete actual core files before consuming them.

The final 808-line snapshot was sent to bounded source-only peers with the
734-line history explicitly distinguished. Their reports, when received, must
retain exact version limits and cannot serve as either final independent axis.
Actual elaboration, local-instance resolution, simplification, kernel closed
calculations and warning cleanliness remain unverified. No XH01 compiler/checker,
project hash helper, audit or acceptance run occurred. All source writers are
stopped; exact full-scope capture/commit and the draft checkpoint are next.

## Final root prose and immutable capture

Root read the complete final 362-line source/license note after adding actual
SourceUnit and concrete-client/negative-case declaration names. Its final
identity is 23,331 bytes, SHA-256
`909599e4ed03fb4aec1d517aa26b97bb3f32a08500f4b0c3d6b7899adce7e64b`.
The only public-root change is the single intended import, and the complete
original source-map prefix was independently checked unchanged. All source
writers stopped; exact full six-path, seven-input and seven-preserved-source
checks are in `priority-queue-source-identities.json`.

Normal Git staging/whitespace/scope checks preceded the local commit
`c088beeb89aa18df45a56f6f1d6b6ff4ad374905`: six paths, 1,874 insertions,
no deletions, clean worktree and unchanged 07e480f original base/parent.
See `priority-queue-candidate.json` and `.md`. These are immutable source-draft
identities, not compiler or final-review evidence. The separate Chapter 1
session interruption and retained continuation ruling are preserved in INC02.
No XH01 validation ran; no chapter or shared unit is accepted.

## Final bounded author-peer readback

After checkpoint 0051, retained author collaborator `/root/architecture`
reported reading all 734 lines of the preserved intermediate snapshot and
every added line of the final 808-line example. The final identity is
38245 bytes, SHA-256
`6edc9c808630a0d1c369fce033dd7e5fb6ba67e9fecd270081adbb1c55db4ae9`;
the compared core remains
`f91f16d5e676526b10fbd0cbe21a6c3c69dc823f4d213bd36a71b3234263ad08`.
The peer confirmed the generic seven-law SourceUnit plus separate reflection
and the two actual public-cardinality applications, with no concrete API,
mathematical or missing-family issue. The previously read local-order, empty
type, tied-payload, fixed-key and malformed-state boundaries remain consistent
with the stopped core. This is source-only author collaboration: elaboration,
instance synthesis, proof execution and warning cleanliness remain untested.
It supplies neither final independent review nor acceptance. No source changed.
