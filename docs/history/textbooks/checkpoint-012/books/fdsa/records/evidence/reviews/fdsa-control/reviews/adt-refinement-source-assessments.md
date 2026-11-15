# XA01 stopped-source assessments

Status: implementation-side source readings only. The candidate is
`20a5b5537a704be016d09e4eb31db0dad8a12d61`, directly descending from the
original review base `07e480f6ec9958d4975bb90151005b84f2907614` on
`work/fdsa-adt-refinement`. No XA01 source has been compiled, and no independent
final Standards/Spec approval or chapter acceptance is claimed.

The complete frozen requirements remain 20,669 bytes / 340 lines, SHA-256
`724e4956333a93a7e60f78f37ede7c77e5c4bc30fffc3b72ddd52fb707729ab0`.
All seven frozen start-input identities still match the original start JSON.
Checkpoint 0048 saved the clean pre-code scope and evidence successfully before
source authoring was released. The original preflights, requirement assessment,
design decision and their stated limits are preserved rather than replaced by
this record.

## Ownership, stopped identities and root capture

The architecture author owned only `SquareKit/ValidGraphs.lean` and
`Applications/Collections/Set.lean`; the book/source author owned only Map,
Modify and AList; the case author owned only SetMapContracts and MapModify.
Root owned ADTRefinement, the provenance note, the three public imports and
the append-only reconstruction-map section. All source writers stopped before
the local commit. `adt-refinement-source-identities.json` records every final
byte/line/SHA identity and confirms equality with the committed blobs.

Root read all five final core modules, both complete final case modules, its
own complete ADTRefinement module, the complete provenance note and the exact
root/map diff. An earlier oversized readback call returned a truncated tool
result; it was not counted as a completed reading. The final examples were
then read in bounded complete sections, and the complete ADTRefinement and
note were read successfully. Pinned-shell Git checks confirmed the original
HEAD/branch, exactly nine new and two modified paths, no pre-existing staged
changes, clean staged/unstaged whitespace checks, exactly three added root
imports and preservation of the entire old reconstruction-map prefix. No
inherited tracked source changed. The committed diff has 2,020 insertions and
no deletions across eleven files. The worktree was clean after commit; no
project build directory exists there.

## Generic relation, Set and Map claims

The architecture author and root read the actual bridge and seven-law Set
contracts against the frozen source/API/case requirements. `validGraph` is
only the invariant plus decoder equation. `liftFun_iff` retains valid-input
conditioning, output validity and the exact model equation with independent
universes. `comp_iff` retains both the initial predicate and the intermediate
predicate after decoding. It supplies no injectivity, surjectivity or implicit
middle-operation agreement.

Set operations are separate from their seven proposition-valued law fields.
The three schema theorems consume the actual bridge; initialization is
unconditional. The Bool membership observation is decoded by equality to true
into Prop, with explicit propositional extensionality. Generic contracts add
no finite-support, order, inhabitance or decision assumption. The ordinary
client retains the two actual insertion validity steps before deletion and
membership; its exact final model and all first/second/same/other query cases
follow the stated set expression. Cross-realization agreement retains valid
inputs and equal initial observations, with no raw-state equality claim.

The book/source author and root read the actual Map, Modify and AList modules
and their inspected pinned APIs. Map has exactly six fields: empty observation
and validity, and semantic/validity pairs for update and deletion. Each semantic
field groups the changed-key equation with every unaffected-key equation.
The generic contract requires no key decision or value order/equality/default.
The optional whole-function equation uses `Function.eq_update_iff` under a
key decision. `lookup_preserves` is law-free and reflexive at the decoder.
All three actual intermediate states of the ordinary update/update/delete
client are retained. Observation agreement compares full lookup functions,
including different concrete state universes.

The modified interface has four law fields and unrestricted Option callbacks.
`toMap` uses constant callbacks; `ofMap` branches on the actual callback result
at the current lookup. Their law constructions retain the validity hypotheses
at the actual input state. `toMap_ofMap` is unconditional equality of the whole
raw Map operations record. The other direction supplies full lookup equality
and output validity on valid input, without a false concrete-state round trip
or any traversal/cost claim.

The AList adapter calls the actual standard empty/insert/erase/lookup operations
and their existing laws. Unique keys are intrinsic, external validity is True,
and only key equality is decided. Prepending/erasing insertion is explicitly
distinguished from the source ordered-list recurrence.

## Connected Set, Map and AList cases

The case author read the complete frozen requirements, start records, source
Chapter 6 and actual final core declarations before consuming the APIs. Root
read both complete final example files. The relevant connected expectations
and public theorem uses are:

| Case | Actual connection and statement-level boundary |
| --- | --- |
| Direct and paired Map models | All six actual fields; Function.update selected/off-key equations. Paired mutations add two and preserve an Even counter through explicit helpers. |
| Direct and paired Set models | All seven actual fields; Bool-to-Set reflection and point-update insertion/deletion observations. |
| Set schemas | `pairedSet_schemas` consumes all three preservation theorems; `pairedSet_initialized` consumes unconditional initialization. |
| Cross-realization clients | `pairedMap_client_model` consumes full `client_observation_agrees`; `pairedSet_client_model` consumes `client_isin_eq`. |
| Two-key Map sequence | The actual validity chain and first/second/final query pairs are `(some false,none)`, `(some false,some true)`, `(none,some true)`. Changed/off-key public laws establish them; counters separately reduce to 2,4,6. |
| Two-key Set sequence | Actual successive insertion validity and final client validity/query theorems; final queries false/true and counters 2,4,6. The documentation's earlier-stage values are independent calculations consistent with the insertion laws, not additional named fixture theorems. |
| Equal and unrelated keys | Dedicated same-key client results; a Nat Set starts with key 2 present and retains it through insert 0, insert 1, delete 0. |
| Already absent deletion | Actual full Map lookup or Set decoder remains unchanged, validity is retained, and the private counter goes from 6 to 8, proving unequal returned states. |
| Equal observations, unequal valid inputs | Counter-zero and counter-two states remain observably equal under the generic clients; no representation injectivity is assumed. |
| Actual Fin 2 AList | Sigma entries are empty, then `[(0,false)]`, then `[(1,true),(0,false)]`, then `[(1,true)]`. Generic laws give final observations and agreement with the paired model. |
| Actual Nat AList | Starts with `[(2,true)]`; key 2 stays present through every actual mutation, and final entries are `[(1,true),(2,true)]`. The final third-key claim consumes `client_lookup_untouched` on that nonempty initial state. |
| Finite-support boundary | An actual finite key list cannot realize constant `some false` on Nat. The proof uses inspected `Finset.exists_notMem`, `List.mem_toFinset`, `AList.mem_keys` and `lookup_eq_none`. |
| Empty and absence boundaries | Empty-key lookup uniqueness and initialization, Empty-value absence and actual deletion, impossibility of an Ops package over Empty states, and distinct none/some-false values with identical some-true set observation. |

The book/source author separately read the complete paused example snapshots
for bounded Map/Modify/AList assistance. No concrete Map-side API mismatch,
mathematical defect or missing frozen Map case was found. That assistance did
not replace the Set-side reading and was not an independent final axis.

## Actual composition and argument-role cases

The architecture author read ADTRefinement's Bool/product prefix against the
actual existing APIs; the book/source author read the complete tagged Map
section and the actual paired/Map declarations. Neither found a concrete
mathematical or API mismatch. Root read the complete stopped module.

The first Bool case has genuinely matching constant-true middle arrows, but
the existential composite retains the intermediate true predicate. Extending
its equation to false fails. The other case has fully valid identity-decoder
relations and individually preserving not/identity squares, but their middle
maps disagree, and the proposed pasted preservation fails. These demonstrate
different missing premises rather than relying on an invalid tagged state
whose particular observations happen to remain correct.

The Nat products use actual `Relational.product` and the valid-graph bridge.
An ordinary parameter 3 and even state 4 yield concrete 10, observed as 5;
the parameter is neither required even nor decoded. Decoding it instead gives
3, exposing the role error. Two represented inputs 4 and 6 give concrete 10
and model 5, while either one-sided validity premise permits the odd cases
(4,1) or (1,4).

The tagged route has intrinsic predicate tag=true and then the actual paired
Even invariant. Update/deletion first-stage squares use exactly the same
paired functions as the second-stage implementations, even on raw odd states.
The second stage consumes actual Map preservation. `existentialSquare` and
`transportRelations` retain tag=true AND Even counter through the exact
`comp_iff`. Nullary initialization composes actual terminal-input squares;
its input transport explicitly uses a PUnit witness. The six tagged Map laws
are derived from these composites, not assumed circularly.

The client square executes both updates then deletion, with rfl connections
to the ordinary client and nested model updates. A further actual composition
adds initialization and the law-free lookup endpoint. The final none/some-true
queries follow from the composite as well as the generic laws. All intermediate
tags stay true and counters are 0,2,4,6. True-tag/odd-counter and false-tag/even-
counter witnesses establish independence of the two predicates without
claiming every invalid state causes an observation failure.

## Modify observations and asymmetric round trip

The derived paired modified interface consumes `ofMap_laws`. Successive actual
callbacks create false from absence, keep the current value, negate it and
delete it. All intermediate validity facts are retained; key 0 yields some
false, some false, some true, none, while key 1 stays some true and counters
are 2,4,6,8. Identity preserves the full lookup but changes the concrete state.
The raw first round trip also consumes the unconditional operations theorem
at an invalid counter-one input, with returned counter three, without applying
a valid-input law to that state. An actual AList modified-interface case uses
the same derived law, changes false to true and has the stated Sigma entries.

The opposite-round-trip witness is independently lawful with validity True.
Its callback-sensitive counter increments by one if f none is none and two
otherwise. Identity at a present false binding and the reconstructed constant-
some-false call have the same full observation but counters one and two. The
case consumes the public whole-function `roundTrip_lookup` and reconstructed
validity theorem; concrete state inequality follows by projecting counters.
The Even predicate is deliberately not imposed on this different realization.

## Final source changes and documentation readback

The architecture author's initial stopped ValidGraphs and Set identities were
`54153a9d9bde60a1cc216a1f04cdbc370bd8e854022cda9db2b59bab567a4b0d`
and `3fb934a16a732368c0a0f27bf25eea816fb0798d9c1843034eacb3ab1f767c65`.
At root's request only `set_option warningAsError true` was added after
`autoImplicit false` in each new module. Removing that one line reproduces
the earlier identities exactly. This was source-authoring consistency, not a
compiler finding or an existing/global warning-policy change. The final hashes
are retained in the identity JSON.

The paused case snapshots used for bounded Map-side assistance had identities
`52f6c851291bfa4604bf9ea86e7ed20fdfeea62a6c5ec96f636a817afb39768c`
and `e4cd33d45454d7df751263403319392d82519238bbadd4b18f4411198bfa630f`.
The only final cleanup was anonymous unused key binders, removal of an unused
cases equation name and explicit off-key Function.update rewrites in three
Set observation proofs. No operation definition, statement, public signature
or expected value changed. The case author and root read the final proof text;
the final identities are in the JSON. No unobserved compiler diagnosis is
inferred from these source edits.

The architecture author additionally read the complete final provenance note
and ADTRefinement module, checked referenced contracts/translations and example
statements, and compared scope with the frozen requirements. No concrete
documentation finding arose. The exact law counts, argument/universe choices,
middle-operation and validity qualifications, independent expected values,
asymmetric round trips and explicit remaining algorithms agree with the source.
Root also read the complete note and the append-only source map. The Isabelle
notice and pinned provenance are retained. All assistance was implementation-
side and all helpers stopped without editing validation state.

## Unverified risks and required next evidence

No Lean/Lake/compiler/checker, project hash helper, cache experiment or remote
write ran for XA01. The sole task compiler/checker remains Chapter 1 session
83124 on candidate 07e480f. Ordinary file SHA-256 and local Git capture do not
supply formal evidence. No new admissions, axioms, unsafe/partial definitions,
native decision shortcut, guard/audit change or weakening was introduced.

Matching compilation must still check implicit state/instance inference,
definitional reductions through operation records and named fixtures, Fin 2
and AList Sigma rfl reductions, Set extensionality/rewrite elaboration, product
and square transport elaboration, local arithmetic, unused-variable/linter
behavior and inherited imports. Source readers found no concrete mathematical
statement or inspected-API defect; they cannot certify elaboration or the
exhaustive proof audit.

Accept repaired Chapter 1 first. Preserve the original base, complete frozen
scope and history through any later fixes or accepted-base merge. Matching
focused and full applicable guarded validation, both integrity phases,
integrated build and exhaustive audit, independent full-scope Standards and
Spec reviews, and immediate candidate verification remain mandatory. None of
the source mappings, preflights or this assessment closes a chapter or shared
unit. Concrete ordered-list/BST/interval/Set2/heap algorithms, costs, Chapter 5
direct proof, C06-035's full embedding and every original book obligation
remain queued.
