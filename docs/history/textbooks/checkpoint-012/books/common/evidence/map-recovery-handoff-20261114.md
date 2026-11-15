# Map recovery: source handoff

This is the first source-ready slice after the verified durable checkpoint 006
gate. The author edited only the six agreed Lean paths in
`recovery-20261114`, whose starting commit was `6a4fb245`. Source writes are
paused for root's focused compilation. **No current compilation or acceptance
is claimed by this handoff.** Root owns the compiler, entrypoint, source
correspondence, Git operations, independent review and durable saving.

## Recovered capabilities and owners

| Path under the source checkout | Change |
|---|---|
| `Applications/Search/OrderedMap/Interface.lean` | Keep existing operations, meaning, laws and chronological executor. Generalize their ordinary algebra to independent key, value and concrete-carrier universes. Derive arbitrary binding-list agreement between different realizations from the existing `bindAll_correct`. Preserve existing common-universe Square helpers and add `bindAllSquare`. |
| `Applications/Search/OrderedMap/Invariant.lean` | Restrict the existing operations to valid subtypes. Prove an equivalence between unconditional `Laws` there and raw observation obligations on valid states, with explicit empty/bind validity. `Laws.ofValid` is a constructor through that equivalence, not a second map interface or executor. |
| `Applications/Search/OrderedMap/Basic.lean` | Existing raw `bind`, `lookup`, independent `observe`, invariant and mathematical proof bodies remain unchanged. `rawTrees` packages those actual operations, and `trees`/`trees_laws` use the common validity adapter. The existing public tree contract remains the same. |
| `Applications/Search/OrderedMap/Observations.lean` | Recover default lookup, presence, binding reconstruction and the default-only noninjectivity result. Joint presence/default observation reflects partial-map equality. Transport chronological writes to ordinary total-function updates and use `Squares.vertical` to supply the actual default-valued client. |
| `Applications/Search/OrderedMap/AssociationList.lean` | Recover VFA shadowing lists and the XA01 adapter for actual Mathlib AList insertion/lookup as realizations of existing `Ops`/`Laws`. Relate chronological writes to reversal followed by the arbitrary initial suffix. Include the ordinary partial-function realization without a finite-support axiom. |
| `Examples/TextbookMaps.lean` | Connect actual implementations through shared clients, `synchronize`/`synchronize_agrees`, and the vertically pasted default observation. Retain discriminating cases listed below. |

The first source-ready identities are:

| File | SHA-256 |
|---|---|
| Interface | `f6ff8ba8e3f49712e0a13da39c3138180986bc2fe30663824a51cccb5950b150` |
| Invariant | `52b36d1f394e314f9c819a61cc1625875c7cd17a92d42d628e12ddf5b11c149d` |
| Basic | `8243452782c4137d6ba61b74691095ff83c196389d8a2f1b72f38f3300660dc0` |
| Observations | `8f04e0ce05638658fa10604e0a9c1fc22cfdd593d3d83d3c7880da54172a27fb` |
| AssociationList | `ed7373f507a5417d23db71d2759bcb71e1bace8adec94fa64401a377b13bdbb7` |
| TextbookMaps | `fe788a8b39e92c40be320eda77fc5c6a5d464db576849953fd57a55b90c2da85` |

These identify this development handoff, not a later correction or accepted
candidate. The repository snapshot receipt remains the authoritative full-scope
identity at review.

## Source provenance and remaining dispositions

The exact FDSA-XA01 donor is
`20a5b5537a704be016d09e4eb31db0dad8a12d61`. The author read its
`Applications/Collections/{Map,AList,Modify}.lean` and
`SquareKit/ValidGraphs.lean`. This slice recovers the empty/bind validity and
observation relationship and the actual AList insertion/lookup realization.
Its retained Isabelle notice accompanies the adapted source. The six-law Map
interface's deletion, the Modify translations/round trips, set deletion and the
general ValidGraphs composition results remain recoverable, explicitly pending
capabilities. No claim is made that this slice replaces all XA01 source.

The VFA source is
`books/vfa/records/math/drafts/table-specs/TableObservations.lean` in the
checkpoint, SHA-256
`0233781d210056e9a61ae9a355120429e55007e72713434d25a5338aa6489b57`.
It has historical focused Lean 4.35.0 success and a bounded independent review,
with TS-1 resolved in `books/vfa/records/evidence/reviews/table-spec-draft.md`.
It is not a never-compiled draft. This recovery reuses its partial observations,
list realization and precedence laws through current shared owners. Its generic
total-Table Ops/Laws remains a distinct weaker capability: a total lookup alone
does not supply the presence information needed by the partial-map contract.
The original source, validation and review evidence remain unchanged.

## Independent expected mathematics and connected cases

The cases were chosen before source edits, from the retained drafts and the
existing PFDS model. Their expected conclusions have not been adjusted to make
proofs elaborate.

- Every binding list preserves equality of complete initial partial meanings
  between lawful realizations, including arbitrary matching nonempty states.
  `alist_list_agrees` and `alist_function_agrees` use the shared client theorem;
  `paired_outputs` uses the existing synchronized implementation. AList/tree
  agreement from empty composes those bridges.
- Chronological writes `[(2,some 7),(1,none),(2,some 9)]` leave key 2 bound to
  `some 9`, key 1 successfully bound to the payload `none`, and key 3 absent.
  `stored_none_and_absent` obtains these through `lookup_bindAll`; defaulting
  both optional results to `none` loses their different presence bits.
- Writes of false at 1 and true at 3 give the total table that is true exactly
  at 3. `default_client` consumes the `Squares.vertical` construction's commuting
  law, not an isolated recomputation of an unrelated function.
- Raw list `[(0,"new"),(0,"old")]` observes `"new"`, while interpreting that
  sequence as chronological writes yields `"old"`. `precedence_boundary` uses
  the new reversal theorem. The shadowed old entry remains a member without
  becoming the observed binding.
- The partial-function realization admits payload `Empty` without a default.
  A separate ordinary client uses Bool keys and type-valued payloads, with
  different universes and no payload equality/order decision.
- A raw tree with root `(0,"root")` and a left child `(1,"hidden")` has directed
  lookup at 1 equal to `none`, while whole-tree observation finds `"hidden"`.
  It is not ordered. This separates the invariant-conditioned observation law
  from the unconditional raw update algebra.

## Statement review

The generic agreement theorem quantifies one shared chronological list and all
matching initial states. It concludes equality of full partial functions, not
merely equal domains, equal summaries or a selected query. It does not require
every abstract meaning to be realized by every concrete representation.

The validity bridge explicitly retains closure at each actual update. Empty
validity supplies a positive starting witness. Its equivalence includes the
raw bind and lookup obligations only on valid inputs; no theorem about invalid
raw states is silently added. A key decision is needed only for the existing
`write` notation and law presentation, not to construct restricted operations.
No payload inhabitance, equality, order or finiteness premise is added.

Ordinary map algebra uses independent universes. Square presentations retain
the existing foundation's common-universe requirement explicitly; this work
does not generalize `Squares.Rep` or hide a lift. The stored-none/default examples
retain both Option layers. Joint observation reflection uses an explicitly
supplied default, while default-only noninjectivity also takes an explicit key.

The function model permits arbitrary partial functions; finite support and
exact enumeration are not universal map laws. AList key uniqueness and tree
ordering belong to their respective realizations. Lookup agreement transfers
no execution cost, callback count, allocation, physical sharing or concrete
state identity. Existing shared-tree resource/retention proofs remain separate.

## Validation requested

Root should run a focused build including `Examples.TextbookMaps`,
`Examples.OrderedMap` and `Examples.SharedTreeMap`. The last imports the other
existing consumer of OrderedMap.Basic, including its explicit sharing/cost
contracts. Current proof elaboration and actual type inspection are still
required. Full acceptance additionally requires the exact combined-candidate
checker/audit, independent Standards and Spec continuation, immediate verify and
snapshot comparison under the original full-spec base.
