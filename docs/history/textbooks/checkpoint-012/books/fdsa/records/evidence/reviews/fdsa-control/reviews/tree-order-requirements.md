# Frozen requirements — FDSA-XT07 shared ordered-tree observations

Frozen 2026-11-02 before any XT07 source edit. This is a cross-cutting unit
under the user's explicit exception; Chapter 1 remains the active chapter.
No chapter, appendix or shared draft is accepted by this freeze. Preserve
this document unchanged; record later clarifications as explicit addenda.

## 1. Original base, dependencies and complete scope

Original review base and intended immediate parent:
`28ba79d8d425400cb87d2daf3ecf1cc5a63a7aa2` (the committed XT06 draft).
Intended branch: `work/fdsa-tree-order`.
Intended isolated worktree: `conaled-tree-order`.
The start record must verify that exact clean base and absent new files before
implementation. No existing source is edited until the pre-code checkpoint
has been created, exposed and successfully uploaded.

Accepted repaired Chapter 1, XT01 and XT06 are prerequisites for integration
and acceptance. Their saved drafts may be read and used for isolated source
authoring, but remain unaccepted. XT07 has no dependency on XT02–XT05,
the probability branches, XQ01, or any not-yet-implemented chapter algorithm.
The core observation module should depend only on XT01; XT06 is consumed by
the separate rotation adapter and examples. Preserve the inherited history,
including the old Chapter 1 repair ancestor, and later merge accepted proof
corrections without rewriting the original base or review scope.

The initial post-Chapter-1 integration prefix remains exactly
`c80eec92f5458eccfd1c34c8314d666c2a1e3847`. XT07 is not added to that prefix
and does not activate Chapters 2, 4, 5, 6 or a later balanced-tree chapter.

Expected complete candidate paths:

1. `Applications/Trees/Ordered.lean` — one recursive relation invariant,
   observation and mapping laws, strict-key consequences.
2. `Applications/Trees/OrderedRotations.lean` — small ordinary and cached
   root-rotation adapters consuming the actual XT06 laws.
3. `Examples/OrderedTrees.lean` — connected generic, concrete and boundary uses.
4. `SquareApplications.lean` — add the example import, preserving prior imports.
5. `docs/research/fdsa-tree-order.md` — provenance, exact mathematical scope,
   source/statement assessment and applicable notice.
6. `docs/research/fdsa-reconstruction-map.md` — append the shared support map
   and pending limits without erasing earlier coverage or findings.

Changes to an existing tree definition, root-rotation operation, cache
invariant, measured executor, source policy, audit tooling, dependency pin or
warning setting are outside this freeze. A concrete inherited defect must
be recorded and repaired in the owning retained loop, not silently changed
as part of XT07. No other new source path is presumed necessary.

## 2. Source and completed preparation

Read `REQUEST.md`, the relevant chapter inventories and the following complete
preflights. Root read all three and the actual source interfaces before this
freeze. These are source assessments, not validation or final review:

| Evidence | SHA-256 |
| --- | --- |
| `research/tree-order-source-preflight.md` (26,305 bytes, 343 lines) | `e7b019f6e3102b081b1c42a446ae36ac709e6cf7e6370ec034a4d744e9a2a880` |
| `research/tree-order-api-preflight.md` (24,262 bytes, 351 lines) | `a6bea839b095ea453bbd83ec4c19f67aa6766b905e83654faacec60adea61ca3` |
| `research/tree-order-case-preflight.md` (12,227 bytes, 210 lines) | `e5c680ecdd0430f71e96f7149ebc64bdd4d834f7b0272129f0976bac4c537ffe` |

The book is the July 27, 2026 edition, PDF SHA-256
`9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`.
Primary manuscript claims are Chapter 5 p.59's recursive strict BST and
p.64's inorder equivalence, with strict-list decomposition on pp.64–66 and
Chapter 6 pp.81–83's full semantic map records ordered by their keys.
Chapter 4 supplies the ordinary carrier/inorder/augmentation observations;
its p.54 sorted-input sentence retains the existing duplicate-input correction.

The companion revision is `f86f290225eebcc52c1ae7dba2e098f405f51c21`, not
asserted to be the commit that built the manuscript. Relevant exact inputs
are `Tree.thy`, `Sorted_Less.thy`, `Tree_Set.thy`, `Tree_Map.thy`,
`AList_Upd_Del.thy`, `Tree2.thy` and `Tree_Rotations.thy`, with identities and
locations in the source preflight. Reproduce the applicable pinned Isabelle
BSD-3-Clause notice in the provenance note for adapted definitions/laws.

The book's Chapter 5 `sorted` is strict `<`; Chapter 2's ordering is weak `≤`.
The companion likewise hides weak `sorted` for its strict set/map framework.
Full semantic `(key,value)` records must not be confused with a payload plus
a recomputable cache annotation. The existing p.82 split-min reference error
and the distinct direct-proof requirement of Exercise 5.3 remain recorded.

## 3. One structural predicate on the existing carrier

Use Mathlib `BinaryTree α`, whose constructor is `.node label left right`,
and the existing `Trees.inorder`. Introduce one recursive proposition,
`Trees.Ordered (R : α → α → Prop) : BinaryTree α → Prop`, with content:

```text
Ordered R nil = True
Ordered R (node a l r) =
  Ordered R l ∧ Ordered R r ∧
  (∀ x ∈ inorder l, R x a) ∧ (∀ y ∈ inorder r, R a y).
```

Publish the nil and node equations. Whole-subtree bounds are required;
comparing only the immediate child roots is insufficient. Inorder membership
already observes every label occurrence. Explain its source correspondence
using the existing nil/node list equations and standard membership laws;
do not introduce another tree carrier, inorder, Finset enumeration, membership
class, executable comparator, or general preservation record.

No relation laws, equality decision, payload order, finite payload carrier,
key projection, or `Inhabited α` premise belongs to this definition.
Payload, target-label, key and annotation universes should remain independent
where their actual interfaces permit it. Keep `autoImplicit false` and the
existing warning policy.

## 4. Required relation and inorder laws

Provide these public mathematical connections; precise helper names beyond
the primary predicate may follow existing local style and must be shared
with the example/adapter authors before use:

1. For arbitrary R, `List.Pairwise R (Trees.inorder t)` implies
   `Trees.Ordered R t`. This direction requires no transitivity.
2. Under an explicit `Transitive R` premise, the recursive invariant implies
   the pairwise inorder observation. Combine these into the corresponding
   iff. The proof must supply every left-to-right cross-subtree comparison
   through the root; it cannot omit that component of `pairwise_append`.
3. Under the same transitivity premise, equality of two actual inorder lists
   transports and reflects `Ordered R`. This reusable observation law is the
   intended connection for rotations and later inorder-preserving algorithms.
4. Pointwise implication `∀ a b, R a b → S a b` transports the recursive
   invariant on the same tree, without transitivity assumptions.
5. The exact map pullback holds for arbitrary relations and maps:
   `Ordered S (t.map f) ↔ Ordered (fun a b => S (f a) (f b)) t`.
   It must not acquire injectivity, transitivity, equality decisions or an
   order on payloads merely from a proof routed through a stronger theorem.
6. Demonstrate forward relation-preserving mapping through the pullback and
   monotonicity laws, and preservation/reflection for key-preserving payload
   maps. This may use a thin public specialization or a generic connected
   client; no second recursive invariant or general record is needed.

Transitivity is a uniform sufficient law for the bridge, not a necessary iff
condition on every individual tree. An exact arbitrary-relation node
decomposition must retain all left/right cross comparisons. Do not advertise
the bridge's assumptions as logically minimal for every separate consequence:
asymmetry alone can give a direct structural Nodup proof, but that additional
generic theorem is not a deliverable here.

No arbitrary relation-preserving map is automatically relation-reflecting.
`StrictMono` gives forward preservation between preorders; an iff needs
reflection or appropriate stronger source hypotheses. Key-preserving maps
can give an iff because the pulled-back key relation is identical, even
when the payload map is globally noninjective.

## 5. Strict keys, adjacency and repeated-key boundary

For arbitrary `key : α → κ` and `[Preorder κ]`, specialize the single
predicate to `fun a b => key a < key b` and establish its equivalence with
pairwise strict order of `(Trees.inorder t).map key`. Reuse the generic
inorder theorem and `List.pairwise_map`.

Connect that observation to the pinned standard `List.SortedLT`, and to its
`List.IsChain (<)` adjacent-element characterization. A public core bridge
plus the existing standard theorem in a connected generic client is enough;
do not implement another sorted-list predicate. The actual pinned APIs are
`List.sortedLT_iff_pairwise` and `List.sortedLT_iff_isChain` in the Preorder
section of `Mathlib.Data.List.Sort`.

Derive distinctness of the **mapped key list** using the actual strict inorder
observation. Expose a convenient strict-key Nodup result. Payload distinctness
and injectivity of the key on the actual tree support can be demonstrated
through the existing `List.Nodup.of_map` and `inj_on_of_nodup_map` rather than
new global assumptions. No global key injectivity is permitted.

For `[PartialOrder κ]`, include the useful strict-key iff nondecreasing keys
plus distinct keys by reusing `List.sortedLT_iff_nodup_and_sortedLE`.
Preserve its antisymmetry requirement. The natural result shape is
`Ordered (fun a b => key a < key b) t ↔
 ((inorder t).map key).Nodup ∧ ((inorder t).map key).SortedLE`.
The preorder-only domain of the earlier strict facts cannot be silently
retained on this converse. Distinct full records are not distinct keys.

These laws formalize the common invariant observation. They neither supply
a source search comparator nor prove a search, update, balanced construction,
or lookup operation correct.

## 6. Actual ordinary and cached rotation adapters

The core `Ordered.lean` imports ordinary observations and appropriate pinned
list/order APIs, without importing rotations, cache resources, sorting
algorithms, or Examples. The separate `OrderedRotations.lean` may import
`Ordered` and XT06's ordinary/cached rotations.

For each actual successful `rotateLeft?` and `rotateRight?`, prove
`Ordered R t' ↔ Ordered R t` under the transitivity premise and the actual
success equation. Consume the existing successful inorder law or the new
inorder congruence law. Preserve the existing `none` failure semantics;
an ordered empty tree or singleton need not admit a rotation.

For arbitrary cached fringes A,B,C, payloads x,y, empty summary and node
summary operation, prove equivalence of erased-payload `Ordered R` for
`Cached.rebuildLeft` and `Cached.rebuildRight`, under transitivity.
Consume `Cached.inorder_erase_rebuildLeft_eq_rebuildRight` (or its actual
success interface). No `Cached.Valid`, balance, reassociation of summaries,
or callback cost hypothesis belongs to this erased ordering result.
Existing cache validity and cached-summary laws retain their own hypotheses.

No new operation, raw annotated-tree rotation, reannotation algorithm,
measured callback, tariff, shape/count proof or global cache-validity theorem
is introduced. Generic arbitrary-relation pairwise observations already
transport through exact inorder equality; they do not justify dropping
transitivity from the recursive-invariant adapters.

## 7. Connected cases and independent expectations

Develop theory and cases together through the repository example-driven
workflow. The following case families cover the substantive interfaces;
existing fixtures should be consumed where they suffice, without modifying
their established expectations. Cases remain uncompiled until the required
later matching validation; no scratch admissions enter the candidate.

### Positive order, empty domain and actual rotation

- Empty trees over arbitrary types, including `Empty`, satisfy the invariant.
  Singleton validity does not require `R a a`. Reuse existing empty-tree and
  failure-shape interfaces to retain the absence of a legal empty/singleton
  rotation, without inventing a label or a default result.
- A generic three-node chain of strict labels with premises `a < b` and
  `b < c` demonstrates satisfiable structural bounds and the inorder bridge.
- The printed p.59 fixture has root 6, left subtree rooted at 3 with children
  2 and 5, and right subtree rooted at 9 with left child 8. Its independently
  specified inorder is `[2,3,5,6,8,9]`. Connect strict order and key
  distinctness through public results; establish its actual left-rotation
  result and consume the new adapter and existing inverse. Existing XT06
  height-changing cases suffice; no new height/balance theorem is required.

### Exact failure of an overgeneralized relation law

Let `R a b := b = a + 1` on Nat and use root 1 with leaf children 0 and 2.
Prove its actual structural invariant, failure of pairwise R on its inorder,
and failure of the structural invariant after its actual legal left rotation.
The same triple witnesses nontransitivity. Preserve this expectation rather
than strengthening an unintended statement to hide the counterexample.

### Strict/weak and semantic-key distinctions

- Reuse the existing repeated-label `balancedThree`/`leftThree` fixture where
  suitable: its inorder `[1,1,1]` is weakly ordered but not a strict BST.
  This supports the p.54 hypothesis correction; the actual balancer remains
  a separate later algorithm obligation.
- Distinct full records `(1,10)` and `(1,20)` can be in explicit full-pair
  lexicographic order while their repeated keys violate strict key order.
  Show the actual mapped-key boundary and payload distinctness; no global
  product-order instance change is permitted.
- Retain a small local indiscrete preorder with two distinct elements (or an
  equivalent standard lifted-order instance) showing weak order plus Nodup
  does not imply strict order without antisymmetry. Keep any local order
  instance confined to this example; do not alter existing Bool/order APIs.
- A generic source-adjacency client uses the actual strict-key equivalence
  and the pinned `SortedLT`/`IsChain` bridge. The positive weak-plus-Nodup
  characterization must also be exercised through the public theorem.

### Mapping and independent cache validity

- A key-preserving payload map such as `(k,b) ↦ (k,())` from `Nat × Bool`
  to `Nat × Unit` is globally noninjective. Apply the actual transport law
  to a valid distinct-key tree; retain its full mapped inorder. An arbitrary
  key-collapsing constant map on a valid multi-node tree destroys strict order.
- Reuse `TreeCacheExamples.corrupt`, which erases to the ordered `sample`
  but fails `Cached.Valid`, and existing annotated repeated-label fixtures
  where cache validity holds but strict erased ordering fails. These expose
  the independence of the two predicates without a new cache executor.
- Exercise the new cached-rebuilding adapter on actual ordered erased
  fringes even when a retained fringe cache is invalid. One concrete choice
  is A=`corrupt`, x=4, B=empty, y=5, C=empty: both rebuilt erased inorders
  are `[0,1,2,3,4,5]`, yet the retained invalid fringe makes both cached
  reconstructions invalid by XT06's validity equivalences. Obtain the second
  ordering conclusion through the new adapter, not by two independent
  fixture computations.

## 8. Source correspondence and remaining obligations

The note and reconstruction map must describe one source-faithful structural
predicate and its stronger-general-domain observation laws. Record the exact
direction/hypotheses, strict versus weak ordering, mapped-key distinctness,
and actual successful-result premise for rotations. Source definition
equivalences and generic specializations are not theorems about physical
execution or an automatically verified source-language translator.

This unit supports C05-001 and the invariant/strict-list portion of C05-025,
the BST consequence of C05-043, strict key-order portions of C06-044/049,
and the invariant qualification for later C04-058. Keep every partial row
explicitly partial; a shared unit cannot close a chapter or waive an
unimplemented set-observation/algorithm obligation.

Still mandatory outside this unit: all-node triples and Exercise 5.1;
Exercise 5.3's direct recursive BST/set proofs without the inorder detour;
lookup/insert/delete and split-min, both deletion strategies, joins and
splitting, Set/Map interfaces and full refinement clients, balance and
height/cost bounds, interval order/cache/search, positioned rotations,
schedules/counts/distance, and all original subsequent chapter obligations.
The annotated map-value distinction and recorded manuscript corrections
remain visible. No earlier frozen requirement or finding is overwritten.

## 9. Validation, review and durable handoff

During the running Chapter 1 gate, all XT07 authoring is source-only.
No agent may run Lean, Lake, a compiler, project checker/hash helper, cache
experiment or another acceptance process. No source in the active Chapter 1
checkout is changed. Root alone owns any permitted Git branch/commit action
after the source authors stop.

Before committing a draft, read every changed claim and connected case,
record actual domains/hypotheses and unresolved elaboration risks, preserve
complete source provenance, and perform the ordinary diff checks in the
pinned shell. The draft handoff must identify the exact original base,
candidate, complete changed paths, source identities, actual dependencies,
public connections and unrun validation. Commit source progress so the
all-refs checkpoint can recover it; preserve local tickets/control as well.

After dependency acceptance and history-preserving integration, the full
immutable candidate needs the applicable guarded integrated build, all
source/coverage/version/integrity checks, exhaustive axiom audit, both
independent Standards and Spec axes on the full original frozen scope, and
immediate candidate-record verification before acceptance. Reuse retained
loops/history and applicable existing mode rulings; no evidence is waived.
Elaboration fixes retain the intended statements/cases and get a new commit
with matching validation. No `sorry`, `admit`, new axiom, unsafe/partial proof
escape, weakened warning policy or native decision shortcut is permitted.

Create, expose and immediately upload a pre-code durability checkpoint; do
the same for the committed draft and later substantial corrective/acceptance
milestones. Preserve every earlier receipt, finding and requirement. No
GitHub ticket, commit, pull request or remote push is authorized by this unit.
