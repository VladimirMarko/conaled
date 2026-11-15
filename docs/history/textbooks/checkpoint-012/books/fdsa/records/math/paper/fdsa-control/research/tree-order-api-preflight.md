# Shared ordered-tree observations: API preflight

Status: bounded source-only preparation, 2026-11-02. This report does not
activate a chapter, freeze implementation requirements, change a source
candidate, supply compilation evidence or accept a shared unit. The sole
Chapter 1 compiler/checker remains root-owned session 83124. No compiler,
Lean/Lake command, project checker/hash helper, Git/ref/cache operation or
remote operation was run for this assessment.

## 1. Evidence and proposed boundary

Read the governing AGENTS, architectural/domain guidance, glossary, ADRs 0001
and 0010, implementation and example-driven guidance including the worked
example, and the preservation-evolution criteria/inventory. This work remains
inside root's existing whole-book workflow. It introduces no new review loop.

Read the complete saved `Trees.Observations`, `Trees.Rotations`, `Trees.Cached`
and `Trees.CachedRotations` modules in `conaled-tree-rotations`, both frozen
XT01/XT06 requirements and their candidate handoffs. The retained XT01 candidate
is `64c6b777d828ecfe83234fc2aed94600a1f24297`; XT06 is
`28ba79d8d425400cb87d2daf3ecf1cc5a63a7aa2`. These identities come from the
retained handoffs, not a new Git check. Their source remains unvalidated.

Inspected the actual pinned Mathlib tree/list/order APIs, saved Lean list
sources, current project sorting observation, existing tree examples, and
the relevant Isabelle definitions. The manifest pins Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`; the retained Lean source pin is
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Isabelle source attribution remains
at mirror revision `f86f290225eebcc52c1ae7dba2e098f405f51c21`.

The reusable gap is small: a source-style recursive ordering predicate on
the existing `BinaryTree`, its precise connection to `List.Pairwise` of the
existing inorder observation, strict-key consequences, and adapters to the
already defined rotations. No new tree carrier, search executor, algebra
record, order class, SquareKit preservation framework or representation
conversion is needed. Lookup, insertion, deletion, balancing and all their
costs remain separate obligations.

## 2. Existing interfaces to consume

All tree declarations in this table are actual saved declarations, not
proposed names. Paths are relative to `conaled-tree-rotations`.

| Actual interface | Present contract and use |
| --- | --- |
| `BinaryTree.nil`, `BinaryTree.node`, `BinaryTree.map` | Mathlib `Data/Tree/Basic.lean` lines 31–34 and 75–78. Constructor order is label, left, right. The carrier admits empty trees without an inhabited payload. It has no existing BST/inorder ordering predicate to extend. |
| `Trees.inorder`, `inorder_nil`, `inorder_node` | `Applications/Trees/Observations.lean` lines 68–74. A node observes `inorder l ++ (a :: inorder r)`, retaining order and every duplicate occurrence. |
| `Trees.inorder_length`, `inorder_map` | Same file, lines 76–87. Length equals canonical node count; arbitrary label maps commute with inorder. |
| `Trees.inorder_of_rotateLeft?`, `inorder_of_rotateRight?` | `Applications/Trees/Rotations.lean` lines 85–98. Exact inorder equality follows from the actual success equation, with no label order assumption. |
| `Trees.map_rotateLeft?`, `map_rotateRight?` | Same file, lines 119–135. Arbitrary label maps commute with the partial operation, including failure. This alone does not say that an arbitrary label map preserves an ordered-tree predicate. |
| `Trees.Cached.erase`, `inorder_erase` | `Applications/Trees/Cached.lean` lines 15 and 89–91. Erasure is `BinaryTree.map Prod.fst`; inorder erasure is list mapping, unconditionally. |
| `Trees.Cached.erase_annotate` | Same file, lines 123–129. Annotation erases to the actual original tree, independent of any ordering or cache algebra law. |
| `Trees.Cached.inorder_erase_rebuildLeft_eq_rebuildRight` | `Applications/Trees/CachedRotations.lean` lines 94–102. The two smart reconstructions have equal erased payload inorder. Cache validity and equality of cached summaries are separate theorems. |
| `Applications.Sorting.KeySorted` | `Applications/Sorting/Stable.lean` lines 13–14. This is **weak** key ordering, `Pairwise (fun a b => key a ≤ key b)`. Preserve this existing meaning; it is not the strict BST invariant. |
| `Applications.Sorting.StableSort.map` | Same file, lines 77–85. An existing example of key-preserving payload maps with no global injectivity premise. It need not become a dependency of the tree core. |

The Mathlib carrier's `Inhabited (BinaryTree α)` instance chooses `nil`; it
does not require or provide `Inhabited α`. Avoid old deprecated `Tree` aliases.
`Trees.inorder` provides sufficient occurrence membership for a narrow
observation interface; a `Finset`, decidable payload equality, separately
bundled finite-set representation or new membership typeclass is unnecessary.

## 3. One structural predicate and the exact relation boundary

The following are proposed mathematical shapes, not elaborated declarations.
Use one source-style recursive predicate, provisionally `Trees.Ordered R`,
on arbitrary `R : α → α → Prop`:

```text
Ordered R nil = True
Ordered R (node a l r) =
  Ordered R l ∧ Ordered R r ∧
  (∀ x ∈ inorder l, R x a) ∧ (∀ y ∈ inorder r, R a y).
```

This is the same structural content as Isabelle `Tree.thy` lines 90–96;
conjunction order is an interface choice. The source bounds use `set_tree`;
`Tree.thy` line 392 connects that observation to inorder membership. Using
inorder membership here does not implement the separate direct recursive
set/BST proof exercises. In particular, C05-021 / Exercise 5.3 remains open
when its requested direct proof route has not been supplied.

No order law, equality decision, inhabitance, finite payload type or key
projection is needed to define this predicate. Keep nil and node equations
and a direct relation-monotonicity theorem: `R x y → S x y` for all x,y
transports `Ordered R t` to `Ordered S t`. That theorem needs no transitivity.
It is the generic counterpart of Isabelle `bst_wrt_mono` at lines 436–440.

For **arbitrary** R, the exact inorder node decomposition has five components:

```text
Pairwise R (inorder (node a l r)) ↔
  Pairwise R (inorder l) ∧ Pairwise R (inorder r) ∧
  (∀ x ∈ inorder l, R x a) ∧
  (∀ y ∈ inorder r, R a y) ∧
  (∀ x ∈ inorder l, ∀ y ∈ inorder r, R x y).
```

The last cross-subtree condition cannot simply be omitted. Consequently:

| Proposed law | Sufficient and appropriately narrow hypotheses |
| --- | --- |
| `Pairwise R (inorder t) → Ordered R t` | None on R; recursive decomposition supplies all required comparisons. |
| `Ordered R t → Pairwise R (inorder t)` | Transitivity of R suffices: each left/root and root/right comparison gives the missing left/right comparison. |
| `Ordered R t ↔ Pairwise R (inorder t)` | The same transitivity premise; no reflexivity, totality, irreflexivity or decidability is needed. |
| `Ordered R t → (inorder t).Nodup` | Asymmetry suffices by direct tree induction. Transitivity plus irreflexivity is a convenient sufficient route through the pairwise bridge. |

Use either an explicit `Transitive R` argument or existing `[IsTrans α R]`
according to the chosen local style. These are existing propositions/classes,
not a reason to define another order interface. Pinned Mathlib
`Order/Defs/Unbundled.lean` lines 23–30 relates `IsTrans` and `Trans`; lines
50–51 define the existing `IsStrictOrder` from transitivity and irreflexivity.
An explicit law can avoid needless instance setup for a local custom relation.

The transitivity assumption is not a universal logical necessity on every
particular finite tree; it is a uniform sufficient law for the stated generic
equivalence. A node-local theorem may retain the actual cross-subtree premise.
Do not describe transitivity as an iff characterization of when one tree works.

The separate distinctness consequence has a weaker direct route. Under
asymmetry, duplicate occurrences across the left and right subtrees would give
both `R x a` and `R a x`; a root repeated in either subtree would give `R a a`.
Both contradict asymmetry, and child distinctness follows inductively.
Existing list Nodup append/cons and disjointness facts suffice. Thus, if a
standalone generic distinctness theorem is exposed, do not describe
transitivity as its necessary law. This refinement does not alter the
transitivity boundary for the full ordered-inorder equivalence.
It is a hypothesis-minimality note, not an additional proposed deliverable:
the intended strict-key Nodup client can use its preorder and the actual
inorder bridge.

**Independent boundary:** let `R a b` mean `b = a + 1`, and let t have root 1
and singleton children 0 and 2. Its recursive root bounds hold, but its inorder
`[0,1,2]` is not pairwise R, because R 0 2 fails. The legal left rotation also
fails `Ordered R`, since the new root 2 must bound the retained label 0. This
one case distinguishes both invalid unqualified generalizations. It is a
hand-derived expected Lean case, not newly checked source.

## 4. Exact pinned list proof routes

The saved Lean files identify the actual core APIs. The proof strategies below
are source-level feasibility assessments; their tactics have not been run.

| Actual API and source location | Relevant shape |
| --- | --- |
| `List.pairwise_cons`, `book-source/LeanList-Basic.lean` 1378–1379 | `Pairwise R (a :: xs) ↔ (∀ b ∈ xs, R a b) ∧ Pairwise R xs`. |
| `List.pairwise_append`, `book-source/LeanList-Pairwise.lean` 170–173 | Pairwise of append iff pairwise of each side and all forward cross comparisons. |
| `List.Pairwise.sublist`, same file 47–50 | A sublist inherits pairwise ordering. The theorem's explicit sublist proof precedes its pairwise proof; method notation already appears in project code. |
| `List.Pairwise.imp`, `imp_of_mem`, same file 52–55 and 68–75 | Relation implication transports pairwise facts; the latter only needs implication on actual members of the list. |
| `List.pairwise_map`, same file 128–131 | Pairwise of the mapped list iff pairwise for the pulled-back relation. No injectivity or equality decision is involved. |
| `List.Pairwise.map`, `of_map`, same file 133–140 | Forward transport uses relation preservation; reverse transport uses relation reflection. |
| `List.Pairwise.nodup`, Mathlib `Data/List/Nodup.lean` 28–30 | Irreflexive pairwise lists are Nodup. Its existing instance assumption is `[Std.Irrefl R]`. |
| `List.Nodup.of_map`, same file 187–188 | Nodup of mapped keys implies Nodup of the original payload list, without requiring global injectivity of key. |
| `List.inj_on_of_nodup_map`, same file 194–204 | Key equality implies payload equality **on the actual list support** when its mapped keys are Nodup. |
| `List.sortedLT_iff_pairwise`, `sortedLE_iff_pairwise`, Mathlib `Data/List/Sort.lean` 407–424 | Available in the `[Preorder α]` section; use these instead of another sorted-list definition. |
| `List.SortedLT.sortedLE`, `List.SortedLT.nodup`, same file 486–492 | Strict ordering implies weak ordering and distinctness over a preorder. |
| `List.sortedLT_iff_nodup_and_sortedLE`, same file 626–638 | The converse is in the **`[PartialOrder α]`** section. |

For the generic equivalence, induct on the actual tree and rewrite only its
inorder node equation plus `pairwise_append`/`pairwise_cons`. In the forward
structural-to-list direction discharge left/right comparisons with the
transitivity law through the root. In the reverse direction project the child
pairwise facts and root bounds, then invoke the induction hypotheses. This
uses ordinary structural induction, with no custom induction or proof system.

Existing `Observations` already imports list basics; additional imports should
match the accepted surface. If the weak-plus-Nodup bridge is included, use
`Mathlib.Data.List.Sort` for its existing theorem instead of rebuilding it.
For a relation-only subset, `Mathlib.Data.List.Nodup` and the relevant standard
order definitions are narrower. Exact import sufficiency still requires later
focused compilation. No `Examples`, project sorting implementation, resource
module or balance algorithm should be imported into the ordered-tree core.

## 5. Strict key observations without unnecessary payload structure

Use arbitrary `key : α → κ`, with independent payload/key universes. A thin
strict-key convenience can specialize `Ordered` to
`fun a b => key a < key b`; it need not introduce a second recursive predicate.

For `[Preorder κ]`, `<` is transitive and irreflexive. Pinned
`Order/Defs/PartialOrder.lean` lines 43–61, 86 and 97 expose this exact scope
and the bridge to `Std.IsPreorder`. Thus the strict-key predicate is equivalent
to `((inorder t).map key).Pairwise (· < ·)` by the generic theorem and
`List.pairwise_map`. It is also equivalent to that mapped list's `SortedLT`.
Linearity, payload ordering, payload equality decisions and global key
injectivity are unnecessary for these observation facts.

Derive distinct **keys** first using the existing irreflexive pairwise/Nodup
API. This implies payload Nodup via `Nodup.of_map key`, and key equality
identifies payloads on this actual tree via `inj_on_of_nodup_map`.
These are local consequences, not a claim that `key` is globally injective.
No occurrence count, filter-based lookup or finite-map representation needs to
be introduced just to express them.

For `[PartialOrder κ]`, reuse `sortedLT_iff_nodup_and_sortedLE` on the mapped
key list to obtain the strict-key iff weak-key-and-distinct-keys bridge.
Its weak observation may be expressed directly by `Pairwise` and connected
to existing `Applications.Sorting.KeySorted` in a client. Keep the core free
of an unnecessary dependency on that project sorting module.

Two boundary distinctions are essential:

1. On a preorder with two distinct but order-equivalent elements, a two-element
   list can be weakly sorted and Nodup without being strictly sorted. The
   reverse bridge needs antisymmetry or an equivalent explicit separation
   law. A mere preorder must not be retained on that converse.
2. Payload Nodup does not replace mapped-key Nodup. Distinct records
   `(1,false)` and `(1,true)` have distinct payloads and weakly sorted keys,
   but their equal keys violate the strict BST invariant even over Nat.

The manuscript's adjacent strict-order recursion and Isabelle's all-pairs
`sorted_wrt (<)` are equivalent under the intended order law, not for every
relation. `book-source/Sorted_Less.thy` lines 9–23 explicitly hides ordinary
weak `sorted`, introduces strict `sorted_wrt (<)`, and installs adjacent rules
using transitivity. `Tree_Map.thy` uses `sorted1`; `AList_Upd_Del.thy` line 9
defines that as strict ordering of `map fst`. Full payload pairs remain in
the semantic inorder; do not sort or compare cached product labels
lexicographically when the intended key is the first component.

## 6. Label maps: preservation, reflection and key erasure

An exact structural pullback law is available without any relation laws:

```text
Ordered S (t.map f) ↔ Ordered (fun x y => S (f x) (f y)) t.
```

Prove it by tree induction, the node predicate equation and `inorder_map`,
using ordinary membership in a mapped list. This is stronger in generality
than routing every map fact through the transitive inorder theorem.

From this one law and relation implication, a map preserving the source
relation gives forward ordering preservation. An iff between two different
relations needs reflection as well as preservation. Injectivity alone does
not preserve an order. Likewise, arbitrary noninjective maps can collapse
distinct keys and destroy strict ordering.

For payload maps with `key' (f x) = key x`, the pulled-back relation is exactly
unchanged. Therefore strict-key ordering is preserved **and reflected**,
without global injectivity of f or key. Example: erase the Boolean component
from Nat × Bool. That map is globally noninjective, while a valid tree using
distinct Nat keys retains all its key ordering. Two payloads with the same
key cannot both occur in the valid input; this is a derived support fact,
not a global premise on the carrier.

If keys themselves are transformed, `StrictMono g` gives forward strict-order
preservation between preorders. Do not silently turn it into an iff there.
Pinned `OrderEmbedding.sortedLT_listMap` works over preorders
(`Data/List/Sort.lean` 815–827), while the `StrictMono.sortedLT_listMap` iff
explicitly requires a **linear** source order (859–871). The general interface
can use explicit relation reflection or an existing OrderEmbedding when an
iff is needed; it need not force linearity on every forward transport.

## 7. Small adapters for ordinary and cached rotations

A separate `Applications/Trees/OrderedRotations.lean` can import the proposed
ordered core plus the existing ordinary/cached rotation modules. This keeps
the basic ordering interface dependent only on XT01 observations and ordinary
list/order mathematics, with XT06 needed only by the adapters.

For a transitive R and `rotateLeft? t = some t'`, derive
`Ordered R t' ↔ Ordered R t` by the pairwise equivalence and
`inorder_of_rotateLeft?`. The right counterpart uses the actual right law.
No balance, nonempty-payload, cache-validity or root-summary hypothesis is
needed. Retain the actual successful result premise: the failure cases remain
`none`, not identity rotations or default trees.

The same reasoning with
`inorder_erase_rebuildLeft_eq_rebuildRight` gives equivalence of the erased
payload ordering of both smart reconstructions. This equivalence is
unconditional on cached annotations or cache validity; transitivity is needed
only for interpreting the structural relation predicate through inorder.
Ordering of full payload/annotation pairs would be a different statement and
need not be preserved when the two annotations are rebuilt.

Annotation and erasure clients need no new operation: use the exact key
pullback law or `erase_annotate` to transport ordering. Keep
`Trees.Cached.Valid` as the separate recursive annotation contract. The
existing `TreeCacheExamples.corrupt` erases to `sample` with inorder
`[0,1,2,3]` while failing cache validity (`Examples/TreeCache.lean` 190–207),
so it is a ready-made example that ordered payloads do not validate summaries.

## 8. Connected expected cases and limits

These are intended public connections for a future scope freeze, not compiled
claims or a per-declaration quota. Root owns the final independent case set.

| Existing or independently derived case | Connection it should exercise |
| --- | --- |
| `TreeCacheExamples.sample`, inorder `[0,1,2,3]` | Strict Nat ordering via the generic equivalence; distinct mapped keys; no need to invent another positive tree fixture. |
| Existing `balancedThree` / `leftThree`, inorder `[1,1,1]` | Weak ordering can hold while strict ordering fails; existing successful rotation preserves the same observation. |
| Root 1 with leaves 0 and 2 under successor relation | The transitivity boundary for structural/list equivalence and rotation preservation. |
| Distinct same-key pairs `(1,false)`, `(1,true)` | Payload distinctness cannot stand in for distinct keys. |
| A distinct-key Nat × Bool tree mapped by `Prod.fst` | Key-preserving map is globally noninjective yet preserves and reflects the ordered observation. |
| Indiscrete preorder on two unequal elements | Weak ordering plus Nodup does not imply strict ordering without antisymmetry. |
| Actual legal rotation of an ordered tree | Consume the saved success equation and new adapter, retaining exact inorder and no balance claim. |
| Existing `corrupt` versus its erased `sample` | Ordered payloads and cache validity remain independent; no annotation repair is executed by a proof observation. |
| Arbitrary `BinaryTree Empty` | Only nil is possible; ordering is true with no default label, but there is no legal root rotation. |

No new list-sorting algorithm is needed. Source-level ordering does not
establish lookup correctness, insertion/deletion refinement, key comparison
costs, logarithmic height, balancing, positioned rotation schedules, tree
shape uniqueness or cached-summary correctness. Those remain in the original
chapter/shared tickets. Inorder equality also does not reconstruct tree shape;
the existing height counterexample already demonstrates that limitation.

## 9. Exact inspected identities

Ordinary byte hashes below identify the inspected files. Mathlib paths are
within `conaled/.lake/packages/mathlib`; tree/project paths are within
`conaled-tree-rotations`. Hashing did not run the project's integrity tooling.
Only relevant API regions of the large dependency/source files were read;
the four tree modules and frozen XT01/XT06 requirements were read completely.

| File | Bytes | Lines | SHA-256 |
| --- | ---: | ---: | --- |
| `Applications/Trees/Observations.lean` | 4119 | 107 | `c8fe22a39c7e690b05af3d2baa23df9ad8a55a179a165df0de7dd20171f4b752` |
| `Applications/Trees/Rotations.lean` | 7436 | 181 | `d9a9aef015fbe2c3ffcc638ea8b963784adaec4d88d9b500b5a5f148264407b3` |
| `Applications/Trees/Cached.lean` | 5668 | 135 | `f84b3c9702d26ed2490b1b711ea97df579561ee11c8d329550ef5f77a1d4b5d6` |
| `Applications/Trees/CachedRotations.lean` | 7146 | 137 | `42dfd73e40f34c4e92de1def37dd877127bba061126e4102cc3b483d6dd2b9fc` |
| `Applications/Sorting/Stable.lean` | 3704 | 87 | `288552150aa002c60ed06c74e69510112cf9b4e2f0045da3d98ca5c39264d881` |
| `Mathlib/Data/Tree/Basic.lean` | 6679 | 188 | `43f201537013e2824d18f6b66f6d329f15bc52289c1ae734fa8acd4bd2a9945d` |
| `Mathlib/Data/List/Nodup.lean` | 16643 | 400 | `dd189100bddbb41c32991672a727d0a3ebc41e7243f390cfa25c348eb0520432` |
| `Mathlib/Data/List/Sort.lean` | 35291 | 901 | `bc2fe8a7888a1298dc605ce769915c7bd5cefcb5db7de9cad5215d898d21abd9` |
| `Mathlib/Order/Defs/PartialOrder.lean` | 8515 | 228 | `c551e636b3f853c46203252d509fda76cca57072cfd5644e28e2496296cc5a48` |
| `Mathlib/Order/Defs/Unbundled.lean` | 16795 | 419 | `b0dcb2909e312447423cf4434ad84618fe3fdc27a0e4bf37ebe1afebf3fcb706` |
| `book-source/LeanList-Basic.lean` | 86754 | 2622 | `566e74dd5c3e72b2111af000b8bd1552f1aaffe29be317ba01bc91c9e5b55293` |
| `book-source/LeanList-Pairwise.lean` | 17626 | 405 | `fcc984c70a81216c178d42a858dea5e3640201023a9a4d2837e76f138fd9b0f4` |
| `book-source/Tree.thy` | 17104 | 489 | `1060e49bbc11b2e974d3a25668a09eff441180f8aad8b67f2444ba33a8a61af9` |
| `book-source/Sorted_Less.thy` | 2133 | 62 | `971199401fc20cd378ad3ca9c22c314bba146e44b5730dcc718a2b0f6f6a52d5` |
| `book-source/Tree_Set.thy` | 3801 | 119 | `f5f9d884c9e6bf5e442f9c6f07cba2c94729c0d8a29681a6da6fe70eff865c9b` |
| `book-source/Tree_Map.thy` | 2028 | 58 | `c6da2fe6f47b788e0a110a35bbe6ad7fe14d01d5878b263f21ecb01046f5da43` |
| `book-source/AList_Upd_Del.thy` | 6194 | 165 | `42f603405ff3fec058ba284c76183924139c42711ec66edaf623bd5b0a921f9a` |
| `reviews/binary-tree-cache-requirements.md` | 14576 | 259 | `81260794bec3767bb9eaa2d2fcaa8337da015220df60bf4dda147590c8ed23ce` |
| `reviews/tree-rotation-requirements.md` | 15484 | 272 | `b194b8888b812416520fe6cf4dc23793b5059a7f2a990246adea172606918fed` |

## 10. Preparation outcome

The narrow interface is feasible using the actual existing observations and
pinned list APIs. The substantive hypothesis boundaries are explicit above:
transitivity for structural-to-inorder ordering, irreflexivity for the
pairwise-to-Nodup consequence, antisymmetry for weak-plus-Nodup converses,
and reflection for transport iff claims. The separate direct asymmetry route
is retained as a minimality note. The strict-key specialization needs no
global key injectivity or payload order/equality/inhabitance assumptions.

No existing source-level interface defect was identified. This is not final
Standards or Spec review. Proposed proof scripts, import sufficiency, typeclass
inference, independent universes and linter behavior remain uncompiled.
Only this report was written; all candidates, frozen requirements, source
inventories, ticket statuses, previous reports and acceptance gates are unchanged.
