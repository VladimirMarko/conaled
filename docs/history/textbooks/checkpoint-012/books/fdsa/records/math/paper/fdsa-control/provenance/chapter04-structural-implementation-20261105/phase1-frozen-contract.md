# Frozen structural observations contract

This contract is frozen before authoring the two Phase 1 source files. It belongs to the existing Chapter 4 whole-task loop, whose original base is `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2` and whose complete 76-row inventory remains unchanged. The author branch starts at `90469ce4ba3fc49397d369a5db7d58aec7014f58`; XT01 is present as an unaccepted development prerequisite. No compiler or acceptance claim is made here.

## Shared carrier and operations

Use Mathlib `BinaryTree α`, with arbitrary `α : Type u`. No `DecidableEq α`, ordering, `Inhabited α`, or finiteness class is assumed. Reuse `Trees.inorder`, Mathlib map, node/leaf counts and height. Do not add minimum-height or shape-bound wrappers.

In namespace `Trees`, reserve these public operations and equations:

```lean
setTree : BinaryTree α → Set α
setTree_nil : setTree (.nil : BinaryTree α) = ∅
setTree_node (a : α) (l r : BinaryTree α) :
  setTree (.node a l r) = setTree l ∪ {a} ∪ setTree r
preorder : BinaryTree α → List α
preorder_nil : preorder (.nil : BinaryTree α) = []
preorder_node (a : α) (l r : BinaryTree α) :
  preorder (.node a l r) = a :: (preorder l ++ preorder r)
```

`setTree` is independently defined by structural recursion into `Set`, not as the set of the inorder list. `preorder` structurally visits root, left, then right, retaining duplicates. The needed independent bridges and transport laws are:

```lean
mem_inorder_iff_mem_setTree (x : α) (t : BinaryTree α) :
  x ∈ inorder t ↔ x ∈ setTree t
mem_preorder_iff_mem_setTree (x : α) (t : BinaryTree α) :
  x ∈ preorder t ↔ x ∈ setTree t
preorder_length (t : BinaryTree α) : (preorder t).length = t.numNodes
preorder_map (label : α → β) (t : BinaryTree α) :
  preorder (t.map label) = (preorder t).map label
```

## Structural containment

`Trees.Subtree : BinaryTree α → BinaryTree α → Prop` is inductive, with exact constructor names and argument order:

```lean
Subtree.refl (t : BinaryTree α) : Subtree t t
Subtree.left {s l r : BinaryTree α} (a : α) :
  Subtree s l → Subtree s (.node a l r)
Subtree.right {s l r : BinaryTree α} (a : α) :
  Subtree s r → Subtree s (.node a l r)
```

The smaller tree is the first argument. This relation denotes a whole rooted descendant subtree, not a pruned tree or a tree with the same label set. Reserve:

```lean
nil_subtree (t : BinaryTree α) : Subtree .nil t
subtree_nil_iff (s : BinaryTree α) : Subtree s .nil ↔ s = .nil
subtree_node_iff (s : BinaryTree α) (a : α) (l r : BinaryTree α) :
  Subtree s (.node a l r) ↔
    s = .node a l r ∨ Subtree s l ∨ Subtree s r
Subtree.trans {s t u : BinaryTree α} (hst : Subtree s t)
  (htu : Subtree t u) : Subtree s u
subtrees (t : BinaryTree α) : Set (BinaryTree α) := {s | Subtree s t}
mem_subtrees_iff {s t : BinaryTree α} : s ∈ subtrees t ↔ Subtree s t
subtrees_nil : subtrees (.nil : BinaryTree α) = {.nil}
subtrees_node (a : α) (l r : BinaryTree α) :
  subtrees (.node a l r) = {.node a l r} ∪ subtrees l ∪ subtrees r
self_mem_subtrees (t : BinaryTree α) : t ∈ subtrees t
nil_mem_subtrees (t : BinaryTree α) : (.nil : BinaryTree α) ∈ subtrees t
```

The constructors supply reflexivity and descent without adding redundant wrappers. The set recurrences prove the book correspondence of the independently exposed relation and set observation.

## Independently expected cases and public connections

The source's three-node sample has root 9, left child 3 and right child 7. Expected preorder is `[9,3,7]`, inorder `[3,9,7]`, label set `{3,9,7}`, and node count/preorder length 3. Examples will connect these to the public recurrence, membership, length, map and containment theorems. Mapping every label to 5 must give preorder `[5,5,5]`, showing that the map law has no injectivity requirement.

A root 5 with a left child 5 and a root 5 with a right child 5 both have traversals `[5,5]` and label set `{5}`, but the left-shaped tree is not a structural subtree of the right-shaped tree. This case distinguishes structural containment from label-set equality and preserves repeated labels. Empty observations will also be instantiated at `BinaryTree Empty`, exposing accidental inhabited-label assumptions. A nested containment example will explicitly consume `Subtree.trans`.

These are statements and intended proof connections. Examples become checked evidence only after the root's qualified compilation and required review/audit gates. No artificial failed compiler attempt is manufactured.

## Ownership and evidence

Phase 1 writes only `Applications/Trees/BasicObservations.lean`, `Examples/TreeBasicObservations.lean`, and new reports in this provenance directory. Root owns the entrypoint, correspondence/map, all other controls and compilation. Phase 2 will begin only after the Phase 1 source commit, in the separately assigned weighted-path files. Source identities, public declaration inventories and mathematical statement assessment will accompany each immutable candidate. The original two root records and all earlier preparation artifacts remain unchanged.
