# Enumeration frozen contract — Phase 2A

Frozen before either Enumeration source file exists. Status: UNCOMPILED intended interface, not an acceptance claim. This continues the original whole-Chapter-4 loop, whose base remains `298fb23eeaa22d0ca8fe2f1a5320da40a2eab3b2` and whose 76 obligations remain intact. Implementation starts at `106601ff0c6af392139786f0ad01a56e0dca96fb`. Earlier holds and source pairs are immutable inputs.

Source basis: C04-019/020, primary July27 2026 book PDF page55 (printed49), reread receipt a5a763. Inventory SHA-256 `e7e282df7f553cbe8a960d1e20818e09a04f63c2cf47a069284223ee3a8595e4`; PDF SHA-256 `9633e91729287dff6cff7c390546d8354b3f3d292fed3eb4cad2b66c891d1645`. No manuscript enters the deliverable.

## Carrier, algorithms, public names and exact contracts

All definitions are in `Trees`, with `{α : Type u}` and NO typeclass assumptions. Reuse the existing Mathlib `BinaryTree α` and `Trees.inorder`.

```
def insertFirst (x : α) : BinaryTree α → List (BinaryTree α)
-- nil => [node x nil nil]
-- node a l r => node x nil (node a l r) ::
--   (insertFirst x l).map (fun l' => node a l' r)

def removeFirst : BinaryTree α → BinaryTree α
-- nil => nil
-- node a nil r => r
-- node a l r, where l is a node => node a (removeFirst l) r

def enumTree : List α → List (BinaryTree α)
-- [] => [nil]
-- x::xs => (enumTree xs).flatMap (insertFirst x)

insertFirst_nil (x : α) : insertFirst x .nil = [.node x .nil .nil]
insertFirst_node (x a : α) (l r : BinaryTree α) :
  insertFirst x (.node a l r) = .node x .nil (.node a l r) ::
    (insertFirst x l).map (fun l' => .node a l' r)
removeFirst_node_of_ne_nil (a : α) (l r : BinaryTree α) (hl : l ≠ .nil) :
  removeFirst (.node a l r) = .node a (removeFirst l) r
nil_not_mem_insertFirst (x : α) (t : BinaryTree α) :
  (.nil : BinaryTree α) ∉ insertFirst x t
inorder_of_mem_insertFirst (x : α) {s t : BinaryTree α}
  (ht : t ∈ insertFirst x s) : inorder t = x :: inorder s
removeFirst_of_mem_insertFirst (x : α) {s t : BinaryTree α}
  (ht : t ∈ insertFirst x s) : removeFirst t = s
nodup_insertFirst (x : α) (t : BinaryTree α) : (insertFirst x t).Nodup
exists_insertFirst_of_inorder_cons (x : α) (xs : List α) (t : BinaryTree α)
  (ht : inorder t = x :: xs) :
  ∃ s, inorder s = xs ∧ t ∈ insertFirst x s
insertFirst_flatMap_nodup (x : α) (ts : List (BinaryTree α)) (hts : ts.Nodup) :
  (ts.flatMap (insertFirst x)).Nodup

enumTree_nil : enumTree ([] : List α) = [.nil]
enumTree_cons (x : α) (xs : List α) :
  enumTree (x :: xs) = (enumTree xs).flatMap (insertFirst x)
mem_enumTree_iff (xs : List α) (t : BinaryTree α) :
  t ∈ enumTree xs ↔ inorder t = xs
set_enumTree (xs : List α) :
  {t | t ∈ enumTree xs} = {t : BinaryTree α | inorder t = xs}
enumTree_nodup (xs : List α) : (enumTree xs).Nodup
```

The insertion and deletion recurse down the left subtree; enumeration recurses on the input tail. Termination is structural, not a postulated fuel bound. A unique deletion inverse separates insertion outputs from different predecessor trees; an empty versus nonempty left child separates the head insertion from the recursive alternatives. Constructor injectivity preserves distinctness within the mapped tail. Therefore the Nodup contract needs no label distinctness or decidable label equality. No Finset/Multiset-toList, noncomputable enumerator, admissions, new axioms, unsafe/partial code or native evaluation shortcuts are allowed. No runtime complexity theorem is asserted.

## Independent expected cases and checked-use plan

These expectations were first saved before Phase2 source at the previous hold and are unchanged:

- Empty labels: `enumTree ([] : List Empty) = [nil]`, and consume `enumTree_nodup` on that input.
- Arbitrary singleton `a` returns exactly `[node a nil nil]`.
- Arbitrary pair `[a,b]` returns exactly `[node a nil (node b nil nil), node b (node a nil nil) nil]`, in that order.
- Substitute `b=a`; both distinct shapes remain, and the displayed two-tree list is Nodup by the GENERAL `enumTree_nodup` law. No label-equality assumption may be added. Independently prove the two shapes unequal by their left children.
- For `[1,2,3]`, independently expected output order is: root1/right chain2,3; root2/leaves1,3; root1/right subtree root3/left leaf2; root3/left subtree root1/right leaf2; root3/left chain2,1. All five are present exactly once. Consume the general Nodup result for this input too.
- A balanced root9/left3/right7 belongs to `enumTree [3,9,7]` through `mem_enumTree_iff`. It is excluded from `enumTree [9,3,7]` through the same public equivalence and its independently calculated inorder.

Exact output reductions test the algorithm's order/shape semantics; positive/excluding membership and repeated-input Nodup must connect those examples to the universal laws. No fictional compiler red/green phase will be recorded. The actual initial evidence is the absent-interface baseline.

## Qualification boundary

Author provides committed source, complete authored public-name/header inventory, immutable SHA-256 identities, and source statement assessment. All source remains UNCOMPILED until root qualifies it. Root owns exact toolchain/pins, focused diagnostics, actual elaborated statements, full immutable candidate/audit, independent Standards/Spec reviews and immediate verification. Enumeration is not a separately accepted chapter or a new review loop. Reconstruction and every other Chapter4 obligation remain mandatory.
