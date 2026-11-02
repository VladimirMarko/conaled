import Applications.Trees.OrderedRotations
import Examples.TreeRotations
import Mathlib.Order.Basic

/-! Connected ordered-tree cases and boundaries. The printed six-label tree,
nontransitive successor relation, repeated keys and invalid retained cache
fringe have independent expectations. Source and statement assessment:
`docs/research/fdsa-tree-order.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace OrderedTreeExamples
universe u v w
variable {α : Type u} {β : Type v} {κ : Type w}

/-- Ordering does not supply a missing rotation pivot. -/
theorem empty_case (R : α → α → Prop) :
    Trees.Ordered R (.nil : BinaryTree α) ∧
      Trees.rotateLeft? (.nil : BinaryTree α) = none ∧
      Trees.rotateRight? (.nil : BinaryTree α) = none :=
  ⟨Trees.ordered_nil R, Trees.rotateLeft?_nil, Trees.rotateRight?_nil⟩

theorem empty_payload (R : Empty → Empty → Prop) (t : BinaryTree Empty) :
    Trees.Ordered R t ∧ Trees.rotateLeft? t = none ∧ Trees.rotateRight? t = none := by
  refine ⟨?_, TreeRotationExamples.empty_payload t⟩
  rw [TreeCacheExamples.empty_tree t]
  exact Trees.ordered_nil R

/-- No reflexive comparison of the single label is needed. -/
theorem singleton_ordered (R : α → α → Prop) (a : α) :
    Trees.Ordered R (TreeRotationExamples.singletonTree a) := by
  simp [TreeRotationExamples.singletonTree]

theorem singleton_case (R : α → α → Prop) (a : α) :
    Trees.Ordered R (TreeRotationExamples.singletonTree a) ∧
      Trees.rotateLeft? (TreeRotationExamples.singletonTree a) = none ∧
      Trees.rotateRight? (TreeRotationExamples.singletonTree a) = none :=
  ⟨singleton_ordered R a, TreeRotationExamples.missing_pivots .nil a a .nil⟩

def three (a b c : α) : BinaryTree α :=
  .node b (TreeRotationExamples.singletonTree a) (TreeRotationExamples.singletonTree c)

def threeAfter (a b c : α) : BinaryTree α :=
  .node c (.node b (TreeRotationExamples.singletonTree a) .nil) .nil

theorem three_inorder (a b c : α) : Trees.inorder (three a b c) = [a, b, c] := rfl

theorem three_left (a b c : α) :
    Trees.rotateLeft? (three a b c) = some (threeAfter a b c) :=
  Trees.rotateLeft?_node_node (TreeRotationExamples.singletonTree a) b .nil c .nil

theorem threeAfter_inorder (a b c : α) :
    Trees.inorder (threeAfter a b c) = [a, b, c] :=
  (Trees.inorder_of_rotateLeft? _ _ (three_left a b c)).trans (three_inorder a b c)

theorem three_strict_ordered [Preorder α] (a b c : α) (hab : a < b) (hbc : b < c) :
    Trees.Ordered (fun x y => x < y) (three a b c) := by
  apply Trees.ordered_of_pairwise_inorder
  rw [three_inorder]
  simp [List.pairwise_cons, hab, hbc, lt_trans hab hbc]

/-- The printed p.59 tree has six labels; the root is 6, not the maximum. -/
def printedTree : BinaryTree Nat :=
  .node 6
    (.node 3 (TreeRotationExamples.singletonTree 2) (TreeRotationExamples.singletonTree 5))
    (.node 9 (TreeRotationExamples.singletonTree 8) .nil)

def printedAfter : BinaryTree Nat :=
  .node 9
    (.node 6
      (.node 3 (TreeRotationExamples.singletonTree 2) (TreeRotationExamples.singletonTree 5))
      (TreeRotationExamples.singletonTree 8))
    .nil

theorem printed_inorder : Trees.inorder printedTree = [2, 3, 5, 6, 8, 9] := rfl

theorem printed_ordered : Trees.Ordered (fun a b : Nat => a < b) printedTree := by
  apply Trees.ordered_of_pairwise_inorder
  rw [printed_inorder]
  decide

theorem printed_keys_nodup :
    ((Trees.inorder printedTree).map (fun n : Nat => n)).Nodup :=
  Trees.ordered_key_nodup (fun n : Nat => n) printedTree printed_ordered

theorem printed_left : Trees.rotateLeft? printedTree = some printedAfter :=
  Trees.rotateLeft?_node_node
    (.node 3 (TreeRotationExamples.singletonTree 2) (TreeRotationExamples.singletonTree 5))
    6 (TreeRotationExamples.singletonTree 8) 9 .nil

theorem printed_right : Trees.rotateRight? printedAfter = some printedTree :=
  Trees.rotateRight?_of_rotateLeft? printedTree printedAfter printed_left

theorem printedAfter_inorder : Trees.inorder printedAfter = [2, 3, 5, 6, 8, 9] :=
  (Trees.inorder_of_rotateLeft? printedTree printedAfter printed_left).trans printed_inorder

theorem printedAfter_ordered : Trees.Ordered (fun a b : Nat => a < b) printedAfter :=
  (Trees.ordered_rotateLeft?_iff _ (fun _ _ _ hab hbc => lt_trans hab hbc)
    printedTree printedAfter printed_left).2 printed_ordered

theorem printed_inverse_order :
    Trees.Ordered (fun a b : Nat => a < b) printedTree ↔
      Trees.Ordered (fun a b : Nat => a < b) printedAfter :=
  Trees.ordered_rotateRight?_iff _ (fun _ _ _ hab hbc => lt_trans hab hbc)
    printedAfter printedTree printed_right

/-- Immediate succession has both root bounds on 0,1,2 but lacks the 0-to-2 comparison. -/
def next (a b : Nat) : Prop := b = a + 1

theorem next_not_transitive : ¬ Transitive next := by
  intro h
  have h02 : next 0 2 := h (show next 0 1 from rfl) (show next 1 2 from rfl)
  exact (by decide : ¬ next 0 2) h02

theorem next_ordered : Trees.Ordered next (three 0 1 2) := by
  simp [three, TreeRotationExamples.singletonTree, next]

theorem next_not_pairwise : ¬ (Trees.inorder (three 0 1 2)).Pairwise next := by
  rw [three_inorder]
  decide

theorem next_rotates : Trees.rotateLeft? (three 0 1 2) = some (threeAfter 0 1 2) :=
  three_left 0 1 2

theorem next_rotated_inorder : Trees.inorder (threeAfter 0 1 2) = [0, 1, 2] :=
  threeAfter_inorder 0 1 2

theorem next_rotated_not_ordered : ¬ Trees.Ordered next (threeAfter 0 1 2) := by
  intro h
  have h02 : next 0 2 :=
    ((Trees.ordered_node next 2
      (.node 1 (TreeRotationExamples.singletonTree 0) .nil) .nil).1 h).2.2.1 0 (by decide)
  exact (by decide : ¬ next 0 2) h02

theorem repeated_inorder :
    Trees.inorder TreeCacheExamples.balancedThree = [1, 1, 1] := rfl

theorem repeated_left_inorder : Trees.inorder TreeCacheExamples.leftThree = [1, 1, 1] :=
  TreeCacheExamples.same_inorder_different_height.1.symm.trans repeated_inorder

theorem repeated_weak :
    (Trees.inorder TreeCacheExamples.balancedThree).SortedLE ∧
      (Trees.inorder TreeCacheExamples.leftThree).SortedLE := by
  rw [repeated_inorder, repeated_left_inorder]
  have h : ([1, 1, 1] : List Nat).SortedLE :=
    List.sortedLE_iff_pairwise.mpr (by decide)
  exact ⟨h, h⟩

theorem repeated_weak_ordered :
    Trees.Ordered (fun a b : Nat => a ≤ b) TreeCacheExamples.balancedThree :=
  Trees.ordered_of_pairwise_inorder _ _ (List.sortedLE_iff_pairwise.mp repeated_weak.1)

theorem repeated_not_strict :
    ¬ Trees.Ordered (fun a b : Nat => a < b) TreeCacheExamples.balancedThree := by
  intro h
  have hn := Trees.ordered_key_nodup (fun n : Nat => n) TreeCacheExamples.balancedThree h
  change ([1, 1, 1] : List Nat).Nodup at hn
  exact (by decide : ¬ ([1, 1, 1] : List Nat).Nodup) hn

theorem repeated_left_not_strict :
    ¬ Trees.Ordered (fun a b : Nat => a < b) TreeCacheExamples.leftThree := by
  intro h
  exact repeated_not_strict
    ((Trees.ordered_rotateLeft?_iff _ (fun _ _ _ hab hbc => lt_trans hab hbc)
      TreeCacheExamples.balancedThree TreeCacheExamples.leftThree
      TreeRotationExamples.balanced_left).1 h)

/-- Full-record lexicographic order remains explicit; it is not a product-order instance. -/
def pairLex (p q : Nat × Nat) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

def sameKeyRecords : BinaryTree (Nat × Nat) :=
  .node (1, 10) .nil (TreeRotationExamples.singletonTree (1, 20))

theorem sameKeyRecords_inorder :
    Trees.inorder sameKeyRecords = [(1, 10), (1, 20)] := rfl

theorem sameKeyRecords_keys : (Trees.inorder sameKeyRecords).map Prod.fst = [1, 1] :=
  congrArg (List.map Prod.fst) sameKeyRecords_inorder

theorem sameKeyRecords_distinct : (Trees.inorder sameKeyRecords).Nodup := by
  rw [sameKeyRecords_inorder]
  decide

theorem sameKeyRecords_lex_ordered : Trees.Ordered pairLex sameKeyRecords := by
  apply Trees.ordered_of_pairwise_inorder
  rw [sameKeyRecords_inorder]
  decide

theorem sameKeyRecords_not_key_ordered :
    ¬ Trees.Ordered (fun p q : Nat × Nat => p.1 < q.1) sameKeyRecords := by
  intro h
  have hn := Trees.ordered_key_nodup Prod.fst sameKeyRecords h
  rw [sameKeyRecords_keys] at hn
  exact (by decide : ¬ ([1, 1] : List Nat).Nodup) hn

/-- The local order identifies two distinct values. Antisymmetry is essential
for recovering strict order from weak order and distinctness. -/
theorem antisymmetry_boundary :
    letI : Preorder Bool := Preorder.lift (fun _ : Bool => (0 : Nat))
    ([false, true] : List Bool).SortedLE ∧
      ([false, true] : List Bool).Nodup ∧
      ¬ ([false, true] : List Bool).SortedLT := by
  letI : Preorder Bool := Preorder.lift (fun _ : Bool => (0 : Nat))
  change ([false, true] : List Bool).SortedLE ∧
    ([false, true] : List Bool).Nodup ∧ ¬ ([false, true] : List Bool).SortedLT
  refine ⟨?_, by decide, ?_⟩
  · apply List.sortedLE_iff_pairwise.mpr
    change ([false, true] : List Bool).Pairwise (fun _ _ => (0 : Nat) ≤ 0)
    decide
  · intro h
    have hp := List.sortedLT_iff_pairwise.mp h
    change ([false, true] : List Bool).Pairwise (fun _ _ => (0 : Nat) < 0) at hp
    exact (by decide : ¬ ([false, true] : List Bool).Pairwise
      (fun _ _ => (0 : Nat) < 0)) hp

theorem adjacent_keys [Preorder κ] (key : α → κ) (t : BinaryTree α) :
    Trees.Ordered (fun a b => key a < key b) t ↔
      List.IsChain (fun a b : κ => a < b) ((Trees.inorder t).map key) :=
  (Trees.ordered_key_iff_sortedLT key t).trans List.sortedLT_iff_isChain

theorem distinct_payloads [Preorder κ] (key : α → κ) (t : BinaryTree α)
    (h : Trees.Ordered (fun a b => key a < key b) t) : (Trees.inorder t).Nodup :=
  List.Nodup.of_map key (Trees.ordered_key_nodup key t h)

/-- Key injectivity is obtained on the actual labels, without a global assumption. -/
theorem key_injective_on_labels [Preorder κ] (key : α → κ) (t : BinaryTree α)
    (h : Trees.Ordered (fun a b => key a < key b) t) {a b : α}
    (ha : a ∈ Trees.inorder t) (hb : b ∈ Trees.inorder t) (hk : key a = key b) : a = b :=
  List.inj_on_of_nodup_map (Trees.ordered_key_nodup key t h) ha hb hk

theorem ordered_from_weak_keys [PartialOrder κ] (key : α → κ) (t : BinaryTree α)
    (distinct : ((Trees.inorder t).map key).Nodup)
    (weak : ((Trees.inorder t).map key).SortedLE) :
    Trees.Ordered (fun a b => key a < key b) t :=
  (Trees.ordered_key_iff_nodup_sortedLE key t).2 ⟨distinct, weak⟩

theorem strict_implies_weak [Preorder α] (t : BinaryTree α)
    (h : Trees.Ordered (fun a b => a < b) t) :
    Trees.Ordered (fun a b => a ≤ b) t :=
  Trees.ordered_mono _ _ (fun _ _ hab => le_of_lt hab) t h

/-- A strictly monotone label map supplies forward transport between preorders. -/
theorem strictMono_map [Preorder α] [Preorder β] (f : α → β) (hf : StrictMono f)
    (t : BinaryTree α) (h : Trees.Ordered (fun a b => a < b) t) :
    Trees.Ordered (fun a b => a < b) (t.map f) :=
  Trees.ordered_map _ _ f (fun _ _ hab => hf hab) t h

def taggedTree : BinaryTree (Nat × Bool) := three (0, false) (1, true) (2, false)

theorem taggedTree_inorder :
    Trees.inorder taggedTree = [(0, false), (1, true), (2, false)] :=
  three_inorder (0, false) (1, true) (2, false)

theorem taggedTree_ordered :
    Trees.Ordered (fun p q : Nat × Bool => p.1 < q.1) taggedTree := by
  apply Trees.ordered_of_pairwise_inorder
  rw [taggedTree_inorder]
  decide

def discardTag (p : Nat × Bool) : Nat × Unit := (p.1, ())

theorem discardTag_preserves_key (p : Nat × Bool) : (discardTag p).1 = p.1 := rfl

theorem discardTag_not_injective : ¬ Function.Injective discardTag := by
  intro h
  have hp : ((1 : Nat), false) = (1, true) := h rfl
  have hb : false = true := congrArg Prod.snd hp
  cases hb

theorem discarded_inorder :
    Trees.inorder (taggedTree.map discardTag) = [(0, ()), (1, ()), (2, ())] :=
  (Trees.inorder_map discardTag taggedTree).trans
    (congrArg (List.map discardTag) taggedTree_inorder)

theorem discarded_ordered_iff :
    Trees.Ordered (fun p q : Nat × Unit => p.1 < q.1) (taggedTree.map discardTag) ↔
      Trees.Ordered (fun p q : Nat × Bool => p.1 < q.1) taggedTree :=
  Trees.ordered_map_key_iff Prod.fst Prod.fst discardTag discardTag_preserves_key taggedTree

theorem discarded_ordered :
    Trees.Ordered (fun p q : Nat × Unit => p.1 < q.1) (taggedTree.map discardTag) :=
  discarded_ordered_iff.2 taggedTree_ordered

theorem sample_ordered : Trees.Ordered (fun a b : Nat => a < b) TreeCacheExamples.sample := by
  apply Trees.ordered_of_pairwise_inorder
  rw [TreeCacheExamples.sample_inorder]
  decide

/-- The positive weak-plus-distinct client uses the partial order on Nat. -/
theorem sample_ordered_from_weak :
    Trees.Ordered (fun a b : Nat => a < b) TreeCacheExamples.sample := by
  apply ordered_from_weak_keys (fun n : Nat => n)
  · change ([0, 1, 2, 3] : List Nat).Nodup
    decide
  · apply List.sortedLE_iff_pairwise.mpr
    change ([0, 1, 2, 3] : List Nat).Pairwise (fun a b => a ≤ b)
    decide

def collapsedSample : BinaryTree Nat := TreeCacheExamples.sample.map (fun _ : Nat => 0)

theorem collapsed_inorder : Trees.inorder collapsedSample = [0, 0, 0, 0] :=
  (Trees.inorder_map (fun _ : Nat => 0) TreeCacheExamples.sample).trans
    (congrArg (List.map (fun _ : Nat => 0)) TreeCacheExamples.sample_inorder)

theorem collapsed_not_ordered : ¬ Trees.Ordered (fun a b : Nat => a < b) collapsedSample := by
  intro h
  have hn := Trees.ordered_key_nodup (fun n : Nat => n) collapsedSample h
  change ([0, 0, 0, 0] : List Nat).Nodup at hn
  exact (by decide : ¬ ([0, 0, 0, 0] : List Nat).Nodup) hn

theorem corrupt_ordered :
    Trees.Ordered (fun a b : Nat => a < b) (Trees.Cached.erase TreeCacheExamples.corrupt) := by
  rw [TreeCacheExamples.corrupt_erases]
  exact sample_ordered

theorem ordered_invalid_cache :
    Trees.Ordered (fun a b : Nat => a < b) (Trees.Cached.erase TreeCacheExamples.corrupt) ∧
      ¬ Trees.Cached.Valid 0 TreeCacheExamples.sizeStep TreeCacheExamples.corrupt :=
  ⟨corrupt_ordered, TreeCacheExamples.corrupt_not_valid⟩

theorem valid_cache_not_strict :
    Trees.Cached.Valid 0 TreeCacheExamples.sizeStep TreeRotationExamples.sizeBefore ∧
      ¬ Trees.Ordered (fun a b : Nat => a < b)
        (Trees.Cached.erase TreeRotationExamples.sizeBefore) := by
  refine ⟨TreeRotationExamples.sizeBefore_valid, ?_⟩
  intro h
  apply repeated_not_strict
  simpa only [TreeRotationExamples.sizeBefore, Trees.Cached.erase_annotate] using h

/-- The retained four-label fringe is ordered but corrupt; rebuilding the two
pivots preserves all six labels without repairing that fringe. -/
def corruptRebuildLeft : BinaryTree (Nat × Nat) :=
  Trees.Cached.rebuildLeft 0 TreeCacheExamples.sizeStep TreeCacheExamples.corrupt 4 .nil 5 .nil

def corruptRebuildRight : BinaryTree (Nat × Nat) :=
  Trees.Cached.rebuildRight 0 TreeCacheExamples.sizeStep TreeCacheExamples.corrupt 4 .nil 5 .nil

theorem corruptRebuild_left :
    Trees.rotateLeft? (Trees.Cached.erase corruptRebuildRight) =
      some (Trees.Cached.erase corruptRebuildLeft) :=
  Trees.Cached.rotateLeft?_erase_rebuildRight 0 TreeCacheExamples.sizeStep
    TreeCacheExamples.corrupt 4 .nil 5 .nil

theorem corruptRebuildRight_inorder :
    Trees.inorder (Trees.Cached.erase corruptRebuildRight) = [0, 1, 2, 3, 4, 5] := by
  calc
    Trees.inorder (Trees.Cached.erase corruptRebuildRight) =
        Trees.inorder (Trees.Cached.erase TreeCacheExamples.corrupt) ++ [4, 5] :=
      Trees.Cached.inorder_erase_rebuildRight 0 TreeCacheExamples.sizeStep
        TreeCacheExamples.corrupt 4 .nil 5 .nil
    _ = [0, 1, 2, 3, 4, 5] :=
      congrArg (fun xs : List Nat => xs ++ [4, 5]) TreeCacheExamples.corrupt_inorder

theorem corruptRebuildLeft_inorder :
    Trees.inorder (Trees.Cached.erase corruptRebuildLeft) = [0, 1, 2, 3, 4, 5] :=
  (Trees.Cached.inorder_erase_rebuildLeft_eq_rebuildRight 0 TreeCacheExamples.sizeStep
    TreeCacheExamples.corrupt 4 .nil 5 .nil).trans corruptRebuildRight_inorder

theorem corruptRebuildRight_ordered :
    Trees.Ordered (fun a b : Nat => a < b) (Trees.Cached.erase corruptRebuildRight) := by
  apply Trees.ordered_of_pairwise_inorder
  rw [corruptRebuildRight_inorder]
  decide

theorem corruptRebuildLeft_ordered :
    Trees.Ordered (fun a b : Nat => a < b) (Trees.Cached.erase corruptRebuildLeft) :=
  (Trees.Cached.ordered_erase_rebuildLeft_iff_rebuildRight _
    (fun _ _ _ hab hbc => lt_trans hab hbc) 0 TreeCacheExamples.sizeStep
    TreeCacheExamples.corrupt 4 .nil 5 .nil).2 corruptRebuildRight_ordered

theorem corruptRebuildLeft_not_valid :
    ¬ Trees.Cached.Valid 0 TreeCacheExamples.sizeStep corruptRebuildLeft := by
  intro h
  exact TreeCacheExamples.corrupt_not_valid
    ((Trees.Cached.rebuildLeft_valid_iff 0 TreeCacheExamples.sizeStep
      TreeCacheExamples.corrupt 4 .nil 5 .nil).1 h).1

theorem corruptRebuildRight_not_valid :
    ¬ Trees.Cached.Valid 0 TreeCacheExamples.sizeStep corruptRebuildRight := by
  intro h
  exact TreeCacheExamples.corrupt_not_valid
    ((Trees.Cached.rebuildRight_valid_iff 0 TreeCacheExamples.sizeStep
      TreeCacheExamples.corrupt 4 .nil 5 .nil).1 h).1

end OrderedTreeExamples
