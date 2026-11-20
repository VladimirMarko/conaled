import Applications.Search.AbstractSet.Refinement
import Applications.Search.OrderedList.Sorted
import Applications.Search.OrderedTree.DeletionInterface

/-!
# Figure 5.1 and composition through the strict-list model

The equalities concern the actual source operations and require only strict
inorder. The generic composition has an independent auxiliary invariant; the
unbalanced tree instances use True. Its contracts form a separate proof route
from the direct structural deletion contracts.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedTree
universe u
variable {α : Type u} [LinearOrder α]

theorem inorder_insert (x : α) {t : BinaryTree α}
    (strict : OrderedList.Strict (Trees.inorder t)) :
    Trees.inorder (insert x t) = OrderedList.insert x (Trees.inorder t) := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      have parts := (OrderedList.strict_middle (Trees.inorder l) a (Trees.inorder r)).mp strict
      have hl := OrderedList.strict_prefix parts.1
      have hr := OrderedList.strict_tail parts.2
      rw [Trees.inorder_node, OrderedList.insert_distribution x a _ _ parts.1]
      by_cases hlt : x < a
      · rw [insert, ite_eq_left hlt, Trees.inorder_node, ihl hl, ite_eq_left hlt]
      · by_cases hgt : a < x
        · rw [insert, ite_eq_right hlt, ite_eq_left hgt, Trees.inorder_node,
            ihr hr, ite_eq_right hlt, OrderedList.insert, ite_eq_right hlt,
            ite_eq_right (ne_of_gt hgt)]
        · have heq : x = a := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
          subst x
          simp [insert, OrderedList.insert]

/-- Only the raw inorder concatenation law of the equality callback is needed. -/
theorem inorder_deleteWith
    (combine : BinaryTree α → BinaryTree α → BinaryTree α)
    (commutes : ∀ l r, Trees.inorder (combine l r) = Trees.inorder l ++ Trees.inorder r)
    (x : α) {t : BinaryTree α} (strict : OrderedList.Strict (Trees.inorder t)) :
    Trees.inorder (deleteWith combine id x t) = OrderedList.delete x (Trees.inorder t) := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      have parts := (OrderedList.strict_middle (Trees.inorder l) a (Trees.inorder r)).mp strict
      have hl := OrderedList.strict_prefix parts.1
      have hr := OrderedList.strict_tail parts.2
      rw [Trees.inorder_node, OrderedList.delete_distribution x a
        (Trees.inorder l) (Trees.inorder r) strict]
      rw [deleteWith]
      simp only [id_eq]
      by_cases hlt : x < a
      · rw [ite_eq_left hlt, Trees.inorder_node, ihl hl, ite_eq_left hlt]
      · by_cases hgt : a < x
        · rw [ite_eq_right hlt, ite_eq_left hgt, Trees.inorder_node,
            ihr hr, ite_eq_right hlt, OrderedList.delete, ite_eq_right (ne_of_gt hgt)]
        · have heq : x = a := le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
          subst x
          simp [commutes, OrderedList.delete]

theorem inorder_delete (x : α) {t : BinaryTree α}
    (strict : OrderedList.Strict (Trees.inorder t)) :
    Trees.inorder (delete x t) = OrderedList.delete x (Trees.inorder t) :=
  inorder_deleteWith Trees.joinLeftmost Trees.inorder_joinLeftmost x strict

theorem inorder_deleteJoin (x : α) {t : BinaryTree α}
    (strict : OrderedList.Strict (Trees.inorder t)) :
    Trees.inorder (deleteJoin x t) = OrderedList.delete x (Trees.inorder t) :=
  inorder_deleteWith Trees.join Trees.inorder_join x strict

theorem member_inorder (x : α) {t : BinaryTree α}
    (strict : OrderedList.Strict (Trees.inorder t)) :
    member x t = decide (x ∈ Trees.inorder t) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  exact (member_correct (ordered_of_inorder_pairwise strict) x).trans
    (contains_iff_mem_entries x t)

theorem inorderRefinement : AbstractSet.Refinement
    (deleteOps : AbstractSet.DeleteOps α (BinaryTree α)) OrderedList.ops Trees.inorder
    (fun _ => True) OrderedList.Strict where
  empty := rfl
  auxiliary_empty := trivial
  insert x _ _ hs := inorder_insert x hs
  auxiliary_insert _ _ _ _ := trivial
  delete x _ _ hs := inorder_delete x hs
  auxiliary_delete _ _ _ _ := trivial
  member x _ _ hs := member_inorder x hs

theorem inorderJoinRefinement : AbstractSet.Refinement
    (deleteJoinOps : AbstractSet.DeleteOps α (BinaryTree α)) OrderedList.ops Trees.inorder
    (fun _ => True) OrderedList.Strict where
  empty := rfl
  auxiliary_empty := trivial
  insert x _ _ hs := inorder_insert x hs
  auxiliary_insert _ _ _ _ := trivial
  delete x _ _ hs := inorder_deleteJoin x hs
  auxiliary_delete _ _ _ _ := trivial
  member x _ _ hs := member_inorder x hs

theorem inorder_valid_iff (t : BinaryTree α) :
    AbstractSet.Refinement.Valid Trees.inorder (fun _ => True) OrderedList.Strict t ↔ Ordered t := by
  exact (and_iff_right trivial).trans (ordered_iff_inorder_pairwise t).symm

theorem refinedDeleteSetLaws : AbstractSet.DeleteLaws
    (deleteOps : AbstractSet.DeleteOps α (BinaryTree α)) Trees.setTree Ordered :=
  ((inorderRefinement.laws OrderedList.laws).congr_valid inorder_valid_iff).congr_observe
    (fun t _ x => (contains_iff_mem_entries x t).symm.trans (contains_iff_mem_setTree x t))

theorem refinedDeleteJoinSetLaws : AbstractSet.DeleteLaws
    (deleteJoinOps : AbstractSet.DeleteOps α (BinaryTree α)) Trees.setTree Ordered :=
  ((inorderJoinRefinement.laws OrderedList.laws).congr_valid inorder_valid_iff).congr_observe
    (fun t _ x => (contains_iff_mem_entries x t).symm.trans (contains_iff_mem_setTree x t))

end Search.OrderedTree
