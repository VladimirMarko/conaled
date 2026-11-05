import Applications.Trees.BasicObservations
import Mathlib.Data.List.Nodup

/-! Total reconstruction from preorder and inorder.
The Option parser fails on mismatched empty inputs, an absent root, or a failed
child parse. Repeated labels use the first inorder occurrence; the correctness
theorem has the source's distinct-preorder hypothesis. The public wrapper uses
the empty tree as its explicit failure result, without a default label.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u
variable {α : Type u}

/-- Parse both traversals, splitting at the first inorder occurrence of the root. -/
def reconstruct? [DecidableEq α] : List α → List α → Option (BinaryTree α)
  | [], [] => some .nil
  | [], _ :: _ => none
  | a :: pre, ino =>
      if a ∈ ino then
        let k := ino.idxOf a
        match reconstruct? (pre.take k) (ino.take k),
          reconstruct? (pre.drop k) (ino.drop (k + 1)) with
        | some l, some r => some (.node a l r)
        | _, _ => none
      else none
termination_by pre _ => pre.length
decreasing_by
  all_goals
    simp only [List.length_take, List.length_drop, List.length_cons]
    omega

@[simp] theorem reconstruct?_nil_nil [DecidableEq α] :
    reconstruct? ([] : List α) [] = some .nil := by
  rw [reconstruct?]

@[simp] theorem reconstruct?_nil_cons [DecidableEq α] (a : α) (ino : List α) :
    reconstruct? [] (a :: ino) = none := by
  rw [reconstruct?]

theorem reconstruct?_cons [DecidableEq α] (a : α) (pre ino : List α) :
    reconstruct? (a :: pre) ino =
      if a ∈ ino then
        match reconstruct? (pre.take (ino.idxOf a)) (ino.take (ino.idxOf a)),
          reconstruct? (pre.drop (ino.idxOf a)) (ino.drop (ino.idxOf a + 1)) with
        | some l, some r => some (.node a l r)
        | _, _ => none
      else none := by
  rw [reconstruct?]

theorem reconstruct?_cons_of_not_mem [DecidableEq α] (a : α) (pre ino : List α)
    (ha : a ∉ ino) : reconstruct? (a :: pre) ino = none := by
  rw [reconstruct?_cons, if_neg ha]

/-- Return the parsed tree, with the empty tree as an explicit failure fallback. -/
def reconstruct [DecidableEq α] (pre ino : List α) : BinaryTree α :=
  (reconstruct? pre ino).getD .nil

@[simp] theorem reconstruct_nil_nil [DecidableEq α] :
    reconstruct ([] : List α) [] = .nil := by
  simp [reconstruct]

theorem reconstruct_of_none [DecidableEq α] {pre ino : List α}
    (h : reconstruct? pre ino = none) : reconstruct pre ino = .nil := by
  simp only [reconstruct, h, Option.getD_none]

/-- Distinct preorder labels identify the correct root split at every node. -/
theorem reconstruct?_traversals [DecidableEq α] (t : BinaryTree α)
    (hn : (preorder t).Nodup) : reconstruct? (preorder t) (inorder t) = some t := by
  revert hn
  induction t with
  | nil => intro _; exact reconstruct?_nil_nil
  | node a l r ihl ihr =>
      intro hn
      have hnode := List.nodup_cons.mp hn
      have hl : (preorder l).Nodup := List.Nodup.of_append_left hnode.2
      have hr : (preorder r).Nodup := List.Nodup.of_append_right hnode.2
      have hnot : a ∉ inorder l := by
        intro ha
        have hp : a ∈ preorder l := (mem_preorder_iff_mem_setTree a l).mpr
          ((mem_inorder_iff_mem_setTree a l).mp ha)
        exact hnode.1 (List.mem_append.mpr (Or.inl hp))
      have hi : (inorder l ++ a :: inorder r).idxOf a = (inorder l).length := by
        rw [List.idxOf_append_of_notMem hnot, List.idxOf_cons_self, Nat.add_zero]
      have hdrop : (inorder l ++ a :: inorder r).drop ((inorder l).length + 1) =
          inorder r := by
        simp only [List.drop_add_one_eq_tail_drop, List.drop_left, List.tail_cons]
      have hlen : (inorder l).length = (preorder l).length := by
        rw [inorder_length, preorder_length]
      have hmem : a ∈ inorder l ++ a :: inorder r := by simp
      rw [preorder_node, inorder_node, reconstruct?_cons, if_pos hmem]
      simp only [hi, List.take_left, hdrop]
      simp only [hlen, List.take_left, List.drop_left, ihl hl, ihr hr]

theorem reconstruct_traversals [DecidableEq α] (t : BinaryTree α)
    (hn : (preorder t).Nodup) : reconstruct (preorder t) (inorder t) = t := by
  simp only [reconstruct, reconstruct?_traversals t hn, Option.getD_some]

end Trees
