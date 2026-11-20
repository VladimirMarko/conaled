import Applications.Search.IntervalTree.Leftmost
import Applications.Search.OrderedTree.Deletion

/-! Successor deletion on annotated interval trees. Search ancestors and the
successor root use the smart constructor. The raw fallback with empty right
returns the entire left subtree unchanged, including any invalid annotations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.IntervalTree
universe u v
variable {α : Type u} {κ : Type v} [LE α] [Max α] [Bot α]

section Raw
variable [LT κ] [DecidableLT κ]

def delete (iv : κ → IntervalKey α) (x : κ) : BinaryTree (κ × α) → BinaryTree (κ × α)
  | .nil => .nil
  | .node (a, _) l r =>
      if x < a then node iv (delete iv x l) a r
      else if a < x then node iv l a (delete iv x r)
      else join iv l r

@[simp] theorem delete_nil (iv : κ → IntervalKey α) (x : κ) :
    delete iv x .nil = .nil := rfl

theorem delete_node (iv : κ → IntervalKey α) (x a : κ) (m : α)
    (l r : BinaryTree (κ × α)) :
    delete iv x (.node (a, m) l r) =
      if x < a then node iv (delete iv x l) a r
      else if a < x then node iv l a (delete iv x r)
      else join iv l r := rfl

theorem delete_of_lt (iv : κ → IntervalKey α) {x a : κ} (h : x < a)
    (m : α) (l r : BinaryTree (κ × α)) :
    delete iv x (.node (a, m) l r) = node iv (delete iv x l) a r := by
  simp only [delete_node, ite_eq_left h]

theorem delete_of_gt (iv : κ → IntervalKey α) {x a : κ}
    (notLeft : ¬x < a) (right : a < x) (m : α) (l r : BinaryTree (κ × α)) :
    delete iv x (.node (a, m) l r) = node iv l a (delete iv x r) := by
  simp only [delete_node, ite_eq_right notLeft, ite_eq_left right]

theorem delete_of_incomparable (iv : κ → IntervalKey α) {x a : κ}
    (notLeft : ¬x < a) (notRight : ¬a < x) (m : α) (l r : BinaryTree (κ × α)) :
    delete iv x (.node (a, m) l r) = join iv l r := by
  simp only [delete_node, ite_eq_right notLeft, ite_eq_right notRight]

/-- The raw comparison interface suffices; no ordering invariant or lawful Max is needed. -/
theorem erase_delete (iv : κ → IntervalKey α) (x : κ) (t : BinaryTree (κ × α)) :
    Trees.Cached.erase (delete iv x t) =
      OrderedTree.deleteBy id x (Trees.Cached.erase t) := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      rcases a with ⟨a, m⟩
      simp only [delete_node, Trees.Cached.erase_node, OrderedTree.deleteBy_node, id_eq]
      split
      · simpa only [erase_node] using congrArg (fun s => BinaryTree.node a s
          (Trees.Cached.erase r)) ihl
      · split
        · simpa only [erase_node] using congrArg (fun s => BinaryTree.node a
            (Trees.Cached.erase l) s) ihr
        · exact erase_join iv l r

theorem delete_cacheValid (iv : κ → IntervalKey α) (x : κ)
    {t : BinaryTree (κ × α)} (valid : CacheValid iv t) :
    CacheValid iv (delete iv x t) := by
  induction t with
  | nil => exact cacheValid_nil iv
  | node a l r ihl ihr =>
      rcases a with ⟨a, m⟩
      have parts := (cacheValid_node iv a m l r).mp valid
      rw [delete_node]
      split
      · exact node_cacheValid iv (ihl parts.1) a parts.2.1
      · split
        · exact node_cacheValid iv parts.1 a (ihr parts.2.1)
        · exact join_cacheValid iv parts.1 parts.2.1

end Raw

section LinearKeys
variable [LinearOrder κ]

theorem delete_eq_root (iv : κ → IntervalKey α) (a : κ) (m : α)
    (l r : BinaryTree (κ × α)) :
    delete iv a (.node (a, m) l r) = join iv l r :=
  delete_of_incomparable iv (lt_irrefl a) (lt_irrefl a) m l r

theorem delete_eq_root_nil (iv : κ → IntervalKey α) (a : κ) (m : α)
    (l : BinaryTree (κ × α)) : delete iv a (.node (a, m) l .nil) = l := by
  rw [delete_eq_root, join_nil_right]

theorem delete_eq_root_splitMin (iv : κ → IntervalKey α) (a : κ) (m : α)
    {l r s : BinaryTree (κ × α)} {x : κ} (found : splitMin iv r = some (x, s)) :
    delete iv a (.node (a, m) l r) = node iv l x s := by
  rw [delete_eq_root, join_of_splitMin iv found]

end LinearKeys
end Search.IntervalTree
