import Applications.Search.IntervalTree.Insert
import Applications.Search.IntervalTree.Delete
import Applications.Search.OrderedTree.Refinement

/-! Update refinements transport the existing ordered-tree/list proofs through
erasure. Strict complete-key inorder is required; cache validity is independent.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.IntervalTree
universe u v
variable {α : Type u} {κ : Type v} [LE α] [Max α] [Bot α] [LinearOrder κ]

theorem inorder_insert (iv : κ → IntervalKey α) (x : κ) {t : BinaryTree (κ × α)}
    (strict : OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    Trees.inorder (Trees.Cached.erase (insert iv x t)) =
      OrderedList.insert x (Trees.inorder (Trees.Cached.erase t)) := by
  rw [erase_insert]
  exact OrderedTree.inorder_insert x strict

theorem inorder_delete (iv : κ → IntervalKey α) (x : κ) {t : BinaryTree (κ × α)}
    (strict : OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    Trees.inorder (Trees.Cached.erase (delete iv x t)) =
      OrderedList.delete x (Trees.inorder (Trees.Cached.erase t)) := by
  rw [erase_delete]
  exact OrderedTree.inorder_delete x strict

theorem strict_inorder_insert (iv : κ → IntervalKey α) (x : κ)
    {t : BinaryTree (κ × α)}
    (strict : OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase (insert iv x t))) := by
  rw [inorder_insert iv x strict]
  exact OrderedList.strict_insert x strict

theorem strict_inorder_delete (iv : κ → IntervalKey α) (x : κ)
    {t : BinaryTree (κ × α)}
    (strict : OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase (delete iv x t))) := by
  rw [inorder_delete iv x strict]
  exact OrderedList.strict_delete x strict

end Search.IntervalTree
