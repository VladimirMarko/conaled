import Applications.Trees.BasicObservations
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

/-!
# Distinct tree contents and node cardinality

Distinct inorder labels identify structural node count with the independently
observed set cardinality. No order, cache or balance invariant is required.
Correspondence: docs/research/fdsa-avl-continuation.md.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u
variable {α : Type u}

theorem setTree_ncard_eq_numNodes (t : BinaryTree α)
    (nodup : (inorder t).Nodup) : (setTree t).ncard = t.numNodes := by
  classical
  have contents : setTree t = ((inorder t).toFinset : Set α) := by
    ext key
    simp only [Finset.mem_coe, List.mem_toFinset, mem_inorder_iff_mem_setTree]
  rw [contents, Set.ncard_coe_finset, List.toFinset_card_of_nodup nodup, inorder_length]

end Trees
