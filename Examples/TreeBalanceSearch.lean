import Applications.Search.OrderedTree.Observations
import Examples.TreeBalance
import Examples.OrderedTree

/-! The consuming balancer interpreted through the existing ordered-set API.
The pure consumer remains order-free. These cross-application laws reuse its
inorder contract and the existing independent ordering/set observations.
Rebalancing is an identity on represented sets, and its relational square
composes with an actual insertion and directed membership query.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.TreeBalanceSearch
open Trees Trees.Balance Search Search.OrderedTree
universe u v w
variable {α : Type u} {κ : Type v} {β : Type w}

theorem ordered_bal_iff [Preorder α] {n : Nat} {xs zs : List α}
    {t : BinaryTree α} (h : bal n xs = some (t, zs)) :
    Ordered t ↔ (xs.take n).Pairwise (· < ·) := by
  rw [ordered_iff_inorder_pairwise, bal_inorder h]

theorem ordered_balList_iff [Preorder α] (n : Nat) (xs : List α)
    (h : n ≤ xs.length) :
    Ordered (balList n xs) ↔ (xs.take n).Pairwise (· < ·) := by
  rw [ordered_iff_inorder_pairwise, inorder_balList h]

theorem ordered_balanceList_iff [Preorder α] (xs : List α) :
    Ordered (balanceList xs) ↔ xs.Pairwise (· < ·) := by
  rw [ordered_iff_inorder_pairwise, inorder_balanceList]

theorem ordered_balTree_iff [Preorder α] (n : Nat) (t : BinaryTree α)
    (h : n ≤ t.numNodes) :
    Ordered (balTree n t) ↔ ((inorder t).take n).Pairwise (· < ·) := by
  rw [ordered_iff_inorder_pairwise, inorder_balTree t h]

theorem ordered_balanceTree_iff [Preorder α] (t : BinaryTree α) :
    Ordered (balanceTree t) ↔ Ordered t := by
  rw [ordered_iff_inorder_pairwise, inorder_balanceTree, ordered_iff_inorder_pairwise]

/-- Key order is independent of the payload type and needs no injectivity law. -/
theorem orderedBy_bal_iff [Preorder κ] (key : α → κ) {n : Nat} {xs zs : List α}
    {t : BinaryTree α} (h : bal n xs = some (t, zs)) :
    OrderedBy key t ↔ (xs.take n).Pairwise (fun x y => key x < key y) := by
  rw [orderedBy_iff_inorder_pairwise, bal_inorder h]

theorem orderedBy_balList_iff [Preorder κ] (key : α → κ) (n : Nat) (xs : List α)
    (h : n ≤ xs.length) :
    OrderedBy key (balList n xs) ↔ (xs.take n).Pairwise (fun x y => key x < key y) := by
  rw [orderedBy_iff_inorder_pairwise, inorder_balList h]

theorem orderedBy_balanceList_iff [Preorder κ] (key : α → κ) (xs : List α) :
    OrderedBy key (balanceList xs) ↔ xs.Pairwise (fun x y => key x < key y) := by
  rw [orderedBy_iff_inorder_pairwise, inorder_balanceList]

theorem orderedBy_balTree_iff [Preorder κ] (key : α → κ) (n : Nat) (t : BinaryTree α)
    (h : n ≤ t.numNodes) :
    OrderedBy key (balTree n t) ↔
      ((inorder t).take n).Pairwise (fun x y => key x < key y) := by
  rw [orderedBy_iff_inorder_pairwise, inorder_balTree t h]

theorem orderedBy_balanceTree_iff [Preorder κ] (key : α → κ) (t : BinaryTree α) :
    OrderedBy key (balanceTree t) ↔ OrderedBy key t := by
  rw [orderedBy_iff_inorder_pairwise, inorder_balanceTree,
    orderedBy_iff_inorder_pairwise]

/-- All raw trees retain their label set; ordering is unnecessary here. -/
theorem setTree_balanceTree (t : BinaryTree α) :
    setTree (balanceTree t) = setTree t := by
  ext x
  simp only [← mem_inorder_iff_mem_setTree, inorder_balanceTree]

/-- A validity-preserving identity on the existing represented set. -/
def rebalanceSquare [Preorder α] :
    Relational.RelSquare (AbstractSet.representation (setTree (α := α)) Ordered)
      (AbstractSet.representation (setTree (α := α)) Ordered) where
  impl := balanceTree
  spec := id
  preserves := by
    change ∀ {t : BinaryTree α} {contents : α → Prop},
      (Ordered t ∧ ∀ x, setTree t x ↔ contents x) →
        Ordered (balanceTree t) ∧ ∀ x, setTree (balanceTree t) x ↔ contents x
    intro t contents h
    refine ⟨(ordered_balanceTree_iff t).mpr h.1, ?_⟩
    intro x
    rw [setTree_balanceTree]
    exact h.2 x

/-- Compose candidate insertion and actual rebalancing through their common API. -/
def insertRebalanceSquare [LinearOrder α] (x : α) :
    Relational.RelSquare (AbstractSet.representation (setTree (α := α)) Ordered)
      (AbstractSet.representation (setTree (α := α)) Ordered) :=
  Relational.compose rebalanceSquare (candidate_set_laws.insertSquare x)

theorem insert_rebalance_contract [LinearOrder α] (x : α) {t : BinaryTree α}
    (ht : Ordered t) :
    Ordered (balanceTree (insertCandidate x t)) ∧
      ∀ y, y ∈ setTree (balanceTree (insertCandidate x t)) ↔ y = x ∨ y ∈ setTree t :=
  (insertRebalanceSquare x).preserves ⟨ht, fun _ => Iff.rfl⟩

/-- The ordinary membership API consumes the transported validity proof. -/
theorem member_insert_rebalance [LinearOrder α] (x y : α) {t : BinaryTree α}
    (ht : Ordered t) :
    memberCandidate y (balanceTree (insertCandidate x t)) = true ↔
      y = x ∨ y ∈ setTree t := by
  have hc := insert_rebalance_contract x ht
  exact (candidate_set_laws.member y _ hc.1).trans (hc.2 y)

theorem figure_ordered : Ordered TreeBalance.figureTree := by
  rw [← TreeBalance.figure_shape, ordered_balanceList_iff]
  decide

/-- Repeated labels are legal for balancing but do not form a strict BST. -/
theorem repeated_not_strict :
    ([1, 1] : List Nat).Pairwise (· ≤ ·) ∧
      ¬ Ordered (balanceList ([1, 1] : List Nat)) := by
  rw [ordered_balanceList_iff]
  decide

/-- An undersized request returns nil; its order does not certify the input. -/
theorem failed_prefix_not_order_certificate :
    Ordered (balList 3 ([2, 1] : List Nat)) ∧
      ¬ (([2, 1] : List Nat).take 3).Pairwise (· < ·) := by
  have hnone : bal 3 ([2, 1] : List Nat) = none :=
    (bal_eq_none_iff _ _).mpr (by decide)
  rw [balList_of_none hnone]
  exact ⟨ordered_nil, by decide⟩

theorem keyed_payloads (a b : β) :
    OrderedBy Prod.fst (balanceList [((1 : Nat), a), (3, b)]) := by
  apply (orderedBy_balanceList_iff Prod.fst _).mpr
  simp

theorem function_payloads :
    OrderedBy Prod.fst
      (balanceList [((1 : Nat), fun n : Nat => n), (3, fun n : Nat => n + 1)]) :=
  keyed_payloads _ _

theorem repeated_keys_not_strict (a b : β) :
    ([(2, a), (2, b)] : List (Nat × β)).Pairwise (fun x y => x.1 ≤ y.1) ∧
      ¬ OrderedBy Prod.fst (balanceList [(2, a), (2, b)]) := by
  rw [orderedBy_balanceList_iff]
  simp

/-- The prefix theorem retains an arbitrary repeated, unsorted suffix. -/
theorem prefix_ignores_suffix (suffix : List Nat) :
    Ordered (balList 3 ([1, 2, 3] ++ suffix)) := by
  have h : 3 ≤ ([1, 2, 3] ++ suffix).length := by simp
  apply (ordered_balList_iff 3 _ h).mpr
  simp

theorem empty_labels : setTree (balanceTree (.nil : BinaryTree Empty)) = ∅ := by
  rw [setTree_balanceTree, setTree_nil]

/-- An actual insertion/rebalance/query client uses the composed public laws. -/
theorem inserted_query :
    memberCandidate 4 (balanceTree (insertCandidate 4 OrderedTree.sample)) = true := by
  apply (member_insert_rebalance 4 4 OrderedTree.sample_ordered).mpr
  exact Or.inl rfl

theorem original_query_preserved :
    memberCandidate 1 (balanceTree (insertCandidate 4 OrderedTree.sample)) = true := by
  apply (member_insert_rebalance 4 1 OrderedTree.sample_ordered).mpr
  right
  exact (contains_iff_mem_setTree _ _).mp OrderedTree.sample_contains_one

end Examples.TreeBalanceSearch
