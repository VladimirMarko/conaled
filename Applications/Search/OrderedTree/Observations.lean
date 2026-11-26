import Applications.Trees.BasicObservations
import Applications.Search.OrderedTree.Contents
import Applications.Search.OrderedTree.Interface

/-! Canonical tree observations and the existing ordered-set contracts.
Raw membership observations agree on every tree. Strict ordering is an
independent invariant; its inorder characterization retains the required
transitivity in the forward direction. Source and statement assessment:
`docs/research/fdsa-tree-search-observations.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedTree
universe u v
variable {α : Type u} {κ : Type v}

/-- This structural correspondence also holds for unordered trees. -/
theorem contains_iff_mem_setTree (x : α) (t : BinaryTree α) :
    Contains x t ↔ x ∈ Trees.setTree t :=
  (contains_iff_mem_entries x t).trans (Trees.mem_inorder_iff_mem_setTree x t)

theorem all_iff_mem_setTree (P : α → Prop) (t : BinaryTree α) :
    All P t ↔ ∀ x, x ∈ Trees.setTree t → P x := by
  rw [all_iff]
  constructor
  · intro h x hx
    exact h x ((contains_iff_mem_setTree x t).mpr hx)
  · intro h x hx
    exact h x ((contains_iff_mem_setTree x t).mp hx)

/-- The converse uses the given strict relation alone: pairwise order already
contains every root/descendant comparison needed by the structural predicate. -/
theorem ordered_of_inorder_pairwise [LT α] {t : BinaryTree α} :
    (Trees.inorder t).Pairwise (· < ·) → Ordered t := by
  induction t with
  | nil => intro _; exact ordered_nil
  | node x l r hl hr =>
      intro h
      rw [Trees.inorder_node, List.pairwise_append] at h
      rcases h with ⟨hleft, hright, hcross⟩
      rw [List.pairwise_cons] at hright
      refine (ordered_node x l r).mpr ⟨hl hleft, hr hright.2, ?_, ?_⟩
      · apply (all_iff (fun y => y < x) l).mpr
        intro y hy
        exact hcross y ((contains_iff_mem_entries y l).mp hy) x (by simp)
      · apply (all_iff (fun y => x < y) r).mpr
        intro y hy
        exact hright.1 y ((contains_iff_mem_entries y r).mp hy)

/-- A preorder supplies transitivity for the forward implication. Neither
linearity nor a decidable comparison is needed for this observation theorem. -/
theorem ordered_iff_inorder_pairwise [Preorder α] (t : BinaryTree α) :
    Ordered t ↔ (Trees.inorder t).Pairwise (· < ·) := by
  constructor
  · intro h
    simpa only [entries_eq_inorder] using ordered_entries_pairwise h
  · exact ordered_of_inorder_pairwise

/-- Payloads need no order and the key need not be injective. -/
theorem orderedBy_of_inorder_pairwise [LT κ] (key : α → κ) (t : BinaryTree α)
    (h : (Trees.inorder t).Pairwise (fun x y => key x < key y)) :
    OrderedBy key t := by
  apply (orderedBy_iff_map key t).mpr
  apply ordered_of_inorder_pairwise
  simpa only [Trees.inorder_map, List.pairwise_map] using h

theorem orderedBy_iff_inorder_pairwise [Preorder κ] (key : α → κ) (t : BinaryTree α) :
    OrderedBy key t ↔ (Trees.inorder t).Pairwise (fun x y => key x < key y) := by
  rw [orderedBy_iff_map, ordered_iff_inorder_pairwise,
    Trees.inorder_map, List.pairwise_map]

/-- The same baseline operations and validity laws use the independent FDSA set. -/
theorem baseline_set_laws [LinearOrder α] :
    AbstractSet.Laws (baselineOps : AbstractSet.Ops α (BinaryTree α))
      Trees.setTree Ordered :=
  baseline_laws.congr_observe (fun t _ x => contains_iff_mem_setTree x t)

/-- Candidate/abort operations satisfy that same observation contract. -/
theorem candidate_set_laws [LinearOrder α] :
    AbstractSet.Laws (candidateOps : AbstractSet.Ops α (BinaryTree α))
      Trees.setTree Ordered :=
  candidate_laws.congr_observe (fun t _ x => contains_iff_mem_setTree x t)

end Search.OrderedTree
