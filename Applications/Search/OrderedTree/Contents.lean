import Applications.Search.OrderedTree.Basic
import Mathlib.Data.List.Nodup

/-!
# Finite, duplicate-free contents of ordered trees

The canonical inorder list witnesses finiteness. Strict all-descendant
ordering makes that list pairwise increasing, hence free of duplicates.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedTree
universe u
variable {α : Type u} [Preorder α]

theorem ordered_entries_pairwise {t : BinaryTree α} (ordered : Ordered t) :
    (entries t).Pairwise (· < ·) := by
  induction t with
  | nil => exact List.Pairwise.nil
  | node x l r hl hr =>
      rw [entries_node, List.pairwise_append]
      refine ⟨hl ordered.1, ?_, ?_⟩
      · rw [List.pairwise_cons]
        exact ⟨fun y hy => ordered.2.2.2.of_contains ((contains_iff_mem_entries y r).mpr hy),
          hr ordered.2.1⟩
      · intro a ha b hb
        have ax : a < x := ordered.2.2.1.of_contains ((contains_iff_mem_entries a l).mpr ha)
        rcases List.mem_cons.mp hb with eq | hb
        · simpa only [eq] using ax
        · exact lt_trans ax
            (ordered.2.2.2.of_contains ((contains_iff_mem_entries b r).mpr hb))

theorem ordered_entries_nodup {t : BinaryTree α} (ordered : Ordered t) :
    (entries t).Nodup := (ordered_entries_pairwise ordered).nodup

/-- An explicit finite enumeration witnesses the represented set; neither
search success nor an assumed finiteness predicate serves as its definition. -/
theorem finite_contents {t : BinaryTree α} (ordered : Ordered t) :
    ∃ xs : List α, xs.Nodup ∧ xs.length = t.numNodes ∧
      ∀ x, Contains x t ↔ x ∈ xs :=
  ⟨entries t, ordered_entries_nodup ordered, entries_length t,
    fun x => contains_iff_mem_entries x t⟩

end Search.OrderedTree
