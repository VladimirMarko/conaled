import Applications.Trees.Rotations.Position

/-!
# Existence of a right-rotation route by induction alone

This owner imports only primitive operations and their measure/trace laws.
It neither defines nor uses listification, a position generator, or a counting
algorithm. Existential witnesses are assembled from induction hypotheses.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.Rotations
open Search.SharedTree (Branch)
universe u
variable {α : Type u}

/-- FDSA Exercise 5.6, independently of every schedule-computing function. -/
theorem exists_right_list (t : BinaryTree α) :
    ∃ (ps : List (List Branch)) (s : BinaryTree α),
      applyAts? rotateRight? ps t = some s ∧ IsList s ∧ inorder s = inorder t := by
  have main : ∀ n, ∀ t : BinaryTree α, measure t = n →
      ∃ (ps : List (List Branch)) (s : BinaryTree α),
        applyAts? rotateRight? ps t = some s ∧ IsList s ∧ inorder s = inorder t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro t ht
        cases t with
        | nil => exact ⟨[], .nil, rfl, True.intro, rfl⟩
        | node a l r =>
            cases l with
            | nil =>
                have small : measure r < n := by
                  rw [← ht]
                  exact measure_descend a r
                obtain ⟨ps, s, run, form, same⟩ := ih (measure r) small r rfl
                refine ⟨ps.map (Branch.right :: ·), .node a .nil s, ?_, ⟨rfl, form⟩, ?_⟩
                · rw [applyAts?_map_right, run]
                  rfl
                · simp only [inorder_node, inorder_nil, List.nil_append, same]
            | node b A B =>
                have small : measure (.node b A (.node a B r)) < n := by
                  rw [← ht]
                  exact measure_rotate b a A B r
                obtain ⟨ps, s, run, form, same⟩ :=
                  ih (measure (.node b A (.node a B r))) small _ rfl
                refine ⟨[] :: ps, s, ?_, form, ?_⟩
                · simpa only [applyAts?_cons, applyAt?_root, rotateRight?_node,
                    Option.bind_some] using run
                · exact same.trans (rotateRight?_inorder rfl)
  exact main (measure t) t rfl

end Trees.Rotations
