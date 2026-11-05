import Applications.Trees.Reconstruction

/-! Reconstruction uses, explicit failure cases, and the two-node repeated-label
ambiguity. The sample's independently calculated traversals are connected to the
all-tree correctness laws after its distinctness hypothesis is established.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeReconstructionExamples
open Trees
universe u
variable {α : Type u}

def sample : BinaryTree Nat :=
  .node 9 (.node 3 .nil (.node 5 .nil .nil)) (.node 7 (.node 6 .nil .nil) .nil)

theorem sample_preorder : preorder sample = [9, 3, 5, 7, 6] := rfl

theorem sample_inorder : inorder sample = [3, 5, 9, 6, 7] := rfl

theorem sample_preorder_nodup : (preorder sample).Nodup := by
  rw [sample_preorder]
  decide

theorem sample_reconstruct? :
    reconstruct? [9, 3, 5, 7, 6] [3, 5, 9, 6, 7] = some sample := by
  simpa only [sample_preorder, sample_inorder] using
    reconstruct?_traversals sample sample_preorder_nodup

theorem sample_reconstruct :
    reconstruct [9, 3, 5, 7, 6] [3, 5, 9, 6, 7] = sample := by
  simpa only [sample_preorder, sample_inorder] using
    reconstruct_traversals sample sample_preorder_nodup

theorem singleton_reconstruct [DecidableEq α] (a : α) :
    reconstruct [a] [a] = .node a .nil .nil := by
  simpa using reconstruct_traversals (.node a .nil .nil) (by simp)

theorem empty_labels : reconstruct ([] : List Empty) [] = .nil := reconstruct_nil_nil

theorem empty_mismatch : reconstruct? ([] : List Nat) [1] = none :=
  reconstruct?_nil_cons 1 []

theorem empty_mismatch_fallback : reconstruct ([] : List Nat) [1] = .nil :=
  reconstruct_of_none empty_mismatch

theorem missing_root : reconstruct? ([9] : List Nat) [3] = none :=
  reconstruct?_cons_of_not_mem 9 [] [3] (by simp)

theorem surplus_preorder : reconstruct? ([1, 2] : List Nat) [1] = none := by
  simp [reconstruct?_cons]

theorem surplus_inorder : reconstruct? ([1] : List Nat) [1, 2] = none := by
  simp [reconstruct?_cons]

/-- Matching multisets alone do not make these two lists valid traversals. -/
theorem same_labels_do_not_suffice :
    ([1, 2, 3] : List Nat).Perm [3, 1, 2] ∧
      reconstruct? ([1, 2, 3] : List Nat) [3, 1, 2] = none := by
  constructor
  · decide
  · simp [reconstruct?_cons]

/-- The general correctness law turns this distinct-label parse failure into
an impossibility result for any proposed common tree. -/
theorem same_labels_not_joint_traversals :
    ¬ ∃ t : BinaryTree Nat, preorder t = [1, 2, 3] ∧ inorder t = [3, 1, 2] := by
  rintro ⟨t, hpre, hino⟩
  have hn : (preorder t).Nodup := by
    rw [hpre]
    decide
  have hparse := reconstruct?_traversals t hn
  rw [hpre, hino, same_labels_do_not_suffice.2] at hparse
  cases hparse

def leftRepeated (a : α) : BinaryTree α := .node a (.node a .nil .nil) .nil

def rightRepeated (a : α) : BinaryTree α := .node a .nil (.node a .nil .nil)

theorem repeated_traversals (a : α) :
    preorder (leftRepeated a) = [a, a] ∧ preorder (rightRepeated a) = [a, a] ∧
      inorder (leftRepeated a) = [a, a] ∧ inorder (rightRepeated a) = [a, a] := by
  simp [leftRepeated, rightRepeated]

theorem repeated_trees_distinct (a : α) : leftRepeated a ≠ rightRepeated a := by
  intro h
  have hleft : (.node a .nil .nil : BinaryTree α) = .nil :=
    congrArg BinaryTree.left h
  cases hleft

theorem repeated_preorder_not_nodup (a : α) : ¬ (preorder (leftRepeated a)).Nodup := by
  simp [leftRepeated]

/-- The specified first-occurrence parser chooses the right-child shape. -/
theorem repeated_parser_choice [DecidableEq α] (a : α) :
    reconstruct [a, a] [a, a] = rightRepeated a := by
  simp [reconstruct, reconstruct?_cons, rightRepeated]

theorem repeated_left_not_recovered [DecidableEq α] (a : α) :
    reconstruct (preorder (leftRepeated a)) (inorder (leftRepeated a)) ≠ leftRepeated a := by
  rw [(repeated_traversals a).1, (repeated_traversals a).2.2.1, repeated_parser_choice]
  intro h
  exact repeated_trees_distinct a h.symm

end TreeReconstructionExamples
