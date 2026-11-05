import Applications.Trees.BasicObservations

/-! Worked observations of the Chapter 4 tree carrier.
The three-node example has independently expected inorder [3,9,7] and
preorder [9,3,7]. Repeated labels distinguish structural containment from
equality of the label set, even when both traversals also agree.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeBasicObservationsExamples
open Trees

/-- The source's root 9 with children 3 and 7. -/
def sample : BinaryTree Nat :=
  .node 9 (.node 3 .nil .nil) (.node 7 .nil .nil)

theorem sample_preorder : preorder sample = [9, 3, 7] := by
  simp [sample]

theorem sample_inorder : inorder sample = [3, 9, 7] := by
  simp [sample]

theorem sample_setTree : setTree sample = {3, 9, 7} := by
  ext x
  simp [sample, or_assoc]

theorem sample_numNodes : sample.numNodes = 3 := rfl

/-- The length claim is connected to the public observation theorem. -/
theorem sample_preorder_length : (preorder sample).length = 3 := by
  rw [preorder_length, sample_numNodes]

/-- Explicit preorder membership transfers to the independent set observation. -/
theorem sample_contains_seven : 7 ∈ setTree sample := by
  apply (mem_preorder_iff_mem_setTree 7 sample).mp
  rw [sample_preorder]
  simp

/-- The other membership bridge rules out a label absent from inorder. -/
theorem sample_excludes_eight : 8 ∉ setTree sample := by
  intro h
  have hi : 8 ∈ inorder sample := (mem_inorder_iff_mem_setTree 8 sample).mpr h
  rw [sample_inorder] at hi
  simp at hi

/-- A noninjective map retains the three visits, even though all labels coincide. -/
theorem sample_constant_map :
    preorder (sample.map (fun _ : Nat => (5 : Nat))) = [5, 5, 5] := by
  rw [preorder_map, sample_preorder]
  rfl

theorem sample_left_subtree :
    (.node 3 .nil .nil : BinaryTree Nat) ∈ subtrees sample := by
  exact Subtree.left 9 (Subtree.refl (.node 3 .nil .nil))

/-- Whole-subtree containment composes through one more enclosing root. -/
theorem nested_left_subtree :
    (.node 3 .nil .nil : BinaryTree Nat) ∈ subtrees (.node 20 sample .nil) := by
  apply mem_subtrees_iff.mpr
  exact Subtree.trans (mem_subtrees_iff.mp sample_left_subtree)
    (Subtree.left 20 (Subtree.refl sample))

theorem sample_has_empty_subtree :
    (.nil : BinaryTree Nat) ∈ subtrees sample := nil_mem_subtrees sample

theorem sample_has_self_subtree : sample ∈ subtrees sample := self_mem_subtrees sample

/-- Repeated labels on the left branch. -/
def leftRepeated : BinaryTree Nat := .node 5 (.node 5 .nil .nil) .nil

/-- The same repeated labels on the right branch. -/
def rightRepeated : BinaryTree Nat := .node 5 .nil (.node 5 .nil .nil)

theorem repeated_traversals :
    preorder leftRepeated = [5, 5] ∧ preorder rightRepeated = [5, 5] ∧
      inorder leftRepeated = [5, 5] ∧ inorder rightRepeated = [5, 5] := by
  simp [leftRepeated, rightRepeated]

theorem repeated_sets :
    setTree leftRepeated = {5} ∧ setTree rightRepeated = {5} := by
  constructor <;> ext x <;> simp [leftRepeated, rightRepeated]

theorem repeated_trees_distinct : leftRepeated ≠ rightRepeated := by
  intro h
  have hl : (.node 5 .nil .nil : BinaryTree Nat) = .nil :=
    congrArg BinaryTree.left h
  cases hl

theorem leftRepeated_not_subtree_rightRepeated :
    ¬ Subtree leftRepeated rightRepeated := by
  simp [leftRepeated, rightRepeated, subtree_node_iff]

/-- Equality of value sets cannot replace structural containment. -/
theorem same_set_not_subtree :
    setTree leftRepeated = setTree rightRepeated ∧
      ¬ Subtree leftRepeated rightRepeated :=
  ⟨repeated_sets.1.trans repeated_sets.2.symm, leftRepeated_not_subtree_rightRepeated⟩

/-- An uninhabited label type still has the empty tree and its observations. -/
theorem empty_label_observations :
    setTree (.nil : BinaryTree Empty) = ∅ ∧
      preorder (.nil : BinaryTree Empty) = [] ∧
      subtrees (.nil : BinaryTree Empty) = {.nil} :=
  ⟨setTree_nil, preorder_nil, subtrees_nil⟩

end TreeBasicObservationsExamples
