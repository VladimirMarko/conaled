import Applications.Trees.Levels

/-! Independent ordered-level examples, including an asymmetric tree whose
right branch has a deeper unmatched level, repeated labels, and an empty label
type. Exact observations are connected to the universal collector laws.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeLevelsExamples
open Trees

def sample : BinaryTree Nat :=
  .node 9
    (.node 3 (.node 8 .nil .nil) .nil)
    (.node 7 (.node 4 .nil (.node 6 .nil .nil)) (.node 5 .nil .nil))

theorem sample_levels : levels sample = [[9], [3, 7], [8, 4, 5], [6]] := rfl

theorem sample_height : sample.height = 4 := rfl

theorem sample_levels_length : (levels sample).length = 4 := by
  rw [levels_length, sample_height]

theorem sample_level_two : level sample 2 = [8, 4, 5] := by
  rw [← levels_getD sample 2, sample_levels]
  rfl

theorem sample_index_two : (levels sample)[2]? = some [8, 4, 5] := by
  rw [levels_getElem? sample 2 (by decide), sample_level_two]

theorem sample_level_four : level sample 4 = [] := by
  rw [← levels_getD sample 4, sample_levels]
  rfl

def repeated : BinaryTree Nat :=
  .node 5 (.node 5 .nil .nil) (.node 5 .nil .nil)

theorem repeated_levels : levels repeated = [[5], [5, 5]] := rfl

theorem repeated_level_one : level repeated 1 = [5, 5] := by
  rw [← levels_getD repeated 1, repeated_levels]
  rfl

theorem repeated_index_one : (levels repeated)[1]? = some [5, 5] := by
  rw [levels_getElem? repeated 1 (by decide), repeated_level_one]

theorem empty_label_levels : levels (.nil : BinaryTree Empty) = [] := levels_nil

theorem empty_label_length : (levels (.nil : BinaryTree Empty)).length = 0 :=
  levels_length .nil

theorem empty_label_level (k : Nat) : level (.nil : BinaryTree Empty) k = [] := by
  rw [← levels_getD (.nil : BinaryTree Empty) k, empty_label_levels]
  simp

end TreeLevelsExamples
