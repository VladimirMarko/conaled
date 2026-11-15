import Applications.Trees.WeightedPaths

/-! Worked natural weighted-path calculations through the public offset law.
The branching sample has weight sum 15 and weighted path length 27. A chain
with the same weights has path length 34. At incoming depth 2 their respective
values are 57 and 64, exposing the distinction between weight and depth.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeWeightedPathsExamples
open Trees

/-- Weights 3 at the root and 5,7 at depth one. -/
def sample : BinaryTree Nat :=
  .node 3 (.node 5 .nil .nil) (.node 7 .nil .nil)

theorem sample_sumTree : sumTree sample = 15 := by
  simp [sample]

/-- The independent node-depth calculation is `3 + 2*5 + 2*7 = 27`. -/
theorem sample_wpl : wpl sample = 27 := by
  simp [sample]

theorem sample_wpl0 : wpl0 sample = 27 := by
  rw [wpl0_eq_wpl, sample_wpl]

/-- A symbolic depth specialization consumes the universal offset theorem. -/
theorem sample_at_depth (d : Nat) : wpld d sample = d * 15 + 27 := by
  rw [wpld_eq_offset, sample_sumTree, sample_wpl]

/-- Direct weights at incoming depth two give `3*3 + 4*5 + 4*7 = 57`. -/
theorem sample_at_depth_two : wpld 2 sample = 57 := by
  calc
    wpld 2 sample = 2 * 15 + 27 := sample_at_depth 2
    _ = 57 := by rfl

/-- The same weights at depths zero, one and two along the left branch. -/
def chain : BinaryTree Nat :=
  .node 3 (.node 5 (.node 7 .nil .nil) .nil) .nil

theorem chain_sumTree : sumTree chain = 15 := by
  simp [chain]

/-- The independent node-depth calculation is `3 + 2*5 + 3*7 = 34`. -/
theorem chain_wpl : wpl chain = 34 := by
  simp [chain]

theorem chain_wpl0 : wpl0 chain = 34 := by
  rw [wpl0_eq_wpl, chain_wpl]

theorem chain_at_depth_two : wpld 2 chain = 64 := by
  calc
    wpld 2 chain = 2 * sumTree chain + wpl chain := wpld_eq_offset 2 chain
    _ = 2 * 15 + 34 := by rw [chain_sumTree, chain_wpl]
    _ = 64 := by rfl

/-- Equal total weights do not determine the weighted path length. -/
theorem same_total_different_path_length :
    sumTree sample = sumTree chain ∧ wpl0 sample < wpl0 chain := by
  constructor
  · rw [sample_sumTree, chain_sumTree]
  · rw [sample_wpl0, chain_wpl0]
    decide

/-- The root contributes its weight, rather than weight times depth zero. -/
theorem singleton_weight (w : Nat) :
    wpl0 (.node w .nil .nil) = w := by
  simp [wpl0_eq_wpl]

theorem singleton_seven : wpl0 (.node 7 .nil .nil) = 7 := singleton_weight 7

/-- A zero-weight root still increases its child's weighted depth. -/
theorem zero_root_seven_child : wpl0 (.node 0 (.node 7 .nil .nil) .nil) = 14 := by
  simp [wpl0_eq_wpl]

theorem empty_observations (d : Nat) :
    sumTree .nil = 0 ∧ wpld d .nil = 0 ∧ wpl0 .nil = 0 := by
  simp [wpl0_eq_wpl]

end TreeWeightedPathsExamples
