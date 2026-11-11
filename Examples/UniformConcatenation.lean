import Applications.Resources.UniformConcatenation

/-! Ordered full-fold consumers and separating finite cost cases for #468. -/
namespace Examples.UniformConcatenation
open Resources Resources.ListFusion Resources.UniformConcatenation

def blocks : List (List Nat) := [[1,2],[3,4]]

theorem blocks_uniform : Uniform 2 blocks := by
  intro xs hx
  simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> rfl

/-- The independent meaning retains order, not only a commutative aggregate. -/
theorem ordered_values :
    (foldConcat 1 List.cons [] blocks).1 = [1,2,3,4] ∧
    (foldLeftConcat 1 List.cons [] blocks).1 = [1,2,3,4] := by
  constructor
  · rw [foldConcat_value]; rfl
  · rw [foldLeftConcat_value]; rfl

theorem pipeline_bills :
    (foldConcat 1 List.cons [] blocks).2 = 22 ∧
    (foldLeftConcat 1 List.cons [] blocks).2 = 18 := by
  constructor
  · simpa [blocks] using foldConcat_uniform_work 1 2 List.cons [] blocks blocks_uniform
  · simpa [blocks] using foldLeftConcat_uniform_work 1 2 List.cons [] blocks blocks_uniform

/-- Consume the old fusion result via the new uniform specialization. -/
theorem fusion_bill : (foldConcat 1 List.cons [] blocks).2 =
    (foldConcatFused 1 List.cons [] blocks).2 + 9 := by
  simpa [blocks] using uniform_fusion_saving 1 2 List.cons [] blocks blocks_uniform

theorem accumulator_bill (acc : List Nat) :
    (concat2Acc acc blocks).2 = 4*acc.length+9 := by
  have h := concat2Acc_uniform_exact 2 acc blocks blocks_uniform
  simp only [blocks, List.length_cons, List.length_nil] at h ⊢
  omega

theorem producer_empty : concat1 ([] : List (List Nat)) = ([],1) ∧
    concat2 ([] : List (List Nat)) = ([],1) := no_blocks

theorem empty_payload (m : Nat) :
    (concat1 (List.replicate m ([] : List Nat))).2 = 2*m+1 ∧
    (concat2 (List.replicate m ([] : List Nat))).2 = 2*m+1 := empty_blocks_exact m

theorem single_producer (xs : List Nat) : (concat2 [xs]).2 = 3 :=
  concat2_single_block xs

theorem single_pipeline (xs : List Nat) :
    (foldLeftConcat 1 List.cons [] [xs]).2 = 2*xs.length+4 := by
  simpa using foldLeftConcat_single 1 List.cons [] xs

theorem no_uniform_payload_lower (c : Nat) :
    ∃ xs : List Nat, c * (concat2 [xs]).2 < xs.length := single_block_lower_obstruction c

def shortFirst : List (List Nat) := [[0],[1,2,3]]
def longFirst : List (List Nat) := [[0,1,2],[3]]

theorem same_sizes_different_work :
    shortFirst.length = longFirst.length ∧
    shortFirst.flatten.length = longFirst.flatten.length ∧
    (concat2 shortFirst).2 = 7 ∧ (concat2 longFirst).2 = 11 := by decide

theorem size_summary_cannot_recover :
    ¬ ∃ cost : Nat → Nat → Nat, ∀ xss : List (List Nat),
      cost xss.length xss.flatten.length = (concat2 xss).2 := by
  rintro ⟨cost,h⟩
  have hs := h shortFirst
  have hl := h longFirst
  have sizes := same_sizes_different_work
  rw [sizes.1, sizes.2.1, sizes.2.2.1] at hs
  rw [sizes.2.2.2] at hl
  omega

def threeBlocks : List (List Nat) := [[1,2],[3,4],[5,6]]

theorem three_uniform : Uniform 2 threeBlocks := by
  intro xs hx
  simp only [threeBlocks, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> rfl

theorem association_tie :
    (concat1 threeBlocks).2 = 19 ∧ (concat2 threeBlocks).2 = 19 := by
  have hr := concat1_uniform_exact 2 threeBlocks three_uniform
  have hl := concat2_uniform_exact 2 threeBlocks three_uniform
  simp only [threeBlocks, List.length_cons, List.length_nil] at hr hl ⊢
  omega

/-- Both constants are shared across all block counts and payload sizes. -/
theorem uniform_bounds (n : Nat) (xss : List (List Nat)) (h : Uniform n xss)
    (hm : 2 ≤ xss.length) (hn : 1 ≤ n) :
    (2*(xss.length*n) ≤ (concat1 xss).2 ∧
      (concat1 xss).2 ≤ 5*(xss.length*n)) ∧
    (xss.length*xss.length*n ≤ 2*(concat2 xss).2 ∧
      (concat2 xss).2 ≤ 3*(xss.length*xss.length*n)) :=
  ⟨concat1_uniform_theta n xss h (by omega) hn, concat2_uniform_theta n xss h hm hn⟩

end Examples.UniformConcatenation
