import Applications.Probability.UniformThreeComposition

/-!
# Checked rejection sampling cases

The first block is rejected on `retryThenOne`. Two bits therefore exhaust fuel;
four bits return 1 at cursor 4. These finite computations exercise the same
machine whose unbounded law is uniform on three outcomes. The dependent second
interpretation is the sum of both samples, retaining the first value separately.
-/
namespace Examples.UniformThree
open Applications.Probability Applications.Probability.UniformThree
open MeasureTheory
open scoped ENNReal

/-- Bits 11 01 00 ...: one rejection, then output 1, then output 0. -/
def retryThenOne : CoinPaths.Tape := fun i => decide (i=0 ∨ i=1 ∨ i=3)

example : Progress.search (step retryThenOne) 2 (0,none) = none := by decide
example : Progress.search (step retryThenOne) 3 (0,none) = none := by decide
example : Progress.search (step retryThenOne) 4 (0,none) = some ((1,4),4) := by decide
example : Progress.search (step retryThenOne) 2 (2,none) = some ((1,4),2) := by decide
example : Progress.search (step retryThenOne) 1 (0,none) = none := by decide

/-- The checked finite search supplies a genuine operational derivation. -/
example : Progress.Evaluates (step retryThenOne) (0,none) (1,4) 4 :=
  Progress.search_sound (by decide : Progress.search (step retryThenOne) 4 (0,none) = some ((1,4),4))

example : Progress.search (step (fun _ => false)) 2 (0,none) = some ((0,2),2) := by decide
example : Progress.search (step (fun i => decide (i=0))) 2 (0,none) = some ((2,2),2) := by decide

/-- The second sample reads bits 4 and 5, returning 0 interpreted as 1+0.
Both first and final cursors and all six bit inspections are retained. -/
example : Progress.search (pairStep retryThenOne) 6 (.inl (0,none)) =
    some (((1,4),1,6),6) := by decide

/-- Reusing the same tape prefix changes the interpretation to 1+1, and
returns cursor 4 again instead of advancing to 6. -/
example : Progress.search (reusedPairStep 0 retryThenOne) 8 (.inl (0,none)) =
    some (((1,4),2,4),8) := by decide

/-- With fuel for only one block, each successful output has mass one quarter,
whereas the unbounded output law below has mass one third. -/
example (a : Fin 3) :
    CoinPaths.law {ω | Progress.search (step ω) 2 (0,none) = some ((a,2),2)} =
      (4⁻¹ : ℝ≥0∞) := by
  have he : {ω | Progress.search (step ω) 2 (0,none) = some ((a,2),2)} =
      {ω | Accept ω 0 0 a} := by
    ext ω
    constructor
    · intro h
      exact (evaluates_iff ω 0 0 a).mp (Progress.search_sound h)
    · intro h
      exact Progress.search_complete (evaluates_of_accept h) (by decide)
  rw [he,accept_mass]
  simp

example : CoinPaths.law (returns 0 2) = (3⁻¹ : ℝ≥0∞) := returns_mass 0 2
example : CoinPaths.law {ω | Progress.search (step ω) 4 (0,none) = none} =
    (4⁻¹ : ℝ≥0∞)^2 := search_timeout_mass 0 2
example : 0 < CoinPaths.law {ω | Progress.search (step ω) 4 (0,none) = none} :=
  search_timeout_pos 0 2
example : ¬ Progress.Terminates (step (fun _ => true)) (0,none) := all_true_diverges 0
example : ∀ᵐ ω ∂CoinPaths.law, Progress.Terminates (step ω) (0,none) := ae_terminates 0

/-- A concrete full joint output separates fresh suffix use from tape reuse. -/
example : CoinPaths.law (pairReturns 0 0 1) = (9⁻¹ : ℝ≥0∞) ∧
    CoinPaths.law (reusedPairReturns 0 0 1) = 0 := fresh_ne_reused 0

/-- First output 2 after one retry, then output 0 without retry: the interpreted
sum is 2 and the exact work is six bit inspections. -/
example : ProbabilityProgress.results CoinPaths.law pairStep (.inl (0,none))
    {Sum.inr (((2,4),2,6),6)} = (4⁻¹ : ℝ≥0∞)^2 * 4⁻¹ := by
  simpa using pair_results_atom 0 1 0 2 0

/-- Sum 4 is impossible when the first output is 0. -/
example : pairReturns 0 0 4 = ∅ :=
  pairReturns_outside 0 0 4 (by intro b; have := b.isLt; simp only [Fin.val_zero]; omega)

/-- Freshness includes a predicate on retry count as well as result, and an
arbitrary measurable event of the entire infinite suffix. -/
example (B : Set CoinPaths.Tape) (hB : MeasurableSet B) :
    CoinPaths.law (selectedSuffix 0 (fun n a => n=1 ∧ a=2) B) =
      CoinPaths.law (selected 0 (fun n a => n=1 ∧ a=2)) * CoinPaths.law B :=
  random_cursor_fresh 0 _ B hB

end Examples.UniformThree
