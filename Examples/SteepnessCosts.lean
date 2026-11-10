import Applications.Resources.Steepness
import Applications.Resources.TreeFlattening.Observation

/-! Measured steepness consumes actual ordered forest outputs and retains their work. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SteepnessCosts
open Squares Resources Resources.Steepness Resources.TreeFlattening
open Resources.RandomAccessCosts Sequences.Steepness

/-- A preceding measured producer retains its charge when the decision runs. -/
def measuredDecision
    (checker : Square ⟨List Int, List Int, id⟩ ⟨Measured Bool Nat, Bool, Prod.fst⟩) :
    Square (measuredSequence Int) ⟨Measured Bool Nat, Bool, Prod.fst⟩ where
  impl result := bind result checker.impl
  spec := checker.spec
  commutes result := checker.commutes result.1

/-- Both decisions consume the list actually produced by the existing stack traversal. -/
def flattenDecision
    (checker : Square ⟨List Int, List Int, id⟩ ⟨Measured Bool Nat, Bool, Prod.fst⟩) :=
  Squares.compose (measuredDecision checker) (stackSquare (α := Int))

theorem flattenDecision_value
    (checker : Square ⟨List Int, List Int, id⟩ ⟨Measured Bool Nat, Bool, Prod.fst⟩)
    (ts : List (RandomAccess.Tree Int)) :
    ((flattenDecision checker).impl ts).1 = checker.spec (ts.flatMap RandomAccess.fromT) :=
  (flattenDecision checker).commutes ts

/-- The checker charge comes from its execution on the produced ordered fringe. -/
theorem flattenDecision_work
    (checker : Square ⟨List Int, List Int, id⟩ ⟨Measured Bool Nat, Bool, Prod.fst⟩)
    (ts : List (RandomAccess.Tree Int)) :
    ((flattenDecision checker).impl ts).2 =
      pending (ts.map RandomAccess.erase) + 1 +
        (checker.impl (ts.flatMap RandomAccess.fromT)).2 := by
  change (cachedFromTsWithCost ts).2 + (checker.impl (cachedFromTsWithCost ts).1).2 = _
  rw [cachedFromTsWithCost_exact]

theorem flatten_naive_correct (ts : List (RandomAccess.Tree Int)) :
    ((flattenDecision naiveSquare).impl ts).1 = true ↔ Steep (ts.flatMap RandomAccess.fromT) := by
  rw [flattenDecision_value]
  exact steep_correct _

theorem flatten_tupled_correct (ts : List (RandomAccess.Tree Int)) :
    ((flattenDecision tupledSquare).impl ts).1 = true ↔ Steep (ts.flatMap RandomAccess.fromT) := by
  rw [flattenDecision_value]
  exact steep_correct _

theorem flatten_decisions_agree (ts : List (RandomAccess.Tree Int)) :
    ((flattenDecision naiveSquare).impl ts).1 = ((flattenDecision tupledSquare).impl ts).1 := by
  rw [flattenDecision_value, flattenDecision_value]
  rfl

theorem flatten_tupled_work_le (ts : List (RandomAccess.Tree Int)) :
    ((flattenDecision tupledSquare).impl ts).2 ≤
      pending (ts.map RandomAccess.erase) + 1 +
        (3 * (ts.flatMap RandomAccess.fromT).length + 1) := by
  rw [flattenDecision_work]
  exact Nat.add_le_add_left (tupled_work_le _) _

theorem signed_sum : sumRun [-3, 0, 8] = (5, 7) := by
  apply Prod.ext
  · rw [sumRun_value]; rfl
  · exact sumRun_work _

private theorem three_steep : Steep [4, 2, 1] :=
  (steep_correct _).mp (by decide)

theorem naive_three : naive [4, 2, 1] = (true, 16) := by
  apply Prod.ext
  · exact (naive_correct _).mpr three_steep
  · exact naive_work_eq_of_steep _ three_steep

theorem tupled_three : tupled [4, 2, 1] = (true, 9) := by
  apply Prod.ext
  · exact (tupled_correct _).mpr three_steep
  · exact tupled_work_eq_of_steep 4 [2, 1] three_steep

theorem naive_empty : naive [] = (true, 1) := rfl
theorem tupled_empty : tupled [] = (true, 1) := rfl

theorem empty_needs_constant : ¬ (tupled []).2 ≤ 3 * ([] : List Int).length := by
  rw [tupled_empty]
  decide

theorem naive_singleton : naive [1] = (true, 4) := by
  have h : Steep [1] := (steep_correct _).mp (by decide)
  exact Prod.ext ((naive_correct _).mpr h) (naive_work_eq_of_steep _ h)

theorem tupled_singleton : tupled [1] = (true, 3) := by
  have h : Steep [1] := (steep_correct _).mp (by decide)
  exact Prod.ext ((tupled_correct _).mpr h) (tupled_work_eq_of_steep 1 [] h)

theorem zero_fails : naive [0] = (false, 3) ∧ tupled [0] = (false, 3) :=
  ⟨naive_cons_failure 0 [] (by decide), tupled_cons_failure 0 [] (by decide)⟩

theorem negative_fails : naive [-1] = (false, 3) ∧ tupled [-1] = (false, 3) :=
  ⟨naive_cons_failure (-1) [] (by decide), tupled_cons_failure (-1) [] (by decide)⟩

theorem first_failure : naive [0, 100, 200] = (false, 7) ∧
    tupled [0, 100, 200] = (false, 7) :=
  ⟨naive_cons_failure 0 [100, 200] (by decide),
    tupled_cons_failure 0 [100, 200] (by decide)⟩

theorem tie_fails : naive [3, 2, 1] = (false, 7) ∧ tupled [3, 2, 1] = (false, 7) :=
  ⟨naive_cons_failure 3 [2, 1] (by decide), tupled_cons_failure 3 [2, 1] (by decide)⟩

theorem no_unconditional_strict_improvement :
    ¬ ∀ xs : List Int, (tupled xs).2 < (naive xs).2 := by
  intro h
  have hf := h [0, 100, 200]
  rw [first_failure.1, first_failure.2] at hf
  exact Nat.lt_irrefl _ hf

theorem quadratic_equality_needs_steep :
    ¬ (naive [3, 2, 1]).2 = (([3, 2, 1] : List Int).length + 1) ^ 2 := by
  rw [tie_fails.1]
  decide

theorem witnessed_comparison (n : Nat) :
    ∃ xs : List Int, xs.length = n + 1 ∧ Steep xs ∧
      (naive xs).2 = (n + 2) * (n + 2) ∧ (tupled xs).2 = 3 * (n + 1) := by
  refine ⟨worstInput (n + 1), worstInput_length _, worstInput_steep _, ?_,
    tupled_worstInput_work n⟩
  simpa [Nat.add_assoc] using naive_worstInput_work (n + 1)

private def threeLeaves (a b c : Int) : List (RandomAccess.Tree Int) :=
  [.node 3 (.leaf a) (.node 2 (.leaf b) (.leaf c))]

private theorem threeLeaves_fringe (a b c : Int) :
    (threeLeaves a b c).flatMap RandomAccess.fromT = [a, b, c] := rfl

private theorem threeLeaves_work (a b c : Int) :
    pending ((threeLeaves a b c).map RandomAccess.erase) + 1 = 6 := rfl

theorem produced_naive : (flattenDecision naiveSquare).impl (threeLeaves 4 2 1) =
    (true, 22) := by
  apply Prod.ext
  · exact (flatten_naive_correct _).mpr (by rw [threeLeaves_fringe]; exact three_steep)
  · rw [flattenDecision_work, threeLeaves_work, threeLeaves_fringe]
    change 6 + (naive [4, 2, 1]).2 = 22
    rw [naive_three]
    decide

theorem produced_tupled : (flattenDecision tupledSquare).impl (threeLeaves 4 2 1) =
    (true, 15) := by
  apply Prod.ext
  · exact (flatten_tupled_correct _).mpr (by rw [threeLeaves_fringe]; exact three_steep)
  · rw [flattenDecision_work, threeLeaves_work, threeLeaves_fringe]
    change 6 + (tupled [4, 2, 1]).2 = 15
    rw [tupled_three]
    decide

theorem produced_failure : (flattenDecision naiveSquare).impl (threeLeaves 0 100 200) =
    (false, 13) ∧ (flattenDecision tupledSquare).impl (threeLeaves 0 100 200) =
    (false, 13) := by
  constructor
  · apply Prod.ext
    · rw [flattenDecision_value, threeLeaves_fringe]
      change steep [0, 100, 200] = false
      rw [← naive_value, first_failure.1]
    · rw [flattenDecision_work, threeLeaves_work, threeLeaves_fringe]
      change 6 + (naive [0, 100, 200]).2 = 13
      rw [first_failure.1]
      decide
  · apply Prod.ext
    · rw [flattenDecision_value, threeLeaves_fringe]
      change steep [0, 100, 200] = false
      rw [← naive_value, first_failure.1]
    · rw [flattenDecision_work, threeLeaves_work, threeLeaves_fringe]
      change 6 + (tupled [0, 100, 200]).2 = 13
      rw [first_failure.2]
      decide

theorem produced_empty : (flattenDecision naiveSquare).impl [] = (true, 2) ∧
    (flattenDecision tupledSquare).impl [] = (true, 2) := by
  constructor
  · apply Prod.ext
    · exact (flatten_naive_correct _).mpr steep_nil
    · rw [flattenDecision_work]; rfl
  · apply Prod.ext
    · exact (flatten_tupled_correct _).mpr steep_nil
    · rw [flattenDecision_work]; rfl

end Examples.SteepnessCosts
