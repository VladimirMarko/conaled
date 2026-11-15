import Applications.Resources.TakeWhileExtrema
import Examples.TakeWhileContract

/-! Importing callers connect the frozen native expectations to general extrema,
ordered prefix-fold laws and full measured suffix independence. -/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.TakeWhileExtremaExamples

open TakeWhileExtrema

def belowThree (n : Nat) : Bool := n < 3

/-- List.cons makes input order observable independently of the resource bill. -/
theorem ordered_failure : foldPrefix 1 belowThree List.cons [] [1, 2, 9, 4] = ([1, 2], 13) := by
  have h := foldPrefix_failure 1 belowThree List.cons [] [1, 2] 9 [4]
    (by simp [belowThree]) (by decide)
  simpa using h

theorem ordered_exhaustion : foldPrefix 1 belowThree List.cons [] [1, 2] = ([1, 2], 12) := by
  apply Prod.ext
  · rw [foldPrefix_value]
    rfl
  · rw [foldPrefix_work]
    rfl

/-- The observed work distinguishes failure from exhaustion with equal output. -/
example : (foldPrefix 1 belowThree List.cons [] [1, 2, 9, 4]).1 =
      (foldPrefix 1 belowThree List.cons [] [1, 2]).1 ∧
    (foldPrefix 1 belowThree List.cons [] [1, 2, 9, 4]).2 =
      (foldPrefix 1 belowThree List.cons [] [1, 2]).2 + 1 := by
  rw [ordered_failure, ordered_exhaustion]
  exact ⟨rfl, rfl⟩

/-- Arbitrarily long/different suffixes after 9 do not change either observation. -/
theorem suffix_pair (left right : List Nat) :
    foldPrefix 1 belowThree List.cons [] ([1, 2] ++ 9 :: left) =
      foldPrefix 1 belowThree List.cons [] ([1, 2] ++ 9 :: right) :=
  foldPrefix_suffix_independent 1 belowThree List.cons [] [1, 2] 9 left right
    (by simp [belowThree]) (by decide)

example (rest : List Nat) : foldPrefix 1 belowThree List.cons [] (9 :: rest) = ([], 3) := by
  simpa using foldPrefix_failure 1 belowThree List.cons [] [] 9 rest (by simp) (by decide)

example : foldPrefix 1 belowThree List.cons [] [] = ([], 2) :=
  foldPrefix_empty 1 belowThree List.cons []

example : ListFusion.takeWhile 1 1 1 id (bestInput 5) = ([], 2) := best_run 5
example : ListFusion.takeWhile 1 1 1 id (worstInput 5) = (worstInput 5, 16) := worst_run 5

/-- Fixed predicate, fixed size: both extrema bracket every input at that size. -/
example (xs : List Bool) :
    (ListFusion.takeWhile 1 1 1 id (bestInput xs.length)).2 ≤
      (ListFusion.takeWhile 1 1 1 id xs).2 ∧
    (ListFusion.takeWhile 1 1 1 id xs).2 ≤
      (ListFusion.takeWhile 1 1 1 id (worstInput xs.length)).2 :=
  ⟨best_minimum xs.length xs rfl, worst_maximum xs.length xs rfl⟩

/-- No eventual uniform linear lower bound even for this one fixed predicate. -/
theorem rejects_eventual_lower :
    ¬ ∃ C N : Nat, ∀ n, N ≤ n → n ≤ C * (ListFusion.takeWhile 1 1 1 id (bestInput n)).2 := by
  rintro ⟨C, N, h⟩
  obtain ⟨n, hn, hlt⟩ := best_eventual_lower_obstruction C N
  exact Nat.not_le_of_gt hlt (h n hn)

/-- Empty input prevents dropping the upper bound's positive-size qualification. -/
example (C : Nat) : ¬ (ListFusion.takeWhile 1 1 1 id (bestInput 0)).2 ≤ C * 0 := by
  rw [best_run]
  simp

example : foldPrefix 1 id List.cons [] (bestInput 5) = ([], 3) :=
  foldPrefix_best 1 List.cons [] 5

example : foldPrefix 1 id List.cons [] (worstInput 5) = (worstInput 5, 27) := by
  simpa using foldPrefix_worst 1 List.cons [] 5

example (n : Nat) (hn : 0 < n) :
    5 * n ≤ (foldPrefix 1 id List.cons [] (worstInput n)).2 ∧
      (foldPrefix 1 id List.cons [] (worstInput n)).2 ≤ 7 * n :=
  foldPrefix_worst_bounds List.cons [] n hn

end Resources.TakeWhileExtremaExamples
