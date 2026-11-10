import Examples.ScanFusion

/-!
# Suffix observations and reachable right-scan fusion

Ordered word concatenation detects direction mistakes. Word-length observation
and the existing even-state client exercise the same public suffix fusion law.
These are finite exact values, with no cost or lazy-demand claim.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuffixScan

open SquareKit.ListFusion

/-- Independently specified concatenations of every suffix, including the empty one. -/
theorem word_suffixes {α : Type*} (xs : List (List α)) :
    xs.scanr (· ++ ·) [] =
      (List.range (xs.length + 1)).map (fun n => (xs.drop n).flatten) := by
  rw [scanr_suffix_values]
  apply List.map_congr_left
  intro n _
  simpa using (List.foldr_append_eq_append (l := xs.drop n) (f := id) (l' := []))

theorem ordered_words :
    ([[1, 2], [3], [4, 5]] : List (List Nat)).scanr (· ++ ·) [] =
      [[1, 2, 3, 4, 5], [3, 4, 5], [4, 5], []] := by
  rw [word_suffixes]
  rfl

/-- Right-fold subtraction is deliberately nonassociative. -/
theorem subtraction_suffixes :
    ([10, 3, 2] : List Int).scanr (· - ·) 0 = [9, 1, 2, 0] := by
  rw [scanr_suffix_values]
  rfl

theorem seeded_empty : ([] : List Int).scanr (· - ·) 7 = [7] := by
  rw [scanr_suffix_values]
  rfl

/-- Output observation commutes with concatenation without equating words. -/
theorem word_lengths {α : Type*} (xs : List (List α)) :
    (xs.scanr (· ++ ·) []).map List.length =
      xs.scanr (fun word n => word.length + n) 0 := by
  apply scanr_reachable (fun (word acc : List α) => word ++ acc)
    (fun (word : List α) n => word.length + n) List.length (fun _ => True) [] trivial
  · intro _ _ _; trivial
  · intro _ _ _; exact List.length_append

theorem word_lengths_example :
    (([[1, 2], [3], [4, 5]] : List (List Nat)).scanr (· ++ ·) []).map List.length =
      [5, 3, 2, 0] := by
  rw [word_lengths, scanr_suffix_values]
  rfl

/-- The original suffix-list formulation uses the same standard scan. -/
theorem suffix_folds :
    ([10, 3, 2] : List Int).tails.map (List.foldr (· - ·) 0) = [9, 1, 2, 0] := by
  rw [foldr_tails_eq_scanr]
  exact subtraction_suffixes

/-- The existing parity invariant suffices at every suffix, as it does for a fold. -/
theorem restricted_scanr (xs : List Int) :
    (xs.scanr ScanFusion.doubleStep 0).map ScanFusion.replaceOdd =
      xs.scanr ScanFusion.doubleStep 0 :=
  scanr_reachable ScanFusion.doubleStep ScanFusion.doubleStep ScanFusion.replaceOdd
    (fun y => y % 2 = 0) 0 (by decide) ScanFusion.doubleStep_even
    ScanFusion.replaceOdd_step xs

theorem restricted_negative_example :
    (([-3, 4, 2] : List Int).scanr ScanFusion.doubleStep 0).map ScanFusion.replaceOdd =
      [6, 12, 4, 0] := by
  rw [restricted_scanr, scanr_suffix_values]
  rfl

/-- The initial invariant cannot be discarded, even for a one-element suffix scan. -/
theorem odd_seed_fails :
    (([1] : List Int).scanr ScanFusion.doubleStep 1).map ScanFusion.replaceOdd ≠
      ([1] : List Int).scanr ScanFusion.doubleStep (ScanFusion.replaceOdd 1) := by
  decide

end Examples.SuffixScan
