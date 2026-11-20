import Applications.Resources.CollisionGrowth

/-! Small endpoints and shifted-key cases for the collision growth adapters. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.CollisionGrowth

open Resources.CollisionGrowth
open Numerals.PositiveKeys Numerals.PositiveArithmetic

theorem small_logarithmic_scales :
    logScale 0 = 2 ∧ logScale 1 = 3 ∧ logScale 2 = 4 := by decide

/-- The largest allowed key at n=4 is7, whose shifted numeral is8, with4 bits. -/
theorem upper_interval_key :
    numeric (encode 7) = 8 ∧ bitLength (encode 7) = 4 ∧
      bitLength (encode 7) + 1 ≤ logScale 4 := by
  refine ⟨by decide, by decide, ?_⟩
  exact encoded_bitLength_le 4 7 (by decide)

theorem empty_distinct_log : 1 + (0 + 1 : Nat).log2 ≤ logScale 0 :=
  distinct_log_le 0 0 (Nat.le_refl 0)

theorem largest_distinct_log (n : Nat) : 1 + (n + 1).log2 ≤ logScale n :=
  distinct_log_le n n (Nat.le_refl n)

/-- All four programs observe one final loop terminal on empty input. -/
theorem empty_work :
    unaryWork [] = 1 ∧ signedHistoryWork [] = 1 ∧ redBlackWork [] = 1 ∧ trieWork [] = 1 := by
  decide

/-- First insertion: history lookup/cell/loop plus terminal costs four;
the accepted RB operations cost five plus two overhead, and the shortest
positive trie performs one lookup, one insertion and one construction. -/
theorem first_zero_key_work :
    unaryWork [0] = 4 ∧ signedHistoryWork [0] = 4 ∧
      redBlackWork [0] = 7 ∧ trieWork [0] = 5 := by
  decide

/-- The second fresh unary query compares3 with2 in three recursive calls;
the signed comparison spends four. The trie uses encoded keys3 and4. -/
theorem two_distinct_interval_work :
    unaryWork [2, 3] = 11 ∧ signedHistoryWork [2, 3] = 12 ∧ trieWork [2, 3] = 16 := by
  decide

theorem repeated_keys_agree :
    (Resources.CollisionHistory.unaryRun [5, 5, 5]).1.1 = 2 ∧
    ((Resources.CollisionHistory.signedRun
      ([5, 5, 5].map (fun key : Nat => (key : ZNum)))).1.1 : Nat) = 2 ∧
    ((Resources.CollisionRedBlack.signedCollisions
      ([5, 5, 5].map (fun key : Nat => (key : ZNum)))).1.1 : Nat) = 2 ∧
    (Resources.PositiveTrie.collisionsRun ([5, 5, 5].map encode)).1 = 2 := by
  have count : Search.Collisions.count [5, 5, 5] = 2 := by decide
  simpa only [count] using represented_counts [5, 5, 5]

/-- The largest legal natural key still needs the positive encoding offset. -/
theorem half_open_upper_key (n : Nat) (positive : 0 < n) :
    numeric (encode (2 * n - 1)) = 2 * n ∧
      bitLength (encode (2 * n - 1)) + 1 ≤ logScale n := by
  refine ⟨?_, encoded_bitLength_le n (2 * n - 1) (by omega)⟩
  rw [numeric_encode]
  omega

theorem four_bounded_programs (n : Nat) (keys : List Nat) (length : keys.length ≤ n)
    (bounded : ∀ key ∈ keys, key < 2 * n) :
    unaryWork keys ≤ 4 * (n + 1) ^ 3 ∧
    signedHistoryWork keys ≤ 8 * ((n + 1) ^ 2 * logScale n) ∧
    redBlackWork keys ≤ 180 * ((n + 1) * logScale n ^ 2) ∧
    trieWork keys ≤ 6 * ((n + 1) * logScale n) :=
  ⟨unaryWork_bound n keys length bounded, signedHistoryWork_bound n keys length bounded,
    redBlackWork_bound n keys length bounded, trieWork_bound n keys length bounded⟩

theorem unary_lower_small_endpoints :
    unaryWork (List.range' 0 0) = 1 ∧ unaryWork (List.range' 1 1) = 4 ∧
      unaryWork (List.range' 2 2) = 11 ∧ unaryWork (List.range' 3 3) = 26 := by
  decide

/-- The finite lower and upper expressions are both for the same measured run. -/
theorem unary_interval_sandwich (n : Nat) :
    (n + 1) * n * (n - 1) / 2 ≤ unaryWork (List.range' n n) ∧
      unaryWork (List.range' n n) ≤ 4 * (n + 1) ^ 3 := unary_interval_bounds n

theorem unary_interval_tight :
    Asymptotics.IsTheta Filter.atTop
      (fun n : Nat => (unaryWork (List.range' n n) : ℝ)) (fun n => (n : ℝ) ^ 3) :=
  unary_interval_isTheta

theorem binary_history_interval_upper :
    Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => (signedHistoryWork (List.range' n n) : ℝ))
      (fun n => (n : ℝ) ^ 2 * Real.logb 2 n) :=
  signedHistory_isBigO (fun n => List.range' n n) (by intro n; simp) interval_key_bound

theorem redblack_interval_upper :
    Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => (redBlackWork (List.range' n n) : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n ^ 2) :=
  redBlack_isBigO (fun n => List.range' n n) (by intro n; simp) interval_key_bound

theorem trie_interval_upper :
    Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => (trieWork (List.range' n n) : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) :=
  trie_isBigO (fun n => List.range' n n) (by intro n; simp) interval_key_bound

end Examples.CollisionGrowth
