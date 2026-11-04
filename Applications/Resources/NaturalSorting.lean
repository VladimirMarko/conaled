import Applications.Sorting.Natural
import Applications.Resources.NaturalRunComparisons
import Applications.Resources.BottomUpSorting

/-!
# Comparisons in natural merge sort

The measured scanner supplies its actual returned runs to the measured ordinary
bottom-up merger. Only adjacent/head comparisons are observed. Builder creation
and application, list construction, control dispatch, key evaluation and machine
runtime are outside this tariff. The exact source counter, adaptive bound and
best case follow from the separately proved component observations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.NaturalSorting

open Applications.Sorting
universe u v
variable {α : Type u} {κ : Type v}

/-- Execute detection, then merge precisely the run list returned by that execution. -/
def run (lt cmp : α → α → Bool) (xs : List α) : Measured (List α) Nat :=
  Resources.bind (NaturalRunComparisons.runsRunBy lt xs) (BottomUpSorting.allRun cmp)

abbrev comparisons (lt cmp : α → α → Bool) (xs : List α) : Nat :=
  (run lt cmp xs).2

@[simp] theorem run_nil (lt cmp : α → α → Bool) : run lt cmp [] = ([], 0) := by
  simp [run, Resources.bind]

@[simp] theorem run_singleton (lt cmp : α → α → Bool) (a : α) :
    run lt cmp [a] = ([a], 0) := by
  simp [run, Resources.bind]

theorem run_value (lt cmp : α → α → Bool) (xs : List α) :
    (run lt cmp xs).1 = sortNaturalBy lt cmp xs := by
  simp only [run, Resources.bind_value, NaturalRunComparisons.runsRunBy_value,
    BottomUpSorting.allRun_value, sortNaturalBy]

theorem run_perm (lt cmp : α → α → Bool) (xs : List α) :
    (run lt cmp xs).1.Perm xs := by
  rw [run_value]
  exact sortNaturalBy_perm lt cmp xs

theorem run_length (lt cmp : α → α → Bool) (xs : List α) :
    (run lt cmp xs).1.length = xs.length := (run_perm lt cmp xs).length_eq

theorem run_multiset (lt cmp : α → α → Bool) (xs : List α) :
    ((run lt cmp xs).1 : Multiset α) = (xs : Multiset α) :=
  Multiset.coe_eq_coe.mpr (run_perm lt cmp xs)

theorem run_correct [LinearOrder κ] (key : α → κ) (xs : List α) :
    KeySorted key
        (run (fun a b => decide (key a < key b))
          (fun a b => decide (key a ≤ key b)) xs).1 ∧
      (run (fun a b => decide (key a < key b))
        (fun a b => decide (key a ≤ key b)) xs).1.Perm xs := by
  simp only [run_value]
  exact sortNaturalOn_correct key xs

@[simp] theorem comparisons_nil (lt cmp : α → α → Bool) :
    comparisons lt cmp [] = 0 := by simp [comparisons]

@[simp] theorem comparisons_singleton (lt cmp : α → α → Bool) (a : α) :
    comparisons lt cmp [a] = 0 := by simp [comparisons]

/-- Cnmsort uses the scan count and the merge count on the actual detected runs. -/
theorem comparisons_eq_scan_add_merge (lt cmp : α → α → Bool) (xs : List α) :
    comparisons lt cmp xs = NaturalRunComparisons.runsCountBy lt xs +
      BottomUpSorting.allComparisons cmp (runsBy lt xs) := by
  change (NaturalRunComparisons.runsRunBy lt xs).2 +
    (BottomUpSorting.allRun cmp (NaturalRunComparisons.runsRunBy lt xs).1).2 = _
  rw [NaturalRunComparisons.runsRunBy_value, NaturalRunComparisons.runsRunBy_cost]

theorem comparisons_eq_length_add_merge (lt cmp : α → α → Bool) (xs : List α) :
    comparisons lt cmp xs = xs.length - 1 +
      BottomUpSorting.allComparisons cmp (runsBy lt xs) := by
  rw [comparisons_eq_scan_add_merge, NaturalRunComparisons.runsCountBy_exact]

theorem run_exact (lt cmp : α → α → Bool) (xs : List α) :
    run lt cmp xs = (sortNaturalBy lt cmp xs,
      xs.length - 1 + BottomUpSorting.allComparisons cmp (runsBy lt xs)) := by
  apply Prod.ext
  · exact run_value lt cmp xs
  · exact comparisons_eq_length_add_merge lt cmp xs

/-- Scanning alone gives the lower bound, including natural subtraction at zero. -/
theorem comparisons_lower (lt cmp : α → α → Bool) (xs : List α) :
    xs.length - 1 ≤ comparisons lt cmp xs := by
  rw [comparisons_eq_length_add_merge]
  exact Nat.le_add_right _ _

/-- Adaptivity depends on the actual number of detected runs, independently of order laws. -/
theorem comparisons_le_adaptive (lt cmp : α → α → Bool) (xs : List α) :
    comparisons lt cmp xs ≤
      xs.length - 1 + xs.length * Nat.clog 2 (runsBy lt xs).length := by
  rw [comparisons_eq_length_add_merge]
  have hm := BottomUpSorting.allComparisons_le_clog cmp (runsBy lt xs)
  rw [runsBy_flatten_length] at hm
  exact Nat.add_le_add_left hm _

theorem comparisons_le_clog (lt cmp : α → α → Bool) (xs : List α) :
    comparisons lt cmp xs ≤ xs.length - 1 + xs.length * Nat.clog 2 xs.length := by
  exact (comparisons_le_adaptive lt cmp xs).trans
    (Nat.add_le_add_left
      (Nat.mul_le_mul_left xs.length (Nat.clog_mono_right 2 (runsBy_length_le lt xs))) _)

/-- Lemma 2.8 deliberately uses the weaker initial summand `n`, rather than `n-1`. -/
theorem comparisons_le_source (lt cmp : α → α → Bool) (xs : List α) :
    comparisons lt cmp xs ≤ xs.length + xs.length * Nat.clog 2 xs.length :=
  (comparisons_le_clog lt cmp xs).trans
    (Nat.add_le_add_right (Nat.sub_le xs.length 1) _)

theorem comparisons_le_of_length (lt cmp : α → α → Bool) (xs : List α)
    (n : Nat) (hlen : xs.length = n) :
    comparisons lt cmp xs ≤ n + n * Nat.clog 2 n := by
  simpa only [hlen] using comparisons_le_source lt cmp xs

/-- Cast the truncated natural scan count as a whole; the zero case never becomes `-1`. -/
theorem comparisons_le_adaptive_int_ceil (lt cmp : α → α → Bool) (xs : List α) :
    (comparisons lt cmp xs : ℤ) ≤ ((xs.length - 1 : Nat) : ℤ) +
      (xs.length : ℤ) * ⌈Real.logb 2 ((runsBy lt xs).length : ℝ)⌉ := by
  rw [BottomUpSorting.int_ceil_logb_two_nat]
  exact_mod_cast comparisons_le_adaptive lt cmp xs

/-- The printed integer-ceiling consequence includes empty and singleton lists. -/
theorem comparisons_le_int_ceil (lt cmp : α → α → Bool) (xs : List α) :
    (comparisons lt cmp xs : ℤ) ≤
      (xs.length : ℤ) + (xs.length : ℤ) * ⌈Real.logb 2 (xs.length : ℝ)⌉ := by
  rw [BottomUpSorting.int_ceil_logb_two_nat]
  exact_mod_cast comparisons_le_source lt cmp xs

theorem comparisons_le_int_ceil_of_length (lt cmp : α → α → Bool) (xs : List α)
    (n : Nat) (hlen : xs.length = n) :
    (comparisons lt cmp xs : ℤ) ≤ (n : ℤ) + (n : ℤ) * ⌈Real.logb 2 (n : ℝ)⌉ := by
  simpa only [hlen] using comparisons_le_int_ceil lt cmp xs

/-- No comparisons are needed to dispatch a sole run, even if the supplied merger is arbitrary. -/
theorem run_of_runs_eq_singleton (lt cmp : α → α → Bool) (xs ys : List α)
    (h : runsBy lt xs = [ys]) : run lt cmp xs = (ys, xs.length - 1) := by
  rw [run_exact, sortNaturalBy_of_runs_eq_singleton lt cmp xs ys h,
    h, BottomUpSorting.allComparisons_singleton, Nat.add_zero]

theorem run_of_ascending_chain (lt cmp : α → α → Bool) (xs : List α)
    (hne : xs ≠ []) (h : xs.IsChain (fun a b => lt b a = false)) :
    run lt cmp xs = (xs, xs.length - 1) :=
  run_of_runs_eq_singleton lt cmp xs xs (runsBy_of_ascending_chain lt xs hne h)

theorem run_of_descending_chain (lt cmp : α → α → Bool) (xs : List α)
    (hne : xs ≠ []) (h : xs.IsChain (fun a b => lt b a = true)) :
    run lt cmp xs = (xs.reverse, xs.length - 1) :=
  run_of_runs_eq_singleton lt cmp xs xs.reverse (runsBy_of_descending_chain lt xs hne h)

theorem mergeComparisons_of_sorted [LinearOrder κ] (key : α → κ)
    (cmp : α → α → Bool) (xs : List α) (hs : KeySorted key xs) (hne : xs ≠ []) :
    BottomUpSorting.allComparisons cmp (runsOn key xs) = 0 := by
  rw [runsOn_of_sorted key xs hs hne, BottomUpSorting.allComparisons_singleton]

/-- The attained best case is proved through the scanner and sole-run merger equations. -/
theorem run_of_sorted [LinearOrder κ] (key : α → κ) (cmp : α → α → Bool)
    (xs : List α) (hs : KeySorted key xs) (hne : xs ≠ []) :
    run (fun a b => decide (key a < key b)) cmp xs = (xs, xs.length - 1) :=
  run_of_runs_eq_singleton _ cmp xs xs (runsOn_of_sorted key xs hs hne)

/-- The count formula also covers the separate empty-input equation. -/
theorem comparisons_of_sorted [LinearOrder κ] (key : α → κ)
    (cmp : α → α → Bool) (xs : List α) (hs : KeySorted key xs) :
    comparisons (fun a b => decide (key a < key b)) cmp xs = xs.length - 1 := by
  cases xs with
  | nil => exact comparisons_nil _ cmp
  | cons a xs =>
    exact congrArg Prod.snd (run_of_sorted key cmp (a :: xs) hs (by simp))

theorem mergeComparisons_of_strictly_descending [LT κ] [DecidableLT κ]
    (key : α → κ) (cmp : α → α → Bool) (xs : List α)
    (hs : xs.Pairwise (fun a b => key b < key a)) (hne : xs ≠ []) :
    BottomUpSorting.allComparisons cmp (runsOn key xs) = 0 := by
  rw [runsOn_of_strictly_descending key xs hs hne, BottomUpSorting.allComparisons_singleton]

/-- Only the supplied strict comparisons are needed for the reversal consequence. -/
theorem run_of_strictly_descending [LT κ] [DecidableLT κ]
    (key : α → κ) (cmp : α → α → Bool) (xs : List α)
    (hs : xs.Pairwise (fun a b => key b < key a)) (hne : xs ≠ []) :
    run (fun a b => decide (key a < key b)) cmp xs = (xs.reverse, xs.length - 1) :=
  run_of_runs_eq_singleton _ cmp xs xs.reverse
    (runsOn_of_strictly_descending key xs hs hne)

/-- A positive linear lower estimate is asserted only from length two onward. -/
theorem length_le_twice_comparisons (lt cmp : α → α → Bool) (xs : List α)
    (hlen : 2 ≤ xs.length) : xs.length ≤ 2 * comparisons lt cmp xs := by
  have h := comparisons_lower lt cmp xs
  omega

theorem comparisons_le_two_clog (lt cmp : α → α → Bool) (xs : List α)
    (hlen : 2 ≤ xs.length) :
    comparisons lt cmp xs ≤ 2 * (xs.length * Nat.clog 2 xs.length) := by
  have hlog : 1 ≤ Nat.clog 2 xs.length :=
    Nat.clog_pos (by decide) (by omega)
  have hm := Nat.mul_le_mul_left xs.length hlog
  have hb := comparisons_le_source lt cmp xs
  omega

/-- The growth statement follows from the actual all-input comparison bound. -/
theorem comparisons_isBigO (lt cmp : α → α → Bool) (inputs : Nat → List α)
    (hlen : ∀ n, (inputs n).length = n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (comparisons lt cmp (inputs n) : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply Resources.isBigO_of_clog_two_bound (C := 2) (N := 2)
  intro n hn
  have hb := comparisons_le_two_clog lt cmp (inputs n) (by simpa only [hlen] using hn)
  simpa only [hlen] using hb

/-- A bounded number of detected runs gives a linear comparison upper bound. -/
theorem comparisons_isBigO_of_bounded_runs (lt cmp : α → α → Bool)
    (inputs : Nat → List α) (hlen : ∀ n, (inputs n).length = n)
    (r : Nat) (hr : ∀ n, (runsBy lt (inputs n)).length ≤ r) :
    Asymptotics.IsBigO Filter.atTop (fun n => (comparisons lt cmp (inputs n) : ℝ))
      (fun n => (n : ℝ)) := by
  apply Resources.isBigO_of_nat_bound _ (fun n => n) (1 + Nat.clog 2 r) 0
  intro n _
  calc
    comparisons lt cmp (inputs n) ≤
        n - 1 + n * Nat.clog 2 (runsBy lt (inputs n)).length := by
      simpa only [hlen] using comparisons_le_adaptive lt cmp (inputs n)
    _ ≤ n + n * Nat.clog 2 r :=
      Nat.add_le_add (Nat.sub_le n 1) (Nat.mul_le_mul_left n (Nat.clog_mono_right 2 (hr n)))
    _ = (1 + Nat.clog 2 r) * n := by ring

/-- Every length-indexed input family retains the scan lower bound eventually. -/
theorem size_isBigO_comparisons (lt cmp : α → α → Bool) (inputs : Nat → List α)
    (hlen : ∀ n, (inputs n).length = n) :
    Asymptotics.IsBigO Filter.atTop (fun n : Nat => (n : ℝ))
      (fun n => (comparisons lt cmp (inputs n) : ℝ)) := by
  apply Resources.isBigO_of_nat_bound (fun n => n) _ 2 2
  intro n hn
  have hb := length_le_twice_comparisons lt cmp (inputs n) (by simpa only [hlen] using hn)
  simpa only [hlen] using hb

theorem sorted_comparisons_isBigO [LinearOrder κ] (key : α → κ)
    (cmp : α → α → Bool) (inputs : Nat → List α)
    (hlen : ∀ n, (inputs n).length = n) (hs : ∀ n, KeySorted key (inputs n)) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (comparisons (fun a b => decide (key a < key b)) cmp (inputs n) : ℝ))
      (fun n => (n : ℝ)) := by
  apply Resources.isBigO_of_nat_bound _ (fun n => n) 1 0
  intro n _
  rw [comparisons_of_sorted key cmp (inputs n) (hs n), hlen n]
  omega

/-- Linear best-case comparison growth is eventual; zero/singleton counts remain zero. -/
theorem sorted_comparisons_isTheta [LinearOrder κ] (key : α → κ)
    (cmp : α → α → Bool) (inputs : Nat → List α)
    (hlen : ∀ n, (inputs n).length = n) (hs : ∀ n, KeySorted key (inputs n)) :
    Asymptotics.IsTheta Filter.atTop
      (fun n => (comparisons (fun a b => decide (key a < key b)) cmp (inputs n) : ℝ))
      (fun n => (n : ℝ)) :=
  ⟨sorted_comparisons_isBigO key cmp inputs hlen hs,
    size_isBigO_comparisons _ cmp inputs hlen⟩

end Resources.NaturalSorting
