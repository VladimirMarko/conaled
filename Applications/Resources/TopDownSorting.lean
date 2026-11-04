import Applications.Sorting.TopDown
import Applications.Resources.ListMerge
import Applications.Resources.Growth
import Mathlib.Data.Nat.Log

/-!
# Comparisons in floor-left top-down merge sort

The FDSA §2.4 execution sorts each actual contiguous half, then supplies the
returned lists to the existing measured merge. Only head comparisons are
observed. Sorting entries, splitting traversals and primitive list construction
are uncharged in this explicitly separate comparison model. Its scalar
projection has the source's handwritten `C_msort` equations; no second sorting
execution is performed to manufacture the observation.

The bound for every length uses the standard natural ceiling logarithm. The
printed sharper real-log statement retains its power-of-two premise.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.TopDownSorting

open Applications.Sorting
universe u v
variable {α : Type u} {κ : Type v}

/-- Actual recursive results are bound into the subsequent measured merge. -/
def run (cmp : α → α → Bool) (xs : List α) : Measured (List α) Nat :=
  if h : xs.length ≤ 1 then Resources.pure xs
  else
    Resources.bind (run cmp (xs.take (xs.length / 2))) fun left =>
      Resources.bind (run cmp (xs.drop (xs.length / 2))) fun right =>
        Resources.reweight Prod.fst (ListMerge.run cmp left right)
termination_by xs.length
decreasing_by
  all_goals
    simp only [List.length_take, List.length_drop]
    omega

abbrev comparisons (cmp : α → α → Bool) (xs : List α) : Nat := (run cmp xs).2

theorem run_of_length_le (cmp : α → α → Bool) (xs : List α)
    (h : xs.length ≤ 1) : run cmp xs = (xs, 0) := by
  rw [run]
  split
  · rfl
  · omega

theorem run_step (cmp : α → α → Bool) (xs : List α) (h : 1 < xs.length) :
    run cmp xs =
      Resources.bind (run cmp (xs.take (xs.length / 2))) fun left =>
        Resources.bind (run cmp (xs.drop (xs.length / 2))) fun right =>
          Resources.reweight Prod.fst (ListMerge.run cmp left right) := by
  rw [run]
  split
  · omega
  · rfl

@[simp] theorem run_nil (cmp : α → α → Bool) : run cmp [] = ([], 0) :=
  run_of_length_le cmp [] (by simp)

@[simp] theorem run_singleton (cmp : α → α → Bool) (x : α) :
    run cmp [x] = ([x], 0) := run_of_length_le cmp [x] (by simp)

/-- Erasure identifies the book's floor-left value algorithm, for any comparator. -/
theorem run_value (cmp : α → α → Bool) (xs : List α) :
    (run cmp xs).1 = sortFloorBy cmp xs := by
  by_cases h : xs.length ≤ 1
  · rw [run_of_length_le cmp xs h, sortFloorBy_of_length_le cmp xs h]
  · rw [run_step cmp xs (by omega), sortFloorBy_step cmp xs (by omega)]
    simp only [Resources.bind_value, Resources.reweight_value, ListMerge.run_value]
    rw [run_value cmp (xs.take (xs.length / 2)), run_value cmp (xs.drop (xs.length / 2))]
termination_by xs.length
decreasing_by
  all_goals
    simp only [List.length_take, List.length_drop]
    omega

theorem run_perm (cmp : α → α → Bool) (xs : List α) : (run cmp xs).1.Perm xs := by
  rw [run_value]
  exact sortFloorBy_perm cmp xs

theorem run_length (cmp : α → α → Bool) (xs : List α) :
    (run cmp xs).1.length = xs.length := (run_perm cmp xs).length_eq

theorem run_stable_spec [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]
    [DecidableEq κ] (key : α → κ) (xs : List α) :
    StableSort key xs (run (fun x y => decide (key x ≤ key y)) xs).1 := by
  rw [run_value]
  exact sortFloorOn_spec key xs

theorem comparisons_of_length_le (cmp : α → α → Bool) (xs : List α)
    (h : xs.length ≤ 1) : comparisons cmp xs = 0 := by
  simp only [comparisons, run_of_length_le cmp xs h]

/-- Exact source counter recurrence, obtained from the executed binds and erasure. -/
theorem comparisons_step (cmp : α → α → Bool) (xs : List α) (h : 1 < xs.length) :
    comparisons cmp xs =
      comparisons cmp (xs.take (xs.length / 2)) +
      comparisons cmp (xs.drop (xs.length / 2)) +
      ListMerge.comparisons cmp (sortFloorBy cmp (xs.take (xs.length / 2)))
        (sortFloorBy cmp (xs.drop (xs.length / 2))) := by
  simp [comparisons, run_step cmp xs h, Resources.bind, Resources.reweight,
    ListMerge.comparisons, run_value, Nat.add_assoc]

theorem comparisons_step_le (cmp : α → α → Bool) (xs : List α) (h : 1 < xs.length) :
    comparisons cmp xs ≤ comparisons cmp (xs.take (xs.length / 2)) +
      comparisons cmp (xs.drop (xs.length / 2)) + xs.length := by
  rw [comparisons_step cmp xs h]
  have hm := ListMerge.comparisons_le cmp
    (sortFloorBy cmp (xs.take (xs.length / 2)))
    (sortFloorBy cmp (xs.drop (xs.length / 2)))
  simp only [sortFloorBy_length, List.length_take, List.length_drop] at hm
  omega

/-- The comparison guarantee holds for every length, without order laws. -/
theorem comparisons_le_clog (cmp : α → α → Bool) (xs : List α) :
    comparisons cmp xs ≤ xs.length * Nat.clog 2 xs.length := by
  by_cases h : xs.length ≤ 1
  · rw [comparisons_of_length_le cmp xs h]
    exact Nat.zero_le _
  · have hn : 2 ≤ xs.length := by omega
    have hl := comparisons_le_clog cmp (xs.take (xs.length / 2))
    have hr := comparisons_le_clog cmp (xs.drop (xs.length / 2))
    have hcl : Nat.clog 2 (xs.take (xs.length / 2)).length ≤
        Nat.clog 2 ((xs.length + 1) / 2) := by
      apply Nat.clog_mono_right 2
      simp only [List.length_take]
      omega
    have hcr : Nat.clog 2 (xs.drop (xs.length / 2)).length ≤
        Nat.clog 2 ((xs.length + 1) / 2) := by
      apply Nat.clog_mono_right 2
      simp only [List.length_drop]
      omega
    have hrec := Nat.clog_of_two_le (b := 2) (n := xs.length) (by decide) hn
    have heq : (xs.length + 2 - 1) / 2 = (xs.length + 1) / 2 := by omega
    rw [heq] at hrec
    have hlen : (xs.take (xs.length / 2)).length +
        (xs.drop (xs.length / 2)).length = xs.length := by
      simp only [List.length_take, List.length_drop]
      omega
    calc
      comparisons cmp xs ≤ comparisons cmp (xs.take (xs.length / 2)) +
          comparisons cmp (xs.drop (xs.length / 2)) + xs.length :=
        comparisons_step_le cmp xs (by omega)
      _ ≤ (xs.take (xs.length / 2)).length * Nat.clog 2 (xs.take (xs.length / 2)).length +
          (xs.drop (xs.length / 2)).length * Nat.clog 2 (xs.drop (xs.length / 2)).length +
          xs.length := Nat.add_le_add_right (Nat.add_le_add hl hr) _
      _ ≤ (xs.take (xs.length / 2)).length * Nat.clog 2 ((xs.length + 1) / 2) +
          (xs.drop (xs.length / 2)).length * Nat.clog 2 ((xs.length + 1) / 2) +
          xs.length := Nat.add_le_add_right
        (Nat.add_le_add (Nat.mul_le_mul_left _ hcl) (Nat.mul_le_mul_left _ hcr)) _
      _ = xs.length * Nat.clog 2 xs.length := by
        rw [← Nat.add_mul, hlen, hrec, Nat.mul_add, Nat.mul_one]
termination_by xs.length
decreasing_by
  all_goals
    simp only [List.length_take, List.length_drop]
    omega

/-- The printed power-of-two comparison estimate, including the singleton case. -/
theorem comparisons_le_of_length_pow (cmp : α → α → Bool) (xs : List α) (k : Nat)
    (hlen : xs.length = 2 ^ k) : comparisons cmp xs ≤ k * 2 ^ k := by
  simpa [hlen, Nat.mul_comm] using comparisons_le_clog cmp xs

/-- The unrounded `n log₂ n` statement retains the printed power-of-two premise. -/
theorem comparisons_le_real_log_of_length_pow (cmp : α → α → Bool) (xs : List α)
    (k : Nat) (hlen : xs.length = 2 ^ k) :
    (comparisons cmp xs : ℝ) ≤ (xs.length : ℝ) * Real.logb 2 xs.length := by
  have hb : (comparisons cmp xs : ℝ) ≤ (k : ℝ) * (2 : ℝ) ^ k := by
    exact_mod_cast comparisons_le_of_length_pow cmp xs k hlen
  have hlog : Real.logb 2 ((2 : ℝ) ^ k) = k := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  simpa only [hlen, Nat.cast_pow, Nat.cast_ofNat, hlog, mul_comm] using hb

/-- An explicit all-length real upper bound, with its actual threshold. -/
theorem comparisons_le_real_log (cmp : α → α → Bool) (xs : List α)
    (hlen : 2 ≤ xs.length) :
    (comparisons cmp xs : ℝ) ≤ 2 * (xs.length : ℝ) * Real.logb 2 xs.length := by
  have hb : (comparisons cmp xs : ℝ) ≤
      (xs.length : ℝ) * (Nat.clog 2 xs.length : ℝ) := by
    exact_mod_cast comparisons_le_clog cmp xs
  calc
    (comparisons cmp xs : ℝ) ≤ (xs.length : ℝ) * (Nat.clog 2 xs.length : ℝ) := hb
    _ ≤ (xs.length : ℝ) * (2 * Real.logb 2 xs.length) :=
      mul_le_mul_of_nonneg_left (Resources.clog_two_cast_le_two_logb xs.length hlen)
        (Nat.cast_nonneg _)
    _ = 2 * (xs.length : ℝ) * Real.logb 2 xs.length := by ring

/-- Uniformity over all lists of a length gives a bound on every such input family. -/
theorem comparisons_isBigO (cmp : α → α → Bool) (inputs : Nat → List α)
    (hlen : ∀ n, (inputs n).length = n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (comparisons cmp (inputs n) : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply Resources.isBigO_of_clog_two_bound (C := 1) (N := 0)
  intro n _
  simpa only [hlen, one_mul] using comparisons_le_clog cmp (inputs n)

end Resources.TopDownSorting
