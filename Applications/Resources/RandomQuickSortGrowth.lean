import Applications.Resources.RandomQuickSortRank
import Applications.Resources.QuickSortMean
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-! Harmonic and logarithmic bounds for the actual fresh-occurrence execution.
The numerical solver receives the proved recurrence of the actual `sizeMean`.
Mapped-key distinctness transports its solution to arbitrary fixed inputs.
The append-inclusive mean uses the comparison of two observations of the same
run. Neither observation charges sampler implementation, indexing, removal,
random bits or physical runtime beyond its specified call-count tariff.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomQuickSort
universe u v w
variable {α : Type u} {κ : Type v}

noncomputable section

/-- The numerical premises are discharged by the actual execution recurrence. -/
theorem sizeMean_eq_closedForm (n : Nat) :
    sizeMean n = Resources.QuickSortMean.closedForm n :=
  Resources.QuickSortMean.eq_closedForm sizeMean sizeMean_zero sizeMean_recurrence n

/-- An exact identity for the actual canonical exercise mean, including zero. -/
theorem sizeMean_eq_harmonic (n : Nat) :
    sizeMean n =
      8 * ((n : ℝ) + 1) * (harmonic n : ℝ) - 12 * (n : ℝ) + 1 :=
  sizeMean_eq_closedForm n

theorem exerciseMean_eq_closedForm [LinearOrder κ] (key : α → κ) (xs : List α)
    (hd : (xs.map key).Nodup) :
    exerciseMean (fun a b => decide (key a < key b)) xs =
      Resources.QuickSortMean.closedForm xs.length :=
  (exerciseMean_eq_sizeMean key xs hd).trans (sizeMean_eq_closedForm xs.length)

/-- Input order and payload representation do not change this distinct-key mean. -/
theorem exerciseMean_eq_harmonic [LinearOrder κ] (key : α → κ) (xs : List α)
    (hd : (xs.map key).Nodup) :
    exerciseMean (fun a b => decide (key a < key b)) xs =
      8 * ((xs.length : ℝ) + 1) * (harmonic xs.length : ℝ) -
        12 * (xs.length : ℝ) + 1 :=
  exerciseMean_eq_closedForm key xs hd

/-- Bounds for the actual append-inclusive observation on the same run. -/
theorem literalMean_harmonic_comparison [LinearOrder κ] (key : α → κ) (xs : List α)
    (hd : (xs.map key).Nodup) :
    8 * ((xs.length : ℝ) + 1) * (harmonic xs.length : ℝ) -
        12 * (xs.length : ℝ) + 1 ≤
      literalMean (fun a b => decide (key a < key b)) xs ∧
    literalMean (fun a b => decide (key a < key b)) xs ≤
      2 * (8 * ((xs.length : ℝ) + 1) * (harmonic xs.length : ℝ) -
        12 * (xs.length : ℝ) + 1) := by
  have h := literalMean_comparison (fun a b => decide (key a < key b)) xs
  rw [exerciseMean_eq_harmonic key xs hd] at h
  exact h

theorem exerciseMean_le_log [LinearOrder κ] (key : α → κ) (xs : List α)
    (hd : (xs.map key).Nodup) (hn : 1 ≤ xs.length) :
    exerciseMean (fun a b => decide (key a < key b)) xs ≤
      16 * (xs.length : ℝ) * (1 + Real.log (xs.length : ℝ)) := by
  rw [exerciseMean_eq_closedForm key xs hd]
  exact Resources.QuickSortMean.closedForm_le_log xs.length hn

theorem literalMean_le_log [LinearOrder κ] (key : α → κ) (xs : List α)
    (hd : (xs.map key).Nodup) (hn : 1 ≤ xs.length) :
    literalMean (fun a b => decide (key a < key b)) xs ≤
      32 * (xs.length : ℝ) * (1 + Real.log (xs.length : ℝ)) := by
  calc
    _ ≤ 2 * exerciseMean (fun a b => decide (key a < key b)) xs :=
      (literalMean_comparison _ xs).2
    _ ≤ 2 * (16 * (xs.length : ℝ) * (1 + Real.log (xs.length : ℝ))) :=
      mul_le_mul_of_nonneg_left (exerciseMean_le_log key xs hd hn) (by norm_num)
    _ = _ := by ring

theorem exerciseMean_le_nlog [LinearOrder κ] (key : α → κ) (xs : List α)
    (hd : (xs.map key).Nodup) (hn : 2 ≤ xs.length) :
    exerciseMean (fun a b => decide (key a < key b)) xs ≤
      (16 * (1 + 1 / Real.log 2)) *
        ((xs.length : ℝ) * Real.log (xs.length : ℝ)) := by
  rw [exerciseMean_eq_closedForm key xs hd]
  exact Resources.QuickSortMean.closedForm_le_nlog xs.length hn

theorem literalMean_le_nlog [LinearOrder κ] (key : α → κ) (xs : List α)
    (hd : (xs.map key).Nodup) (hn : 2 ≤ xs.length) :
    literalMean (fun a b => decide (key a < key b)) xs ≤
      (32 * (1 + 1 / Real.log 2)) *
        ((xs.length : ℝ) * Real.log (xs.length : ℝ)) := by
  calc
    _ ≤ 2 * exerciseMean (fun a b => decide (key a < key b)) xs :=
      (literalMean_comparison _ xs).2
    _ ≤ 2 * ((16 * (1 + 1 / Real.log 2)) *
        ((xs.length : ℝ) * Real.log (xs.length : ℝ))) :=
      mul_le_mul_of_nonneg_left (exerciseMean_le_nlog key xs hd hn) (by norm_num)
    _ = _ := by ring

/-- The real binary-log bound begins at two, after both positive base tariffs. -/
theorem exerciseMean_le_nlogb [LinearOrder κ] (key : α → κ) (xs : List α)
    (hd : (xs.map key).Nodup) (hn : 2 ≤ xs.length) :
    exerciseMean (fun a b => decide (key a < key b)) xs ≤
      32 * ((xs.length : ℝ) * Real.logb 2 (xs.length : ℝ)) := by
  rw [exerciseMean_eq_closedForm key xs hd]
  exact Resources.QuickSortMean.closedForm_le_nlogb xs.length hn

theorem literalMean_le_nlogb [LinearOrder κ] (key : α → κ) (xs : List α)
    (hd : (xs.map key).Nodup) (hn : 2 ≤ xs.length) :
    literalMean (fun a b => decide (key a < key b)) xs ≤
      64 * ((xs.length : ℝ) * Real.logb 2 (xs.length : ℝ)) := by
  calc
    _ ≤ 2 * exerciseMean (fun a b => decide (key a < key b)) xs :=
      (literalMean_comparison _ xs).2
    _ ≤ 2 * (32 * ((xs.length : ℝ) * Real.logb 2 (xs.length : ℝ))) :=
      mul_le_mul_of_nonneg_left (exerciseMean_le_nlogb key xs hd hn) (by norm_num)
    _ = _ := by ring

theorem sizeMean_isBigO_log :
    Asymptotics.IsBigO Filter.atTop sizeMean
      (fun n : Nat => (n : ℝ) * Real.log (n : ℝ)) := by
  have h : sizeMean = Resources.QuickSortMean.closedForm := funext sizeMean_eq_closedForm
  rw [h]
  exact Resources.QuickSortMean.closedForm_isBigO_log

theorem sizeMean_isBigO_logb :
    Asymptotics.IsBigO Filter.atTop sizeMean
      (fun n : Nat => (n : ℝ) * Real.logb 2 (n : ℝ)) := by
  have h : sizeMean = Resources.QuickSortMean.closedForm := funext sizeMean_eq_closedForm
  rw [h]
  exact Resources.QuickSortMean.closedForm_isBigO_logb

/-- The growth variable is actual input length; key distinctness is only eventual. -/
theorem exerciseMean_family_isBigO_log {ι : Type w} [LinearOrder κ] (key : α → κ)
    (l : Filter ι) (xs : ι → List α)
    (hd : ∀ᶠ i in l, ((xs i).map key).Nodup)
    (hlen : Filter.Tendsto (fun i => (xs i).length) l Filter.atTop) :
    Asymptotics.IsBigO l
      (fun i => exerciseMean (fun a b => decide (key a < key b)) (xs i))
      (fun i => ((xs i).length : ℝ) * Real.log ((xs i).length : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨16 * (1 + 1 / Real.log 2), ?_⟩
  filter_upwards [hd, Filter.tendsto_atTop.mp hlen 2] with i hdi hi
  have hlog : 0 ≤ Real.log ((xs i).length : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ (xs i).length by omega))
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (exerciseMean_nonneg _ _),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog)]
  exact exerciseMean_le_nlog key (xs i) hdi hi

theorem literalMean_family_isBigO_log {ι : Type w} [LinearOrder κ] (key : α → κ)
    (l : Filter ι) (xs : ι → List α)
    (hd : ∀ᶠ i in l, ((xs i).map key).Nodup)
    (hlen : Filter.Tendsto (fun i => (xs i).length) l Filter.atTop) :
    Asymptotics.IsBigO l
      (fun i => literalMean (fun a b => decide (key a < key b)) (xs i))
      (fun i => ((xs i).length : ℝ) * Real.log ((xs i).length : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨32 * (1 + 1 / Real.log 2), ?_⟩
  filter_upwards [hd, Filter.tendsto_atTop.mp hlen 2] with i hdi hi
  have hlog : 0 ≤ Real.log ((xs i).length : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ (xs i).length by omega))
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (literalMean_nonneg _ _),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog)]
  exact literalMean_le_nlog key (xs i) hdi hi

theorem exerciseMean_family_isBigO_logb {ι : Type w} [LinearOrder κ] (key : α → κ)
    (l : Filter ι) (xs : ι → List α)
    (hd : ∀ᶠ i in l, ((xs i).map key).Nodup)
    (hlen : Filter.Tendsto (fun i => (xs i).length) l Filter.atTop) :
    Asymptotics.IsBigO l
      (fun i => exerciseMean (fun a b => decide (key a < key b)) (xs i))
      (fun i => ((xs i).length : ℝ) * Real.logb 2 ((xs i).length : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨32, ?_⟩
  filter_upwards [hd, Filter.tendsto_atTop.mp hlen 2] with i hdi hi
  have hlog : 0 ≤ Real.logb 2 ((xs i).length : ℝ) :=
    Real.logb_nonneg (by norm_num)
      (by exact_mod_cast (show 1 ≤ (xs i).length by omega))
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (exerciseMean_nonneg _ _),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog)]
  exact exerciseMean_le_nlogb key (xs i) hdi hi

theorem literalMean_family_isBigO_logb {ι : Type w} [LinearOrder κ] (key : α → κ)
    (l : Filter ι) (xs : ι → List α)
    (hd : ∀ᶠ i in l, ((xs i).map key).Nodup)
    (hlen : Filter.Tendsto (fun i => (xs i).length) l Filter.atTop) :
    Asymptotics.IsBigO l
      (fun i => literalMean (fun a b => decide (key a < key b)) (xs i))
      (fun i => ((xs i).length : ℝ) * Real.logb 2 ((xs i).length : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨64, ?_⟩
  filter_upwards [hd, Filter.tendsto_atTop.mp hlen 2] with i hdi hi
  have hlog : 0 ≤ Real.logb 2 ((xs i).length : ℝ) :=
    Real.logb_nonneg (by norm_num)
      (by exact_mod_cast (show 1 ≤ (xs i).length by omega))
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (literalMean_nonneg _ _),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog)]
  exact literalMean_le_nlogb key (xs i) hdi hi

end
end Resources.RandomQuickSort
