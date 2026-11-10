import Applications.Resources.Growth
import Applications.Resources.ListExecution
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Signed growth and observations of existing executions

Native signed upper/lower comparisons retain their positive rational witnesses.
Norm equivalences use eventual signs; zero-aware factorization keeps eventual
equality and an unrestricted signed source witness. The measured clients use
the actual reverse and fixed-price fold executions, preserving returned values.
The observation model does not charge input construction or reweighting itself.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ResourceGrowth
open Filter Asymptotics Resources Resources.ListExecution
universe u v
variable {α : Type u} {β : Type v}

/-- Reweighting preserves the returned list of the actual reverse. -/
theorem half_reverse_value (a : α) (n : ℕ) :
    (reweight (fun k : ℕ => (k : ℚ) / 2) (reverse (List.replicate n a))).1 =
      List.replicate n a := by
  rw [reweight_value, reverse_value, List.reverse_replicate]

/-- The terminal charge contributes the nonintegral constant one half. -/
theorem half_reverse_work (a : α) (n : ℕ) :
    (reweight (fun k : ℕ => (k : ℚ) / 2) (reverse (List.replicate n a))).2 =
      (n : ℚ) + 1 / 2 := by
  change ((reverse (List.replicate n a)).2 : ℚ) / 2 = _
  rw [reverse_work, List.length_replicate]
  push_cast
  ring

/-- Explicit positive rational comparison constants, valid from length one. -/
theorem half_reverse_bounds (a : α) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℚ) ≤
        (reweight (fun k : ℕ => (k : ℚ) / 2) (reverse (List.replicate n a))).2 ∧
      (reweight (fun k : ℕ => (k : ℚ) / 2) (reverse (List.replicate n a))).2 ≤
        (3 / 2 : ℚ) * (n : ℚ) := by
  rw [half_reverse_work]
  have hnq : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  constructor <;> linarith

theorem half_reverse_theta (a : α) :
    (fun n : ℕ =>
      (reweight (fun k : ℕ => (k : ℚ) / 2) (reverse (List.replicate n a))).2)
      =Θ[atTop] (fun n : ℕ => (n : ℚ)) := by
  have hwork : ∀ᶠ n : ℕ in atTop, 0 ≤
      (reweight (fun k : ℕ => (k : ℚ) / 2) (reverse (List.replicate n a))).2 :=
    Eventually.of_forall fun n => by rw [half_reverse_work]; positivity
  have hnat : ∀ᶠ n : ℕ in atTop, 0 ≤ (n : ℚ) :=
    Eventually.of_forall fun n => Nat.cast_nonneg n
  constructor
  · apply (isBigO_rat_iff_eventually_le_mul _ _ hwork hnat).mpr
    refine ⟨3 / 2, by norm_num, eventually_atTop.mpr ⟨1, ?_⟩⟩
    intro n hn
    exact (half_reverse_bounds a n hn).2
  · apply (isBigO_rat_iff_eventually_le_mul _ _ hnat hwork).mpr
    refine ⟨1, by norm_num, eventually_atTop.mpr ⟨1, ?_⟩⟩
    intro n hn
    simpa only [one_mul] using (half_reverse_bounds a n hn).1

-- Independently, the structural counts are one at length zero and seven at
-- length three. Reweighting those counts gives one half and seven halves.
theorem half_reverse_nil (a : α) :
    (reweight (fun k : ℕ => (k : ℚ) / 2) (reverse (List.replicate 0 a))).2 =
      1 / 2 := by
  rw [half_reverse_work]
  norm_num

theorem half_reverse_three (a : α) :
    (reweight (fun k : ℕ => (k : ℚ) / 2) (reverse (List.replicate 3 a))).2 =
      7 / 2 := by
  rw [half_reverse_work]
  norm_num

theorem half_reverse_no_global_linear_bound (a : α) :
    ¬ ∃ C : ℚ, ∀ n : ℕ,
      (reweight (fun k : ℕ => (k : ℚ) / 2) (reverse (List.replicate n a))).2 ≤
        C * (n : ℚ) := by
  rintro ⟨C, h⟩
  have hzero := h 0
  rw [half_reverse_nil] at hzero
  norm_num at hzero

/-- A signed left function may be bounded above while its norm is unbounded. -/
theorem signed_negative_upper :
    ∃ C : ℚ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, -(n : ℚ) ≤ C * 1 := by
  refine ⟨1, by norm_num, Eventually.of_forall ?_⟩
  intro n
  have hn : 0 ≤ (n : ℚ) := Nat.cast_nonneg n
  linarith

theorem signed_negative_not_isBigO :
    ¬ ((fun n : ℕ => -(n : ℚ)) =O[atTop] (fun _ : ℕ => (1 : ℚ))) := by
  intro h
  obtain ⟨C, _, hbound⟩ := isBigO_iff'.mp h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  obtain ⟨m, hm⟩ := exists_nat_gt C
  have hx := hN (max N m) (le_max_left _ _)
  have hcast : (m : ℝ) ≤ ((max N m : ℕ) : ℝ) := by
    exact_mod_cast (le_max_right N m)
  have hnorm : ‖-((max N m : ℕ) : ℚ)‖ = ((max N m : ℕ) : ℝ) := by
    rw [norm_neg, ← Rat.norm_cast_real]
    simp only [Rat.cast_natCast, Real.norm_natCast]
  rw [hnorm] at hx
  norm_num at hx
  linarith

theorem signed_negative_comparator_theta :
    (fun _ : ℕ => (1 : ℚ)) =Θ[atTop] (fun _ : ℕ => (-1 : ℚ)) :=
  isTheta_const_const (by norm_num) (by norm_num)

theorem signed_negative_comparator_not_upper :
    ¬ ∃ C : ℚ, 0 < C ∧ ∀ᶠ _n : ℕ in atTop, (1 : ℚ) ≤ C * (-1) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  have hx := hN N le_rfl
  linarith

/-- Increasing this coefficient would reverse the useful comparison. -/
theorem signed_half_coefficient :
    0 < (1 / 2 : ℚ) ∧
      ∀ᶠ _n : ℕ in atTop, (-1 : ℚ) ≤ (1 / 2 : ℚ) * (-2) := by
  refine ⟨by norm_num, Eventually.of_forall ?_⟩
  intro n
  norm_num

theorem signed_no_positive_nat_coefficient :
    ¬ ∃ C : ℕ, 0 < C ∧
      ∀ᶠ _n : ℕ in atTop, (-1 : ℚ) ≤ (C : ℚ) * (-2) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  have hx := hN N le_rfl
  have hCq : (1 : ℚ) ≤ (C : ℚ) := by exact_mod_cast (show 1 ≤ C from hC)
  linarith

/-! ## Natural coefficients, exact thresholds, and squares -/

/-- This retains the source's positive coefficient and inclusive threshold. -/
theorem nat_upper_iff_isBigO (f g : ℕ → ℕ) :
    (∃ C N : ℕ, 0 < C ∧ ∀ n, N ≤ n → f n ≤ C * g n) ↔
      (fun n => (f n : ℝ)) =O[atTop] (fun n => (g n : ℝ)) := by
  rw [isBigO_natCast_iff]
  constructor
  · rintro ⟨C, N, hC, hbound⟩
    exact ⟨C, hC, eventually_atTop.mpr ⟨N, hbound⟩⟩
  · rintro ⟨C, hC, hbound⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
    exact ⟨C, N, hC, hN⟩

theorem nat_upper_refl (f : ℕ → ℕ) :
    ∃ C N : ℕ, 0 < C ∧ ∀ n, N ≤ n → f n ≤ C * f n :=
  ⟨1, 0, by decide, fun _ _ => by simp⟩

theorem nat_upper_trans {f g h : ℕ → ℕ}
    (hfg : ∃ C N : ℕ, 0 < C ∧ ∀ n, N ≤ n → f n ≤ C * g n)
    (hgh : ∃ D M : ℕ, 0 < D ∧ ∀ n, M ≤ n → g n ≤ D * h n) :
    ∃ C N : ℕ, 0 < C ∧ ∀ n, N ≤ n → f n ≤ C * h n := by
  obtain ⟨C, N, hC, hfg⟩ := hfg
  obtain ⟨D, M, hD, hgh⟩ := hgh
  refine ⟨C * D, max N M, Nat.mul_pos hC hD, ?_⟩
  intro n hn
  exact (hfg n (by omega)).trans (by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left C (hgh n (by omega)))

/-- Cast the supplied coefficient and retain its threshold. -/
theorem nat_upper_to_rat_upper {f g : ℕ → ℕ}
    (hfg : ∃ C N : ℕ, 0 < C ∧ ∀ n, N ≤ n → f n ≤ C * g n) :
    ∃ C : ℚ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (f n : ℚ) ≤ C * (g n : ℚ) := by
  obtain ⟨C, N, hC, hbound⟩ := hfg
  refine ⟨(C : ℚ), Nat.cast_pos.mpr hC, eventually_atTop.mpr ⟨N, ?_⟩⟩
  intro n hn
  simpa only [Nat.cast_mul] using (Nat.cast_le (α := ℚ)).mpr (hbound n hn)

/-- The lower rational coefficient is the reciprocal of the actual reverse
natural coefficient; a natural lower coefficient is not required. -/
theorem nat_twoSided_to_rat_twoSided {f g : ℕ → ℕ}
    (hfg : ∃ C N : ℕ, 0 < C ∧ ∀ n, N ≤ n → f n ≤ C * g n)
    (hgf : ∃ D M : ℕ, 0 < D ∧ ∀ n, M ≤ n → g n ≤ D * f n) :
    ∃ c C : ℚ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in atTop, c * (g n : ℚ) ≤ (f n : ℚ) ∧
        (f n : ℚ) ≤ C * (g n : ℚ) := by
  obtain ⟨C, N, hC, hupper⟩ := hfg
  obtain ⟨D, M, hD, hreverse⟩ := hgf
  have hDq : 0 < (D : ℚ) := Nat.cast_pos.mpr hD
  refine ⟨1 / (D : ℚ), (C : ℚ), one_div_pos.mpr hDq, Nat.cast_pos.mpr hC,
    eventually_atTop.mpr ⟨max N M, ?_⟩⟩
  intro n hn
  have hlower : (g n : ℚ) ≤ (D : ℚ) * (f n : ℚ) := by
    simpa only [Nat.cast_mul] using
      (Nat.cast_le (α := ℚ)).mpr (hreverse n (by omega))
  constructor
  · calc
      (1 / (D : ℚ)) * (g n : ℚ) = (g n : ℚ) / (D : ℚ) := by ring
      _ ≤ (f n : ℚ) := (div_le_iff₀ hDq).mpr (by simpa only [mul_comm] using hlower)
  · simpa only [Nat.cast_mul] using
      (Nat.cast_le (α := ℚ)).mpr (hupper n (by omega))

theorem successor_square_theta :
    (fun n : ℕ => (((n + 1) * (n + 1) : ℕ) : ℝ)) =Θ[atTop]
      (fun n : ℕ => ((n * n : ℕ) : ℝ)) := by
  constructor
  · apply (isBigO_natCast_iff _ _).mpr
    refine ⟨4, by decide, eventually_atTop.mpr ⟨1, ?_⟩⟩
    intro n hn
    simpa only [Nat.mul_assoc] using (successor_square_bounds n hn).2
  · apply (isBigO_natCast_iff _ _).mpr
    refine ⟨1, by decide, eventually_atTop.mpr ⟨1, ?_⟩⟩
    intro n hn
    simpa only [one_mul] using (successor_square_bounds n hn).1

theorem successor_square_rat_theta :
    (fun n : ℕ => ((n : ℚ) + 1) * ((n : ℚ) + 1)) =Θ[atTop]
      (fun n : ℕ => (n : ℚ) * (n : ℚ)) := by
  have hshift : ∀ᶠ n : ℕ in atTop, 0 ≤ ((n : ℚ) + 1) * ((n : ℚ) + 1) :=
    Eventually.of_forall fun n => by positivity
  have hsquare : ∀ᶠ n : ℕ in atTop, 0 ≤ (n : ℚ) * (n : ℚ) :=
    Eventually.of_forall fun n => by positivity
  constructor
  · apply (isBigO_rat_iff_eventually_le_mul _ _ hshift hsquare).mpr
    refine ⟨4, by norm_num, eventually_atTop.mpr ⟨1, ?_⟩⟩
    intro n hn
    have h : ((n : ℚ) + 1) * ((n : ℚ) + 1) ≤ 4 * (n : ℚ) * (n : ℚ) := by
      exact_mod_cast (successor_square_bounds n hn).2
    simpa only [mul_assoc] using h
  · apply (isBigO_rat_iff_eventually_le_mul _ _ hsquare hshift).mpr
    refine ⟨1, by norm_num, eventually_atTop.mpr ⟨1, ?_⟩⟩
    intro n hn
    simp only [one_mul]
    exact_mod_cast (successor_square_bounds n hn).1

theorem successor_square_zero_upper_false :
    ¬ (0 + 1) * (0 + 1) ≤ 4 * (0 : ℕ) * 0 := by decide

theorem successor_square_one_sharp :
    (1 + 1) * (1 + 1) = 4 * (1 : ℕ) * 1 := by decide

theorem successor_square_ne (n : ℕ) : (n + 1) * (n + 1) ≠ n * n := by
  intro h
  nlinarith

theorem successor_square_not_eventuallyEq :
    ¬ ((fun n : ℕ => (n + 1) * (n + 1)) =ᶠ[atTop] (fun n => n * n)) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  exact successor_square_ne N (hN N le_rfl)

/-- The modified functions have negative values at zero, but eventual signs. -/
theorem negative_prefix_eventually_nonnegative :
    (∀ᶠ n : ℕ in atTop,
      0 ≤ if n = 0 then (-7 : ℚ) else ((n : ℚ) + 1) * ((n : ℚ) + 1)) ∧
    (∀ᶠ n : ℕ in atTop,
      0 ≤ if n = 0 then (-3 : ℚ) else (n : ℚ) * (n : ℚ)) := by
  constructor <;> refine eventually_atTop.mpr ⟨1, ?_⟩ <;> intro n hn
  · rw [ite_eq_right (show n ≠ 0 by omega)]
    positivity
  · rw [ite_eq_right (show n ≠ 0 by omega)]
    positivity

theorem negative_prefix_theta :
    (fun n : ℕ => if n = 0 then (-7 : ℚ) else ((n : ℚ) + 1) * ((n : ℚ) + 1))
      =Θ[atTop]
      (fun n : ℕ => if n = 0 then (-3 : ℚ) else (n : ℚ) * (n : ℚ)) := by
  have hf : (fun n : ℕ => ((n : ℚ) + 1) * ((n : ℚ) + 1)) =ᶠ[atTop]
      (fun n : ℕ => if n = 0 then (-7 : ℚ) else ((n : ℚ) + 1) * ((n : ℚ) + 1)) :=
    eventually_atTop.mpr ⟨1, fun n hn => by simp [show n ≠ 0 by omega]⟩
  have hg : (fun n : ℕ => (n : ℚ) * (n : ℚ)) =ᶠ[atTop]
      (fun n : ℕ => if n = 0 then (-3 : ℚ) else (n : ℚ) * (n : ℚ)) :=
    eventually_atTop.mpr ⟨1, fun n hn => by simp [show n ≠ 0 by omega]⟩
  exact ⟨successor_square_rat_theta.1.congr' hf hg,
    successor_square_rat_theta.2.congr' hg hf⟩

/-- The bridge consumes eventual signs even though neither global sign holds. -/
theorem negative_prefix_upper_witness :
    ∃ C : ℚ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (if n = 0 then (-7 : ℚ) else ((n : ℚ) + 1) * ((n : ℚ) + 1)) ≤
        C * (if n = 0 then (-3 : ℚ) else (n : ℚ) * (n : ℚ)) :=
  (isBigO_rat_iff_eventually_le_mul _ _
    negative_prefix_eventually_nonnegative.1
    negative_prefix_eventually_nonnegative.2).mp negative_prefix_theta.1

theorem zero_upper_one :
    ∃ C : ℚ, 0 < C ∧ ∀ᶠ _n : ℕ in atTop, (0 : ℚ) ≤ C * 1 :=
  ⟨1, by norm_num, Eventually.of_forall fun _ => by norm_num⟩

theorem zero_isBigO_one :
    (fun _ : ℕ => (0 : ℚ)) =O[atTop] (fun _ : ℕ => (1 : ℚ)) := by
  apply (isBigO_rat_iff_eventually_le_mul _ _
    (Eventually.of_forall fun _ => le_rfl)
    (Eventually.of_forall fun _ => by norm_num)).mpr
  exact zero_upper_one

theorem zero_not_twoSided_one :
    ¬ ∃ c C : ℚ, 0 < c ∧ 0 < C ∧
      ∀ᶠ _n : ℕ in atTop, c * 1 ≤ 0 ∧ (0 : ℚ) ≤ C * 1 := by
  rintro ⟨c, C, hc, _, hbound⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  have hlower := (hN N le_rfl).1
  linarith

theorem zero_not_isTheta_one :
    ¬ ((fun _ : ℕ => (0 : ℚ)) =Θ[atTop] (fun _ : ℕ => (1 : ℚ))) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (isTheta_zero_left.mp h)
  have hzero := hN N le_rfl
  norm_num at hzero

/-- Existing callers may still supply the zero coefficient to the old adapter. -/
theorem old_nat_adapter_zero (g : ℕ → ℕ) :
    (fun _ : ℕ => (0 : ℝ)) =O[atTop] (fun n => (g n : ℝ)) := by
  simpa only [Nat.cast_zero] using
    isBigO_of_nat_bound (fun _ => 0) g 0 0 (fun _ _ => by simp)

-- The three supplied source cases now use the native order/norm contracts.
example : ∃ C : ℚ, 0 < C ∧ ∀ᶠ _n : ℕ in atTop, (0 : ℚ) ≤ C * 1 := zero_upper_one
example : ¬ ∃ c C : ℚ, 0 < c ∧ 0 < C ∧
    ∀ᶠ _n : ℕ in atTop, c * 1 ≤ 0 ∧ (0 : ℚ) ≤ C * 1 := zero_not_twoSided_one
example :
    (∃ C N : ℕ, 0 < C ∧ ∀ n, N ≤ n → (n + 1) * (n + 1) ≤ C * (n * n)) ∧
    (∃ C N : ℕ, 0 < C ∧ ∀ n, N ≤ n → n * n ≤ C * ((n + 1) * (n + 1))) :=
  ⟨(nat_upper_iff_isBigO (fun n => (n + 1) * (n + 1)) (fun n => n * n)).mpr
      successor_square_theta.1,
    (nat_upper_iff_isBigO (fun n => n * n) (fun n => (n + 1) * (n + 1))).mpr
      successor_square_theta.2⟩

/-! ## Fixed-price actual recursive and direct folds -/

theorem recursive_fold_value (c : ℕ) (f : β → α → β) (e : β) (a : α) (n : ℕ) :
    (foldlViaInit c f e (List.replicate n a)).1 = (List.replicate n a).foldl f e :=
  foldlViaInit_value c f e _

theorem recursive_fold_work (c : ℕ) (f : β → α → β) (e : β) (a : α) (n : ℕ) :
    (foldlViaInit c f e (List.replicate n a)).2 =
      3 * (List.range (n + 1)).sum + c * n + 1 := by
  simpa only [List.length_replicate] using foldlViaInit_work c f e (List.replicate n a)

theorem recursive_fold_bounds (c : ℕ) (f : β → α → β) (e : β) (a : α)
    (n : ℕ) (hn : 1 ≤ n) :
    n * n ≤ (foldlViaInit c f e (List.replicate n a)).2 ∧
      (foldlViaInit c f e (List.replicate n a)).2 ≤ (4 * (3 + c)) * (n * n) := by
  constructor
  · simpa only [List.length_replicate] using
      foldlViaInit_quadratic_lower c f e (List.replicate n a)
  · calc
      (foldlViaInit c f e (List.replicate n a)).2 ≤ (3 + c) * ((n + 1) * (n + 1)) := by
        simpa only [List.length_replicate, Nat.mul_assoc] using
          foldlViaInit_quadratic_upper c f e (List.replicate n a)
      _ ≤ (3 + c) * (4 * n * n) :=
        Nat.mul_le_mul_left (3 + c) (successor_square_bounds n hn).2
      _ = (4 * (3 + c)) * (n * n) := by ring

theorem recursive_fold_theta (c : ℕ) (f : β → α → β) (e : β) (a : α) :
    (fun n : ℕ => ((foldlViaInit c f e (List.replicate n a)).2 : ℝ)) =Θ[atTop]
      (fun n : ℕ => ((n * n : ℕ) : ℝ)) := by
  constructor
  · apply (isBigO_natCast_iff _ _).mpr
    refine ⟨4 * (3 + c), by positivity, eventually_atTop.mpr ⟨1, ?_⟩⟩
    intro n hn
    exact (recursive_fold_bounds c f e a n hn).2
  · apply (isBigO_natCast_iff _ _).mpr
    refine ⟨1, by decide, eventually_atTop.mpr ⟨1, ?_⟩⟩
    intro n hn
    simpa only [one_mul] using (recursive_fold_bounds c f e a n hn).1

theorem direct_fold_value (c : ℕ) (f : β → α → β) (e : β) (a : α) (n : ℕ) :
    (foldl c f e (List.replicate n a)).1 = (List.replicate n a).foldl f e :=
  foldl_value c f e _

theorem direct_fold_work (c : ℕ) (f : β → α → β) (e : β) (a : α) (n : ℕ) :
    (foldl c f e (List.replicate n a)).2 = (1 + c) * n + 1 := by
  simpa only [List.length_replicate] using foldl_work c f e (List.replicate n a)

theorem fold_values_agree (c : ℕ) (f : β → α → β) (e : β) (a : α) (n : ℕ) :
    (foldlViaInit c f e (List.replicate n a)).1 =
      (foldl c f e (List.replicate n a)).1 := by
  rw [recursive_fold_value, direct_fold_value]

theorem direct_fold_bounds (c : ℕ) (f : β → α → β) (e : β) (a : α)
    (n : ℕ) (hn : 1 ≤ n) :
    n ≤ (foldl c f e (List.replicate n a)).2 ∧
      (foldl c f e (List.replicate n a)).2 ≤ (2 + c) * n := by
  rw [direct_fold_work]
  constructor <;> nlinarith

theorem direct_fold_theta (c : ℕ) (f : β → α → β) (e : β) (a : α) :
    (fun n : ℕ => ((foldl c f e (List.replicate n a)).2 : ℝ)) =Θ[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  constructor
  · apply (isBigO_natCast_iff _ _).mpr
    refine ⟨2 + c, by positivity, eventually_atTop.mpr ⟨1, ?_⟩⟩
    intro n hn
    exact (direct_fold_bounds c f e a n hn).2
  · apply (isBigO_natCast_iff _ _).mpr
    refine ⟨1, by decide, eventually_atTop.mpr ⟨1, ?_⟩⟩
    intro n hn
    simpa only [one_mul] using (direct_fold_bounds c f e a n hn).1

theorem fold_nil_costs (c : ℕ) (f : β → α → β) (e : β) (a : α) :
    (foldlViaInit c f e (List.replicate 0 a)).2 = 1 ∧
      (foldl c f e (List.replicate 0 a)).2 = 1 := by
  rw [recursive_fold_work, direct_fold_work]
  norm_num [List.range_succ]

theorem fold_singleton_costs (c : ℕ) (f : β → α → β) (e : β) (a : α) :
    (foldlViaInit c f e (List.replicate 1 a)).2 = c + 4 ∧
      (foldl c f e (List.replicate 1 a)).2 = c + 2 := by
  rw [recursive_fold_work, direct_fold_work]
  norm_num [List.range_succ]
  constructor <;> omega

theorem fold_three_costs (c : ℕ) (f : β → α → β) (e : β) (a : α) :
    (foldlViaInit c f e (List.replicate 3 a)).2 = 3 * c + 19 ∧
      (foldl c f e (List.replicate 3 a)).2 = 3 * c + 4 := by
  rw [recursive_fold_work, direct_fold_work]
  norm_num [List.range_succ]
  constructor <;> ring

/-! ## Full signed rational algebra in native Filter expressions -/

section Signed
variable {ι : Type u} {l : Filter ι}

theorem rat_upper_refl (f : ι → ℚ) :
    ∃ C : ℚ, 0 < C ∧ ∀ᶠ x in l, f x ≤ C * f x :=
  ⟨1, by norm_num, Eventually.of_forall fun _ => by simp⟩

theorem rat_lower_refl (f : ι → ℚ) :
    ∃ c : ℚ, 0 < c ∧ ∀ᶠ x in l, c * f x ≤ f x :=
  ⟨1, by norm_num, Eventually.of_forall fun _ => by simp⟩

theorem rat_twoSided_iff (f g : ι → ℚ) :
    (∃ c C : ℚ, 0 < c ∧ 0 < C ∧
      ∀ᶠ x in l, c * g x ≤ f x ∧ f x ≤ C * g x) ↔
      (∃ C : ℚ, 0 < C ∧ ∀ᶠ x in l, f x ≤ C * g x) ∧
      (∃ c : ℚ, 0 < c ∧ ∀ᶠ x in l, c * g x ≤ f x) := by
  constructor
  · rintro ⟨c, C, hc, hC, hbound⟩
    exact ⟨⟨C, hC, hbound.mono fun _ hx => hx.2⟩,
      ⟨c, hc, hbound.mono fun _ hx => hx.1⟩⟩
  · rintro ⟨⟨C, hC, hupper⟩, ⟨c, hc, hlower⟩⟩
    exact ⟨c, C, hc, hC, hlower.and hupper⟩

theorem rat_twoSided_refl (f : ι → ℚ) :
    ∃ c C : ℚ, 0 < c ∧ 0 < C ∧
      ∀ᶠ x in l, c * f x ≤ f x ∧ f x ≤ C * f x :=
  (rat_twoSided_iff f f).mpr ⟨rat_upper_refl f, rat_lower_refl f⟩

theorem rat_upper_trans {f g h : ι → ℚ}
    (hfg : ∃ C : ℚ, 0 < C ∧ ∀ᶠ x in l, f x ≤ C * g x)
    (hgh : ∃ D : ℚ, 0 < D ∧ ∀ᶠ x in l, g x ≤ D * h x) :
    ∃ C : ℚ, 0 < C ∧ ∀ᶠ x in l, f x ≤ C * h x := by
  obtain ⟨C, hC, hfg⟩ := hfg
  obtain ⟨D, hD, hgh⟩ := hgh
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  filter_upwards [hfg, hgh] with x hx hy
  calc
    f x ≤ C * g x := hx
    _ ≤ C * (D * h x) := mul_le_mul_of_nonneg_left hy hC.le
    _ = (C * D) * h x := (mul_assoc _ _ _).symm

theorem rat_lower_iff_reverse_upper (f g : ι → ℚ) :
    (∃ c : ℚ, 0 < c ∧ ∀ᶠ x in l, c * g x ≤ f x) ↔
      (∃ C : ℚ, 0 < C ∧ ∀ᶠ x in l, g x ≤ C * f x) := by
  constructor
  · rintro ⟨c, hc, hbound⟩
    refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
    filter_upwards [hbound] with x hx
    have hm := mul_le_mul_of_nonneg_left hx (inv_pos.mpr hc).le
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul] using hm
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
    filter_upwards [hbound] with x hx
    have hm := mul_le_mul_of_nonneg_left hx (inv_pos.mpr hC).le
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hC), one_mul] using hm

theorem rat_twoSided_symm {f g : ι → ℚ}
    (h : ∃ c C : ℚ, 0 < c ∧ 0 < C ∧
      ∀ᶠ x in l, c * g x ≤ f x ∧ f x ≤ C * g x) :
    ∃ c C : ℚ, 0 < c ∧ 0 < C ∧
      ∀ᶠ x in l, c * f x ≤ g x ∧ g x ≤ C * f x := by
  obtain ⟨hupper, hlower⟩ := (rat_twoSided_iff f g).mp h
  exact (rat_twoSided_iff g f).mpr
    ⟨(rat_lower_iff_reverse_upper f g).mp hlower,
      (rat_lower_iff_reverse_upper g f).mpr hupper⟩

theorem rat_twoSided_trans {f g h : ι → ℚ}
    (hfg : ∃ c C : ℚ, 0 < c ∧ 0 < C ∧
      ∀ᶠ x in l, c * g x ≤ f x ∧ f x ≤ C * g x)
    (hgh : ∃ c C : ℚ, 0 < c ∧ 0 < C ∧
      ∀ᶠ x in l, c * h x ≤ g x ∧ g x ≤ C * h x) :
    ∃ c C : ℚ, 0 < c ∧ 0 < C ∧
      ∀ᶠ x in l, c * h x ≤ f x ∧ f x ≤ C * h x := by
  obtain ⟨hfgU, hfgL⟩ := (rat_twoSided_iff f g).mp hfg
  obtain ⟨hghU, hghL⟩ := (rat_twoSided_iff g h).mp hgh
  apply (rat_twoSided_iff f h).mpr
  exact ⟨rat_upper_trans hfgU hghU,
    (rat_lower_iff_reverse_upper f h).mpr
      (rat_upper_trans ((rat_lower_iff_reverse_upper g h).mp hghL)
        ((rat_lower_iff_reverse_upper f g).mp hfgL))⟩

/-- Only the multiplying context has a sign assumption. The compared functions
remain arbitrary and signed. -/
theorem rat_upper_mul_context {g h : ι → ℚ} (f : ι → ℚ)
    (hf : ∀ᶠ x in l, 0 ≤ f x)
    (hbound : ∃ C : ℚ, 0 < C ∧ ∀ᶠ x in l, h x ≤ C * g x) :
    ∃ C : ℚ, 0 < C ∧ ∀ᶠ x in l, f x * h x ≤ C * (f x * g x) := by
  obtain ⟨C, hC, hbound⟩ := hbound
  refine ⟨C, hC, ?_⟩
  filter_upwards [hf, hbound] with x hfx hx
  calc
    f x * h x ≤ f x * (C * g x) := mul_le_mul_of_nonneg_left hx hfx
    _ = C * (f x * g x) := by ring

end Signed

/-- The context law applies to negative compared factors. -/
theorem signed_context_case :
    ∃ C : ℚ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, (n : ℚ) * (-1) ≤ C * ((n : ℚ) * (-2)) :=
  rat_upper_mul_context (fun n : ℕ => (n : ℚ))
    (Eventually.of_forall fun n => Nat.cast_nonneg n)
    ⟨1 / 2, signed_half_coefficient.1, signed_half_coefficient.2⟩

/-! ## Zero-aware factorization and the signed source witness -/

/-- Compose the standard bounded-factor theorem without an eventual-nonzero
premise. The conclusion is eventual equality, including at filters with zeros. -/
theorem multiplicative_isBigO_factorization {ι : Type u} {𝕜 : Type v}
    [NormedField 𝕜] {l : Filter ι} (f g h : ι → 𝕜) :
    h =O[l] (fun x => f x * g x) ↔
      ∃ u : ι → 𝕜, u =O[l] g ∧ h =ᶠ[l] (fun x => f x * u x) := by
  constructor
  · intro hbound
    obtain ⟨φ, ⟨C, hφ⟩, heq⟩ := isBigO_iff_exists_eq_mul.mp hbound
    refine ⟨fun x => φ x * g x, ?_, ?_⟩
    · have hu : IsBigOWith C l (fun x => φ x * g x) g :=
        isBigOWith_of_eq_mul φ hφ (Eventually.of_forall fun _ => rfl)
      exact hu.isBigO
    · filter_upwards [heq] with x hx
      calc
        h x = φ x * (f x * g x) := hx
        _ = f x * (φ x * g x) := by ring
  · rintro ⟨u, hu, heq⟩
    exact ((isBigO_refl f l).mul hu).congr' heq.symm (Eventually.of_forall fun _ => rfl)

/-- Only the right sign is needed for this direction. A signed upper bound
cannot in general be converted back to a norm bound. -/
private theorem rat_upper_of_isBigO {ι : Type u} {l : Filter ι} {f g : ι → ℚ}
    (hg : ∀ᶠ x in l, 0 ≤ g x) (hbound : f =O[l] g) :
    ∃ C : ℚ, 0 < C ∧ ∀ᶠ x in l, f x ≤ C * g x := by
  obtain ⟨c, hc, hnorm⟩ := isBigO_iff'.mp hbound
  obtain ⟨K, hK⟩ := exists_nat_gt c
  have hKpos : 0 < K := (Nat.cast_pos (α := ℝ)).mp (hc.trans hK)
  refine ⟨(K : ℚ), Nat.cast_pos.mpr hKpos, ?_⟩
  filter_upwards [hg, hnorm] with x hgx hx
  have hgr : 0 ≤ (g x : ℝ) := Rat.cast_nonneg.mpr hgx
  have hnormg : ‖g x‖ = (g x : ℝ) := by
    rw [← Rat.norm_cast_real, Real.norm_of_nonneg hgr]
  have hleft : (f x : ℝ) ≤ ‖f x‖ := by
    rw [← Rat.norm_cast_real]
    exact Real.le_norm_self _
  rw [hnormg] at hx
  have hupper : (f x : ℝ) ≤ (K : ℝ) * (g x : ℝ) :=
    (hleft.trans hx).trans (mul_le_mul_of_nonneg_right hK.le hgr)
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_mul, Rat.cast_natCast] using hupper

/-- The existential witness is an arbitrary signed rational function. Its
one-sided upper bound is deliberately weaker than norm Big O. -/
theorem rat_upper_factorization {ι : Type u} {l : Filter ι} (f g h : ι → ℚ)
    (hf : ∀ᶠ x in l, 0 ≤ f x) (hg : ∀ᶠ x in l, 0 ≤ g x)
    (hh : ∀ᶠ x in l, 0 ≤ h x) :
    (∃ C : ℚ, 0 < C ∧ ∀ᶠ x in l, h x ≤ C * (f x * g x)) ↔
      ∃ u : ι → ℚ,
        (∃ C : ℚ, 0 < C ∧ ∀ᶠ x in l, u x ≤ C * g x) ∧
        h =ᶠ[l] (fun x => f x * u x) := by
  constructor
  · intro hupper
    have hfg : ∀ᶠ x in l, 0 ≤ f x * g x :=
      (hf.and hg).mono fun _ hx => mul_nonneg hx.1 hx.2
    have hnorm := (isBigO_rat_iff_eventually_le_mul h (fun x => f x * g x) hh hfg).mpr hupper
    obtain ⟨u, hu, heq⟩ := (multiplicative_isBigO_factorization f g h).mp hnorm
    exact ⟨u, rat_upper_of_isBigO hg hu, heq⟩
  · rintro ⟨u, ⟨C, hC, hupper⟩, heq⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [hf, hupper, heq] with x hfx hx heqx
    rw [heqx]
    calc
      f x * u x ≤ f x * (C * g x) := mul_le_mul_of_nonneg_left hx hfx
      _ = C * (f x * g x) := by ring

/-- The source conditional is ordinary division even at a zero denominator. -/
theorem conditional_factor_eq_div {ι : Type u} (f h : ι → ℚ) (x : ι) :
    (if f x = 0 then 0 else h x / f x) = h x / f x := by
  by_cases hx : f x = 0 <;> simp [hx]

theorem parity_factorization :
    ∃ u : ℕ → ℚ,
      (∃ C : ℚ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, u n ≤ C * ((n : ℚ) + 1)) ∧
      (fun n : ℕ => (if n % 2 = 0 then (0 : ℚ) else 1) * ((n : ℚ) + 1))
        =ᶠ[atTop] (fun n => (if n % 2 = 0 then (0 : ℚ) else 1) * u n) := by
  let f : ℕ → ℚ := fun n => if n % 2 = 0 then 0 else 1
  let g : ℕ → ℚ := fun n => (n : ℚ) + 1
  have hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f n := Eventually.of_forall fun n => by
    dsimp only [f]
    split <;> norm_num
  have hg : ∀ᶠ n : ℕ in atTop, 0 ≤ g n := Eventually.of_forall fun n => by
    dsimp only [g]
    positivity
  have hprod : ∀ᶠ n : ℕ in atTop, 0 ≤ f n * g n :=
    (hf.and hg).mono fun _ hn => mul_nonneg hn.1 hn.2
  exact (rat_upper_factorization f g (fun n => f n * g n) hf hg hprod).mp
    ⟨1, by norm_num, Eventually.of_forall fun _ => by simp⟩

theorem parity_factor_not_eventually_nonzero :
    ¬ ∀ᶠ n : ℕ in atTop, (if n % 2 = 0 then (0 : ℚ) else 1) ≠ 0 := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hzero := hN (2 * N) (by omega)
  rw [Nat.mul_mod_right, ite_eq_left rfl] at hzero
  exact hzero rfl

theorem finite_zero_factorization :
    ∃ u : ℕ → ℚ, u =O[atTop] (fun _ : ℕ => (1 : ℚ)) ∧
      (fun n : ℕ => if n = 0 then (1 : ℚ) else 0) =ᶠ[atTop]
        (fun n => (0 : ℚ) * u n) := by
  have heq : (fun n : ℕ => if n = 0 then (1 : ℚ) else 0) =ᶠ[atTop]
      (fun _ : ℕ => (0 : ℚ)) :=
    eventually_atTop.mpr ⟨1, fun n hn => by simp [show n ≠ 0 by omega]⟩
  have hnorm : (fun n : ℕ => if n = 0 then (1 : ℚ) else 0) =O[atTop]
      (fun _ : ℕ => (0 : ℚ)) := isBigO_zero_right_iff.mpr heq
  apply (multiplicative_isBigO_factorization (fun _ : ℕ => (0 : ℚ))
    (fun _ : ℕ => (1 : ℚ)) (fun n : ℕ => if n = 0 then (1 : ℚ) else 0)).mp
  simpa only [zero_mul] using hnorm

theorem finite_zero_no_global_factorization :
    ¬ ∃ u : ℕ → ℚ, ∀ n : ℕ,
      (if n = 0 then (1 : ℚ) else 0) = (0 : ℚ) * u n := by
  rintro ⟨u, hu⟩
  have hzero := hu 0
  norm_num at hzero

/-- This particular supplied source witness is not norm-bounded. -/
theorem signed_factor_witness :
    (∃ C : ℚ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, -(n : ℚ) ≤ C * 1) ∧
      ((fun _ : ℕ => (0 : ℚ)) =ᶠ[atTop] (fun n => (0 : ℚ) * (-(n : ℚ)))) ∧
      ¬ ((fun n : ℕ => -(n : ℚ)) =O[atTop] (fun _ : ℕ => (1 : ℚ))) :=
  ⟨signed_negative_upper, Eventually.of_forall fun _ => by simp, signed_negative_not_isBigO⟩

theorem zero_product_from_signed_witness :
    ∃ C : ℚ, 0 < C ∧ ∀ᶠ _n : ℕ in atTop, (0 : ℚ) ≤ C * (0 * 1) := by
  have hzero : ∀ᶠ _n : ℕ in atTop, 0 ≤ (0 : ℚ) := Eventually.of_forall fun _ => le_rfl
  have hone : ∀ᶠ _n : ℕ in atTop, 0 ≤ (1 : ℚ) :=
    Eventually.of_forall fun _ => by norm_num
  exact (rat_upper_factorization (fun _ : ℕ => (0 : ℚ)) (fun _ : ℕ => (1 : ℚ))
    (fun _ : ℕ => (0 : ℚ)) hzero hone hzero).mpr
    ⟨fun n : ℕ => -(n : ℚ), signed_factor_witness.1, signed_factor_witness.2.1⟩

/-- Factor an actual observation mathematically; no new execution is priced. -/
theorem recursive_fold_factorization (c : ℕ) (f : β → α → β) (e : β) (a : α) :
    ∃ u : ℕ → ℝ, u =O[atTop] (fun n : ℕ => (n : ℝ)) ∧
      (fun n : ℕ => ((foldlViaInit c f e (List.replicate n a)).2 : ℝ)) =ᶠ[atTop]
        (fun n => (n : ℝ) * u n) := by
  apply (multiplicative_isBigO_factorization (fun n : ℕ => (n : ℝ))
    (fun n : ℕ => (n : ℝ))
    (fun n : ℕ => ((foldlViaInit c f e (List.replicate n a)).2 : ℝ))).mp
  simpa only [Nat.cast_mul] using (recursive_fold_theta c f e a).1

theorem recursive_fold_not_global_factorization
    (c : ℕ) (f : β → α → β) (e : β) (a : α) :
    ¬ ∃ u : ℕ → ℝ, ∀ n : ℕ,
      ((foldlViaInit c f e (List.replicate n a)).2 : ℝ) = (n : ℝ) * u n := by
  rintro ⟨u, hu⟩
  have hzero := hu 0
  have hwork := congrArg (fun k : ℕ => (k : ℝ)) (fold_nil_costs c f e a).1
  rw [hwork] at hzero
  norm_num at hzero

/-! ## Exact ceiling witness and failure of additive context -/

/-- This retains the source's concrete expression, even for negative inputs. -/
theorem lt_ceil_natAbs_add_one (q : ℚ) :
    q < ((q.ceil.natAbs + 1 : ℕ) : ℚ) := by
  have hceil : q ≤ (q.ceil : ℚ) := Rat.le_ceil
  have habs : (q.ceil : ℚ) ≤ ((q.ceil.natAbs : ℕ) : ℚ) := by
    simpa only [Int.cast_natCast] using
      ((Int.cast_le (R := ℚ)).mpr (Int.le_natAbs (a := q.ceil)))
  have hsucc : ((q.ceil.natAbs : ℕ) : ℚ) < ((q.ceil.natAbs + 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.lt_succ_self q.ceil.natAbs
  exact (hceil.trans habs).trans_lt hsucc

theorem additive_context_counterexample :
    (∃ C : ℚ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      2 * (n : ℚ) * (n : ℚ) ≤ C * ((n : ℚ) * (n : ℚ) + 1)) ∧
    ¬ ∃ C : ℚ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      2 * (n : ℚ) * (n : ℚ) ≤ (n : ℚ) * (n : ℚ) + C := by
  constructor
  · refine ⟨2, by norm_num, Eventually.of_forall ?_⟩
    intro n
    nlinarith
  · rintro ⟨C, _, hbound⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
    let n := max N (C.ceil.natAbs + 1)
    have hNn : N ≤ n := le_max_left _ _
    have habove : C.ceil.natAbs + 1 ≤ n := le_max_right _ _
    have hCn : C < (n : ℚ) := (lt_ceil_natAbs_add_one C).trans_le (by exact_mod_cast habove)
    have hn : 1 ≤ n := (show 1 ≤ C.ceil.natAbs + 1 by omega).trans habove
    have hnq : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    have hnSquare : (n : ℚ) ≤ (n : ℚ) * (n : ℚ) := by nlinarith
    have hfailure := hN n hNn
    nlinarith

end Examples.ResourceGrowth
