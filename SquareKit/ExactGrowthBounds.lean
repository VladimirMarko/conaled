import SquareKit.NonnegativeArithmetic
import SquareKit.HarmonicBounds
import SquareKit.LogarithmicSums

/-!
# Exact real bounds from finite logarithmic and square-root observations

The sharper logarithmic bound retains an actual raw lower member. Its real
consequences use the accepted correspondence with the standard real functions.
The fixed coefficients are finite witnesses, with no optimality claim.
-/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.ExactGrowthBounds
open NonnegativeArithmetic
open scoped NNReal BigOperators

noncomputable section

/-- The logarithm of one is exactly zero; larger inputs permit twice the floor.
The lower endpoint remains an actual raw approximation. -/
theorem bounded_log_twice_floor (n : ℕ) (hn : 1 ≤ n) :
    Bounded (logarithm n) (n.log2 : ℚ) (2 * (n.log2 : ℚ)) := by
  by_cases he : n = 1
  · subst n
    simpa using bounded_log_power 0
  · have hn2 : 2 ≤ n := by omega
    have hlog : 1 ≤ n.log2 :=
      (Nat.le_log2 (by omega : n ≠ 0)).mpr (by simpa using hn2)
    have hlogq : (1 : ℚ) ≤ (n.log2 : ℚ) := by exact_mod_cast hlog
    have hb := bounded_log n hn
    refine ⟨hb.1, ?_⟩
    intro a ha
    have hu : a ≤ (n.log2 : ℚ) + 1 := hb.2 ha
    calc
      a ≤ (n.log2 : ℚ) + 1 := hu
      _ ≤ (n.log2 : ℚ) + (n.log2 : ℚ) := add_le_add le_rfl hlogq
      _ = 2 * (n.log2 : ℚ) := (two_mul _).symm

/-- The actual standard logarithm lies between its floor and twice that floor
on the source's valid domain, including the exact zero at one. -/
theorem logb_floor_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n.log2 : ℝ) ≤ Real.logb 2 (n : ℝ) ∧
      Real.logb 2 (n : ℝ) ≤ 2 * (n.log2 : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hlog0 : 0 ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hn)
  obtain ⟨x, hx, hlo, hhi⟩ :=
    rel_bounds_real (raw_related (logarithm n)) (bounded_log_twice_floor n hn)
  have hx' : Real.toNNReal (Real.logb 2 (n : ℝ)) = x := by
    apply WithBot.coe_injective
    simpa only [value_logarithm, logarithmValue, ite_eq_right hn0] using hx
  rw [← hx'] at hlo hhi
  simpa only [Real.coe_toNNReal _ hlog0, Rat.cast_natCast, Rat.cast_mul,
    Rat.cast_ofNat] using And.intro hlo hhi

/-- The actual standard square root is bracketed by the native floor root,
with no positive-input restriction. -/
theorem sqrt_floor_bounds (n : ℕ) :
    (n.sqrt : ℝ) ≤ Real.sqrt (n : ℝ) ∧
      Real.sqrt (n : ℝ) ≤ (n.sqrt : ℝ) + 1 := by
  obtain ⟨x, hx, hlo, hhi⟩ :=
    rel_bounds_real (raw_related (squareRoot n)) (bounded_root n)
  have hx' : NNReal.sqrt (n : ℝ≥0) = x := by
    apply WithBot.coe_injective
    simpa only [value_squareRoot, squareRootValue] using hx
  rw [← hx'] at hlo hhi
  simpa only [Real.coe_sqrt, NNReal.coe_natCast, Rat.cast_natCast,
    Rat.cast_add, Rat.cast_one] using And.intro hlo hhi

/-- Positive inputs make the floor root at least one. -/
theorem sqrt_twice_floor_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n.sqrt : ℝ) ≤ Real.sqrt (n : ℝ) ∧
      Real.sqrt (n : ℝ) ≤ 2 * (n.sqrt : ℝ) := by
  have hb := sqrt_floor_bounds n
  have hk : 1 ≤ n.sqrt := Nat.le_sqrt.mpr (by simpa using hn)
  have hkR : (1 : ℝ) ≤ (n.sqrt : ℝ) := by exact_mod_cast hk
  exact ⟨hb.1, by linarith [hb.2]⟩

/-- The exact finite comparison retains coefficient two and threshold sixteen. -/
theorem n_log_le_two_n_sqrt (n : ℕ) (hn : 16 ≤ n) :
    (n : ℝ) * Real.logb 2 (n : ℝ) ≤
      2 * ((n : ℝ) * Real.sqrt (n : ℝ)) := by
  have hlog := logb_floor_bounds n (by omega)
  have hroot := (sqrt_floor_bounds n).1
  have hcompare : (n.log2 : ℝ) ≤ (n.sqrt : ℝ) := by
    exact_mod_cast DiscreteScales.log2_le_sqrt hn
  calc
    (n : ℝ) * Real.logb 2 (n : ℝ) ≤ (n : ℝ) * (2 * (n.log2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog.2 (Nat.cast_nonneg n)
    _ ≤ (n : ℝ) * (2 * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hcompare.trans hroot) (by norm_num))
        (Nat.cast_nonneg n)
    _ = 2 * ((n : ℝ) * Real.sqrt (n : ℝ)) := by ring

/-- Both exact harmonic/logarithm coefficients hold from index two. -/
theorem harmonic_logb_coefficients (n : ℕ) (hn : 2 ≤ n) :
    (harmonic n : ℝ) ≤ 3 * Real.logb 2 (n : ℝ) ∧
      Real.logb 2 (n : ℝ) ≤ 4 * (harmonic n : ℝ) := by
  have hlog := logb_floor_bounds n (by omega)
  have hb := HarmonicBounds.harmonic_log2_coefficients n hn
  have hloQ : (n.log2 : ℚ) ≤ 2 * harmonic n := by
    linarith only [hb.1]
  have hlo : (n.log2 : ℝ) ≤ 2 * (harmonic n : ℝ) := by
    exact_mod_cast hloQ
  have hhi : (harmonic n : ℝ) ≤ 3 * (n.log2 : ℝ) := by
    exact_mod_cast hb.2
  constructor <;> linarith only [hlog.1, hlog.2, hlo, hhi]

/-- Nonnegative index scaling preserves the separate coefficients three and four. -/
theorem mul_harmonic_logb_coefficients (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * (harmonic n : ℝ) ≤ 3 * ((n : ℝ) * Real.logb 2 (n : ℝ)) ∧
      (n : ℝ) * Real.logb 2 (n : ℝ) ≤ 4 * ((n : ℝ) * (harmonic n : ℝ)) := by
  have hb := harmonic_logb_coefficients n hn
  constructor
  · calc
      (n : ℝ) * (harmonic n : ℝ) ≤ (n : ℝ) * (3 * Real.logb 2 (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hb.1 (Nat.cast_nonneg n)
      _ = 3 * ((n : ℝ) * Real.logb 2 (n : ℝ)) := by ring
  · calc
      (n : ℝ) * Real.logb 2 (n : ℝ) ≤ (n : ℝ) * (4 * (harmonic n : ℝ)) :=
        mul_le_mul_of_nonneg_left hb.2 (Nat.cast_nonneg n)
      _ = 4 * ((n : ℝ) * (harmonic n : ℝ)) := by ring

/-- Finite native factorial bounds give exact logarithmic witnesses four and twelve. -/
theorem factorial_logb_coefficients (n : ℕ) (hn : 4 ≤ n) :
    Real.logb 2 (Nat.factorial n : ℝ) ≤ 4 * ((n : ℝ) * Real.logb 2 (n : ℝ)) ∧
      (n : ℝ) * Real.logb 2 (n : ℝ) ≤ 12 * Real.logb 2 (Nat.factorial n : ℝ) := by
  have hfactorial := logb_floor_bounds (Nat.factorial n)
    (Nat.succ_le_iff.mpr (Nat.factorial_pos n))
  have hlog := logb_floor_bounds n (by omega)
  have hb := LogarithmicSums.factorial_log2_bounds n hn
  have hlo : (n : ℝ) * (n.log2 : ℝ) ≤ 6 * ((Nat.factorial n).log2 : ℝ) := by
    exact_mod_cast hb.1
  have hhi : ((Nat.factorial n).log2 : ℝ) ≤ 2 * ((n : ℝ) * (n.log2 : ℝ)) := by
    exact_mod_cast hb.2
  have hscaledLo := mul_le_mul_of_nonneg_left hlog.1 (Nat.cast_nonneg n)
  have hscaledHi := mul_le_mul_of_nonneg_left hlog.2 (Nat.cast_nonneg n)
  constructor
  · calc
      Real.logb 2 (Nat.factorial n : ℝ) ≤ 2 * ((Nat.factorial n).log2 : ℝ) :=
        hfactorial.2
      _ ≤ 4 * ((n : ℝ) * (n.log2 : ℝ)) := by linarith only [hhi]
      _ ≤ 4 * ((n : ℝ) * Real.logb 2 (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hscaledLo (by norm_num)
  · calc
      (n : ℝ) * Real.logb 2 (n : ℝ) ≤ 2 * ((n : ℝ) * (n.log2 : ℝ)) := by
        nlinarith only [hscaledHi]
      _ ≤ 12 * ((Nat.factorial n).log2 : ℝ) := by linarith only [hlo]
      _ ≤ 12 * Real.logb 2 (Nat.factorial n : ℝ) :=
        mul_le_mul_of_nonneg_left hfactorial.1 (by norm_num)

/-- The standard positive weighted sum is enclosed by its floor sum at every n.
This is a real inequality; actual raw attainment belongs to the syntax-family theorem. -/
theorem weighted_logb_floor_bounds (n : ℕ) :
    ((∑ k ∈ Finset.Ico 1 (n + 1), k * Nat.log2 k : ℕ) : ℝ) ≤
      (∑ k ∈ Finset.Ico 1 (n + 1), (k : ℝ) * Real.logb 2 (k : ℝ)) ∧
      (∑ k ∈ Finset.Ico 1 (n + 1), (k : ℝ) * Real.logb 2 (k : ℝ)) ≤
        2 * ((∑ k ∈ Finset.Ico 1 (n + 1), k * Nat.log2 k : ℕ) : ℝ) := by
  have hcast : ((∑ k ∈ Finset.Ico 1 (n + 1), k * Nat.log2 k : ℕ) : ℝ) =
      ∑ k ∈ Finset.Ico 1 (n + 1), (k : ℝ) * (Nat.log2 k : ℝ) := by
    simp only [Nat.cast_sum, Nat.cast_mul]
  constructor
  · rw [hcast]
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left
      (logb_floor_bounds k (Finset.mem_Ico.mp hk).1).1 (Nat.cast_nonneg k)
  · calc
      (∑ k ∈ Finset.Ico 1 (n + 1), (k : ℝ) * Real.logb 2 (k : ℝ)) ≤
          ∑ k ∈ Finset.Ico 1 (n + 1), (k : ℝ) * (2 * (Nat.log2 k : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left
          (logb_floor_bounds k (Finset.mem_Ico.mp hk).1).2 (Nat.cast_nonneg k)
      _ = 2 * ((∑ k ∈ Finset.Ico 1 (n + 1), k * Nat.log2 k : ℕ) : ℝ) := by
        rw [hcast, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring

/-- The exact positive weighted sum retains coefficients two and thirty-six. -/
theorem weighted_logb_coefficients (n : ℕ) (hn : 4 ≤ n) :
    (∑ k ∈ Finset.Ico 1 (n + 1), (k : ℝ) * Real.logb 2 (k : ℝ)) ≤
      2 * ((n : ℝ) ^ 2 * Real.logb 2 (n : ℝ)) ∧
      (n : ℝ) ^ 2 * Real.logb 2 (n : ℝ) ≤
        36 * (∑ k ∈ Finset.Ico 1 (n + 1), (k : ℝ) * Real.logb 2 (k : ℝ)) := by
  have hsum := weighted_logb_floor_bounds n
  have hlog := logb_floor_bounds n (by omega)
  have hb := LogarithmicSums.weighted_log_bounds n hn
  have hlo : (n : ℝ) * (n : ℝ) * (n.log2 : ℝ) ≤
      18 * ((∑ k ∈ Finset.Ico 1 (n + 1), k * Nat.log2 k : ℕ) : ℝ) := by
    exact_mod_cast hb.1
  have hhi : ((∑ k ∈ Finset.Ico 1 (n + 1), k * Nat.log2 k : ℕ) : ℝ) ≤
      (n : ℝ) * (n : ℝ) * (n.log2 : ℝ) := by
    exact_mod_cast hb.2
  have hscaledLo := mul_le_mul_of_nonneg_left hlog.1 (sq_nonneg (n : ℝ))
  have hscaledHi := mul_le_mul_of_nonneg_left hlog.2 (sq_nonneg (n : ℝ))
  constructor
  · calc
      (∑ k ∈ Finset.Ico 1 (n + 1), (k : ℝ) * Real.logb 2 (k : ℝ)) ≤
          2 * ((∑ k ∈ Finset.Ico 1 (n + 1), k * Nat.log2 k : ℕ) : ℝ) := hsum.2
      _ ≤ 2 * ((n : ℝ) ^ 2 * (n.log2 : ℝ)) := by nlinarith only [hhi]
      _ ≤ 2 * ((n : ℝ) ^ 2 * Real.logb 2 (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hscaledLo (by norm_num)
  · calc
      (n : ℝ) ^ 2 * Real.logb 2 (n : ℝ) ≤
          2 * ((n : ℝ) ^ 2 * (n.log2 : ℝ)) := by nlinarith only [hscaledHi]
      _ ≤ 36 * ((∑ k ∈ Finset.Ico 1 (n + 1), k * Nat.log2 k : ℕ) : ℝ) := by
        nlinarith only [hlo]
      _ ≤ 36 * (∑ k ∈ Finset.Ico 1 (n + 1), (k : ℝ) * Real.logb 2 (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum.1 (by norm_num)

/-- The lower exact logarithmic terms preserve the finite cubic witnesses six and one. -/
theorem cubic_logb_coefficients (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ 3 + (n : ℝ) ^ 2 + (n : ℝ) * Real.logb 2 (n : ℝ) ≤
      6 * (n : ℝ) ^ 3 ∧
      (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 + (n : ℝ) ^ 2 + (n : ℝ) * Real.logb 2 (n : ℝ) := by
  have hlog := logb_floor_bounds n hn
  have hb : (n : ℝ) * (n : ℝ) * (n : ℝ) + (n : ℝ) * (n : ℝ) +
      (n : ℝ) * (n.log2 : ℝ) ≤ 3 * ((n : ℝ) * (n : ℝ) * (n : ℝ)) := by
    exact_mod_cast (DiscreteScales.cubic_lower_terms_bounds n).2
  have hscaled := mul_le_mul_of_nonneg_left hlog.2 (Nat.cast_nonneg n)
  have hlog0 : 0 ≤ Real.logb 2 (n : ℝ) :=
    (Nat.cast_nonneg n.log2).trans hlog.1
  have hnlog0 := mul_nonneg (Nat.cast_nonneg n) hlog0
  have hcube0 := pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)) 3
  constructor
  · nlinarith only [hb, hscaled, hcube0, sq_nonneg (n : ℝ)]
  · nlinarith only [hnlog0, sq_nonneg (n : ℝ)]

/-- Every positive natural coefficient and every threshold has a strict exact-real
counterexample. The existing discrete proof supplies a symbolic power-of-two square. -/
theorem linear_plus_sqrt_counterexample (C : ℕ) (hC : 0 < C) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (C : ℝ) * (Real.sqrt (n : ℝ) * Real.logb 2 (n : ℝ)) <
      (n : ℝ) + Real.sqrt (n : ℝ) := by
  have hfourC : (0 : ℚ) < 4 * (C : ℚ) :=
    mul_pos (by norm_num) (by exact_mod_cast hC)
  obtain ⟨n, hn, hstrict⟩ :=
    DiscreteScales.sqrt_log2_counterexample (4 * (C : ℚ)) hfourC (max N 2)
  have hnN : N ≤ n := (le_max_left N 2).trans hn
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
  have hlog := logb_floor_bounds n (by omega)
  have hroot := sqrt_twice_floor_bounds n (by omega)
  have hstrictR : (4 * (C : ℝ)) * ((n.sqrt : ℝ) * (n.log2 : ℝ)) <
      (n : ℝ) + (n.sqrt : ℝ) := by exact_mod_cast hstrict
  have hlog0 : 0 ≤ Real.logb 2 (n : ℝ) :=
    (Nat.cast_nonneg n.log2).trans hlog.1
  have hprod : Real.sqrt (n : ℝ) * Real.logb 2 (n : ℝ) ≤
      4 * ((n.sqrt : ℝ) * (n.log2 : ℝ)) := by
    calc
      Real.sqrt (n : ℝ) * Real.logb 2 (n : ℝ) ≤
          (2 * (n.sqrt : ℝ)) * Real.logb 2 (n : ℝ) :=
        mul_le_mul_of_nonneg_right hroot.2 hlog0
      _ ≤ (2 * (n.sqrt : ℝ)) * (2 * (n.log2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog.2 (by positivity)
      _ = 4 * ((n.sqrt : ℝ) * (n.log2 : ℝ)) := by ring
  refine ⟨n, hnN, ?_⟩
  calc
    (C : ℝ) * (Real.sqrt (n : ℝ) * Real.logb 2 (n : ℝ)) ≤
        (C : ℝ) * (4 * ((n.sqrt : ℝ) * (n.log2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg C)
    _ = (4 * (C : ℝ)) * ((n.sqrt : ℝ) * (n.log2 : ℝ)) := by ring
    _ < (n : ℝ) + (n.sqrt : ℝ) := hstrictR
    _ ≤ (n : ℝ) + Real.sqrt (n : ℝ) := add_le_add le_rfl hroot.1

/-! Connected boundary cases. They use the public results and the independently
required domains/constants rather than the proof construction. -/

example : Bounded (logarithm 1) 0 0 := by
  simpa using bounded_log_twice_floor 1 (by decide)

example : Real.logb 2 (1 : ℝ) = 0 := by
  have hb := logb_floor_bounds 1 (by decide)
  have hlog : (1 : ℕ).log2 = 0 := by decide
  rw [hlog, Nat.cast_zero, mul_zero] at hb
  simpa only [Nat.cast_one] using le_antisymm hb.2 hb.1

example : (16 : ℝ) * Real.logb 2 (16 : ℝ) ≤
    2 * ((16 : ℝ) * Real.sqrt (16 : ℝ)) :=
  n_log_le_two_n_sqrt 16 (by decide)

example : (harmonic 2 : ℝ) ≤ 3 * Real.logb 2 (2 : ℝ) ∧
    Real.logb 2 (2 : ℝ) ≤ 4 * (harmonic 2 : ℝ) :=
  harmonic_logb_coefficients 2 (by decide)

example : ¬ (harmonic 1 : ℝ) ≤ 3 * Real.logb 2 (1 : ℝ) := by
  norm_num [harmonic]

example : Real.logb 2 (Nat.factorial 4 : ℝ) ≤ 4 * ((4 : ℝ) * Real.logb 2 (4 : ℝ)) ∧
    (4 : ℝ) * Real.logb 2 (4 : ℝ) ≤ 12 * Real.logb 2 (Nat.factorial 4 : ℝ) :=
  factorial_logb_coefficients 4 (by decide)

example : (∑ k ∈ Finset.Ico 1 ((0 : ℕ) + 1), (k : ℝ) * Real.logb 2 (k : ℝ)) = 0 := by
  have hb := weighted_logb_floor_bounds 0
  have hw : (∑ k ∈ Finset.Ico 1 ((0 : ℕ) + 1), k * Nat.log2 k : ℕ) = 0 := by simp
  simp only [hw, Nat.cast_zero, mul_zero] at hb
  exact le_antisymm hb.2 hb.1

example : (∑ k ∈ Finset.Ico 1 ((1 : ℕ) + 1), (k : ℝ) * Real.logb 2 (k : ℝ)) = 0 := by
  have hb := weighted_logb_floor_bounds 1
  have hw : (∑ k ∈ Finset.Ico 1 ((1 : ℕ) + 1), k * Nat.log2 k : ℕ) = 0 := by decide
  simp only [hw, Nat.cast_zero, mul_zero] at hb
  exact le_antisymm hb.2 hb.1

example (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ Real.sqrt (n : ℝ) * Real.logb 2 (n : ℝ) <
      (n : ℝ) + Real.sqrt (n : ℝ) := by
  simpa only [Nat.cast_one, one_mul] using linear_plus_sqrt_counterexample 1 (by decide) N

end
end SquareKit.ExactGrowthBounds
