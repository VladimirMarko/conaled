import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite rational harmonic bounds

The harmonic number is the existing Mathlib `harmonic`. A shifted block is a
native finite sum with exactly `k` denominators, from `m + 1` through `m + k`.
The dyadic estimates use these finite blocks and rational inequalities.
-/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.HarmonicBounds

open scoped BigOperators

/-- Nonnegativity of the native rational harmonic sum, including zero. -/
theorem harmonic_nonneg (n : Nat) : 0 ≤ harmonic n := by
  unfold harmonic
  exact Finset.sum_nonneg fun j _ => inv_nonneg.mpr (Nat.cast_nonneg (j + 1))

/-- The shifted block has exactly `k` nonnegative reciprocal summands. -/
theorem block_nonneg (m k : Nat) :
    0 ≤ ∑ j ∈ Finset.range k, (((m + j + 1 : Nat) : ℚ)⁻¹) := by
  exact Finset.sum_nonneg fun j _ => inv_nonneg.mpr (Nat.cast_nonneg (m + j + 1))

/-- Native finite-range splitting preserves the starting denominator. -/
theorem harmonic_append (m k : Nat) :
    harmonic (m + k) = harmonic m +
      ∑ j ∈ Finset.range k, (((m + j + 1 : Nat) : ℚ)⁻¹) := by
  simpa only [harmonic] using
    (Finset.sum_range_add (fun j : Nat => (((j + 1 : Nat) : ℚ)⁻¹)) m k)

/-- Adding a nonnegative reciprocal block makes the native harmonic sequence monotone. -/
theorem harmonic_mono : Monotone harmonic := by
  intro m n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [harmonic_append]
  exact le_add_of_nonneg_right (block_nonneg m k)

/-- A positive upper bound on every denominator gives a lower bound on the whole block. -/
theorem block_lower (m k b : Nat) (hb : 0 < b) (h : m + k ≤ b) :
    (k : ℚ) / (b : ℚ) ≤
      ∑ j ∈ Finset.range k, (((m + j + 1 : Nat) : ℚ)⁻¹) := by
  calc
    (k : ℚ) / (b : ℚ) = ∑ _j ∈ Finset.range k, (b : ℚ)⁻¹ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ ∑ j ∈ Finset.range k, (((m + j + 1 : Nat) : ℚ)⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hden : m + j + 1 ≤ b := by omega
      apply (inv_le_inv₀ (by exact_mod_cast hb) (by positivity)).2
      exact_mod_cast hden

/-- A positive lower bound on every denominator gives an upper bound on the whole block. -/
theorem block_upper (m k a : Nat) (ha : 0 < a) (h : a ≤ m + 1) :
    (∑ j ∈ Finset.range k, (((m + j + 1 : Nat) : ℚ)⁻¹)) ≤
      (k : ℚ) / (a : ℚ) := by
  calc
    (∑ j ∈ Finset.range k, (((m + j + 1 : Nat) : ℚ)⁻¹)) ≤
        ∑ _j ∈ Finset.range k, (a : ℚ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j _
      have hden : a ≤ m + j + 1 := by omega
      apply (inv_le_inv₀ (by positivity) (by exact_mod_cast ha)).2
      exact_mod_cast hden
    _ = (k : ℚ) / (a : ℚ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_eq_mul_inv]

/-- Every positive doubling block contributes between one half and one. -/
theorem doubling_block_bounds (m : Nat) (hm : 0 < m) :
    (1 / 2 : ℚ) ≤ (∑ j ∈ Finset.range m, (((m + j + 1 : Nat) : ℚ)⁻¹)) ∧
      (∑ j ∈ Finset.range m, (((m + j + 1 : Nat) : ℚ)⁻¹)) ≤ 1 := by
  have hl := block_lower m m (2 * m) (by omega) (by omega)
  have hu := block_upper m m m hm (by omega)
  have hmp : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hhalf : (m : ℚ) / ((2 * m : Nat) : ℚ) = (1 / 2 : ℚ) := by
    apply (div_eq_iff (by positivity)).2
    push_cast
    ring
  constructor
  · simpa only [hhalf] using hl
  · simpa only [div_self (ne_of_gt hmp)] using hu

/-- Finite doubling gives both dyadic bounds, including the initial value `harmonic 1`. -/
theorem harmonic_dyadic_bounds (k : Nat) :
    1 + (k : ℚ) / 2 ≤ harmonic (2 ^ k) ∧
      harmonic (2 ^ k) ≤ 1 + (k : ℚ) := by
  induction k with
  | zero => norm_num [harmonic]
  | succ k ih =>
      have hb := doubling_block_bounds (2 ^ k) (by positivity)
      have he : (2 : Nat) ^ (k + 1) = 2 ^ k + 2 ^ k := by
        rw [pow_succ]
        omega
      rw [he, harmonic_append]
      push_cast at hb ⊢
      constructor <;> linarith [ih.1, ih.2, hb.1, hb.2]

/-- Monotonicity places each positive index between the adjacent dyadic estimates. -/
theorem harmonic_log2_bounds (n : Nat) (hn : 1 ≤ n) :
    (n.log2 : ℚ) / 2 ≤ harmonic n ∧ harmonic n ≤ (n.log2 : ℚ) + 2 := by
  have hlo : harmonic (2 ^ n.log2) ≤ harmonic n :=
    harmonic_mono (Nat.log2_self_le (by omega : n ≠ 0))
  have hhi : harmonic n ≤ harmonic (2 ^ (n.log2 + 1)) :=
    harmonic_mono (Nat.le_of_lt (Nat.lt_log2_self (n := n)))
  have bl := harmonic_dyadic_bounds n.log2
  have bu := harmonic_dyadic_bounds (n.log2 + 1)
  push_cast at bu
  constructor <;> linarith [bl.1, bu.2]

/-- Explicit rational comparison coefficients are valid from index two. -/
theorem harmonic_log2_coefficients (n : Nat) (hn : 2 ≤ n) :
    (1 / 2 : ℚ) * (n.log2 : ℚ) ≤ harmonic n ∧
      harmonic n ≤ 3 * (n.log2 : ℚ) := by
  have hb := harmonic_log2_bounds n (by omega)
  have hk : 1 ≤ n.log2 := (Nat.le_log2 (by omega : n ≠ 0)).2 (by simpa using hn)
  have hkq : (1 : ℚ) ≤ (n.log2 : ℚ) := by exact_mod_cast hk
  constructor <;> linarith [hb.1, hb.2]

/-- Multiplication by the nonnegative natural index preserves the same coefficients. -/
theorem mul_harmonic_log2_coefficients (n : Nat) (hn : 2 ≤ n) :
    (1 / 2 : ℚ) * ((n : ℚ) * (n.log2 : ℚ)) ≤ (n : ℚ) * harmonic n ∧
      (n : ℚ) * harmonic n ≤ 3 * ((n : ℚ) * (n.log2 : ℚ)) := by
  have hb := harmonic_log2_coefficients n hn
  constructor
  · calc
      (1 / 2 : ℚ) * ((n : ℚ) * (n.log2 : ℚ)) =
          (n : ℚ) * ((1 / 2 : ℚ) * (n.log2 : ℚ)) := by ring
      _ ≤ (n : ℚ) * harmonic n := mul_le_mul_of_nonneg_left hb.1 (Nat.cast_nonneg n)
  · calc
      (n : ℚ) * harmonic n ≤ (n : ℚ) * (3 * (n.log2 : ℚ)) :=
        mul_le_mul_of_nonneg_left hb.2 (Nat.cast_nonneg n)
      _ = 3 * ((n : ℚ) * (n.log2 : ℚ)) := by ring

/-- Every rational log band has the stated finite coefficients; its value at zero is unrestricted. -/
theorem harmonic_logBand_coefficients {l : Nat → ℚ}
    (hl : ∀ n, 1 ≤ n → l n ∈ Set.Icc (n.log2 : ℚ) ((n.log2 : ℚ) + 1))
    (n : Nat) (hn : 2 ≤ n) :
    (1 / 4 : ℚ) * l n ≤ harmonic n ∧ harmonic n ≤ 3 * l n := by
  have hv := hl n (by omega)
  have hb := harmonic_log2_coefficients n hn
  have hk : 1 ≤ n.log2 := (Nat.le_log2 (by omega : n ≠ 0)).2 (by simpa using hn)
  have hkq : (1 : ℚ) ≤ (n.log2 : ℚ) := by exact_mod_cast hk
  constructor <;> linarith [hv.1, hv.2, hb.1, hb.2]

end SquareKit.HarmonicBounds
