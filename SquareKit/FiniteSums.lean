import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Positivity

/-!
# Positive finite sums and geometric polynomial identities

The sums use the native positive interval `Finset.Ico 1 (n + 1)`. In particular,
an arbitrary zero term is excluded. Exact natural quotients and finite bounds
are mathematical facts independent of any execution-cost model.
-/
set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.FiniteSums

open Finset
open scoped BigOperators

universe u

/-- Removing the zero term is justified by its value, not by the index notation. -/
theorem sum_Ico_one_eq_sum_range {M : Type u} [AddCommMonoid M]
    (f : Nat → M) (n : Nat) (hzero : f 0 = 0) :
    (∑ k ∈ Ico 1 (n + 1), f k) = ∑ k ∈ range (n + 1), f k := by
  rw [Finset.sum_range_eq_add_Ico f (Nat.succ_pos n), hzero, zero_add]

/-- The list used by the existing work formula has the same nonzero summands. -/
theorem list_range_sum_eq_triangle (n : Nat) :
    (List.range (n + 1)).sum = ∑ k ∈ Ico 1 (n + 1), k := by
  have h : (∑ k ∈ range (n + 1), k) = (List.range (n + 1)).sum := by
    simpa only [List.toFinset_range, List.map_id_fun', id_eq] using
      (List.sum_toFinset (fun k : Nat => k) (List.nodup_range (n := n + 1)))
  exact h.symm.trans (sum_Ico_one_eq_sum_range (fun k : Nat => k) n rfl).symm

/-- Gauss' formula on the positive inclusive interval, with no division. -/
theorem triangle_double (n : Nat) :
    2 * (∑ k ∈ Ico 1 (n + 1), k) = n * (n + 1) := by
  rw [sum_Ico_one_eq_sum_range (fun k : Nat => k) n rfl]
  simpa [Nat.mul_comm] using Finset.sum_range_id_mul_two (n + 1)

/-- The quotient is exact natural division. -/
theorem triangle_exact (n : Nat) :
    (∑ k ∈ Ico 1 (n + 1), k) = n * (n + 1) / 2 := by
  rw [← triangle_double n, Nat.mul_comm 2, Nat.mul_div_cancel _ Nat.zero_lt_two]

/-- Both bounds include the empty interval at zero. -/
theorem triangle_bounds (n : Nat) :
    n * n ≤ 2 * (∑ k ∈ Ico 1 (n + 1), k) ∧
      (∑ k ∈ Ico 1 (n + 1), k) ≤ n * n := by
  have h := triangle_double n
  have hn := Nat.le_mul_self n
  constructor <;> nlinarith

/-- The quadratic specialization of the standard Bernoulli sum formula. -/
theorem squares_six (n : Nat) :
    6 * (∑ k ∈ Ico 1 (n + 1), k * k) = n * (n + 1) * (2 * n + 1) := by
  have h := sum_Ico_pow n 2
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two] at h
  have hq : (6 : ℚ) * (∑ k ∈ Ico 1 (n + 1), (k : ℚ) ^ 2) =
      (n : ℚ) * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1) := by
    nlinarith [h]
  have hn : 6 * (∑ k ∈ Ico 1 (n + 1), k ^ 2) =
      n * (n + 1) * (2 * n + 1) := by
    exact_mod_cast hq
  simpa only [pow_two] using hn

/-- The square-sum quotient is also exact natural division. -/
theorem squares_exact (n : Nat) :
    (∑ k ∈ Ico 1 (n + 1), k * k) = n * (n + 1) * (2 * n + 1) / 6 := by
  rw [← squares_six n, Nat.mul_comm 6, Nat.mul_div_cancel _ (by decide : 0 < 6)]

/-- Cubic comparison holds at every natural index, including zero. -/
theorem squares_bounds (n : Nat) :
    n * n * n ≤ 6 * (∑ k ∈ Ico 1 (n + 1), k * k) ∧
      (∑ k ∈ Ico 1 (n + 1), k * k) ≤ n * n * n := by
  constructor
  · rw [squares_six]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left n (Nat.le_succ n)) (by omega)
  · calc
      (∑ k ∈ Ico 1 (n + 1), k * k) ≤ ∑ _k ∈ Ico 1 (n + 1), n * n := by
        apply Finset.sum_le_sum
        intro k hk
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hk).2
        exact Nat.mul_le_mul hkn hkn
      _ = n * n * n := by simp [Nat.mul_comm]


section Geometric

variable {R : Type u} [CommRing R]

/-- Evaluation of the actual finite geometric polynomial preserves all `n+1` terms. -/
theorem geom_eval (x : R) (n : Nat) :
    (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k).eval x =
      ∑ k ∈ range (n + 1), x ^ k := by
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X]

/-- The actual formal derivative has the shifted sum of `n` terms. -/
theorem derivative_geom_eval (x : R) (n : Nat) :
    (Polynomial.derivative
      (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k)).eval x =
      ∑ j ∈ range n, (j + 1 : R) * x ^ j := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Polynomial.derivative_add, Polynomial.derivative_one,
    add_zero, Polynomial.derivative_sum, Polynomial.derivative_X_pow_succ,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]

/-- The positive weighted sum is obtained from that actual derivative. -/
theorem weighted_derivative (x : R) (n : Nat) :
    (∑ k ∈ Ico 1 (n + 1), (k : R) * x ^ k) =
      x * (Polynomial.derivative
        (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k)).eval x := by
  rw [derivative_geom_eval]
  have hshift : (∑ k ∈ Ico 1 (n + 1), (k : R) * x ^ k) =
      ∑ j ∈ range n, (j + 1 : R) * x ^ (j + 1) := by
    simpa [Nat.add_comm, Nat.cast_add, Nat.cast_one, add_comm] using
      (Finset.sum_Ico_eq_sum_range (fun k : Nat => (k : R) * x ^ k) 1 (n + 1))
  rw [hshift, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_succ]
  ring

/-- The polynomial geometric identity, valid even at `X=1` after evaluation. -/
theorem geom_polynomial_scaled (n : Nat) :
    (1 - Polynomial.X) * (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k) =
      1 - Polynomial.X ^ (n + 1) :=
  mul_neg_geom_sum (Polynomial.X : Polynomial R) (n + 1)

/-- Differentiate the polynomial identity before deriving its scaled form. -/
theorem derivative_geom_polynomial_scaled (n : Nat) :
    (1 - Polynomial.X) ^ 2 * Polynomial.derivative
        (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k) =
      1 - Polynomial.C (n + 1 : R) * Polynomial.X ^ n +
        Polynomial.C (n : R) * Polynomial.X ^ (n + 1) := by
  let p : Polynomial R := ∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k
  have hg : (1 - Polynomial.X) * p = 1 - Polynomial.X ^ (n + 1) :=
    geom_polynomial_scaled n
  have hd := congrArg (fun q : Polynomial R => Polynomial.derivative q) hg
  simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_one, Polynomial.derivative_X,
    Polynomial.derivative_X_pow_succ, zero_sub] at hd
  have hfirst : (1 - Polynomial.X) * Polynomial.derivative p =
      p - Polynomial.C (n + 1 : R) * Polynomial.X ^ n := by
    linear_combination hd
  change (1 - Polynomial.X) ^ 2 * Polynomial.derivative p = _
  calc
    (1 - Polynomial.X) ^ 2 * Polynomial.derivative p =
        (1 - Polynomial.X) * ((1 - Polynomial.X) * Polynomial.derivative p) := by ring
    _ = (1 - Polynomial.X) * (p - Polynomial.C (n + 1 : R) * Polynomial.X ^ n) := by
      rw [hfirst]
    _ = (1 - Polynomial.X) * p -
        (1 - Polynomial.X) * (Polynomial.C (n + 1 : R) * Polynomial.X ^ n) := by ring
    _ = (1 - Polynomial.X ^ (n + 1)) -
        (1 - Polynomial.X) * (Polynomial.C (n + 1 : R) * Polynomial.X ^ n) := by rw [hg]
    _ = 1 - Polynomial.C (n + 1 : R) * Polynomial.X ^ n +
        Polynomial.C (n : R) * Polynomial.X ^ (n + 1) := by
      simp only [Polynomial.C_add, Polynomial.C_1, pow_succ]
      ring

/-- The scalar geometric identity retains the exceptional quotient point `x=1`. -/
theorem geom_scaled (x : R) (n : Nat) :
    (1 - x) * (∑ k ∈ range (n + 1), x ^ k) = 1 - x ^ (n + 1) :=
  mul_neg_geom_sum x (n + 1)

/-- Evaluation of the differentiated polynomial identity. -/
theorem derivative_geom_scaled (x : R) (n : Nat) :
    (1 - x) ^ 2 * (∑ j ∈ range n, (j + 1 : R) * x ^ j) =
      1 - (n + 1 : R) * x ^ n + (n : R) * x ^ (n + 1) := by
  have h := congrArg (fun q : Polynomial R => q.eval x)
    (derivative_geom_polynomial_scaled (R := R) n)
  simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C,
    derivative_geom_eval] using h

/-- Multiplying the actual derivative identity by `x` gives the weighted one. -/
theorem weighted_geom_scaled (x : R) (n : Nat) :
    (1 - x) ^ 2 * (∑ k ∈ Ico 1 (n + 1), (k : R) * x ^ k) =
      x * (1 - (n + 1 : R) * x ^ n + (n : R) * x ^ (n + 1)) := by
  rw [weighted_derivative, derivative_geom_eval]
  calc
    (1 - x) ^ 2 * (x * ∑ j ∈ range n, (j + 1 : R) * x ^ j) =
        x * ((1 - x) ^ 2 * ∑ j ∈ range n, (j + 1 : R) * x ^ j) := by ring
    _ = x * (1 - (n + 1 : R) * x ^ n + (n : R) * x ^ (n + 1)) := by
      rw [derivative_geom_scaled]

end Geometric

section GeometricField

variable {R : Type u} [Field R]

/-- Division is used only away from `x=1`. -/
theorem geom_closed (x : R) (n : Nat) (hx : x ≠ 1) :
    (∑ k ∈ range (n + 1), x ^ k) = (1 - x ^ (n + 1)) / (1 - x) := by
  apply (eq_div_iff (sub_ne_zero.mpr hx.symm)).2
  simpa only [mul_comm] using geom_scaled x n

/-- The weighted quotient requires the same explicit nonzero denominator. -/
theorem weighted_geom_closed (x : R) (n : Nat) (hx : x ≠ 1) :
    (∑ k ∈ Ico 1 (n + 1), (k : R) * x ^ k) =
      x * (1 - (n + 1 : R) * x ^ n + (n : R) * x ^ (n + 1)) / (1 - x) ^ 2 := by
  apply (eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr hx.symm))).2
  simpa only [mul_comm] using weighted_geom_scaled x n

end GeometricField

/-- Casting the finite natural sum preserves its summands and positive interval. -/
theorem weighted_two_cast (n : Nat) :
    ((∑ k ∈ Ico 1 (n + 1), k * 2 ^ k : Nat) : ℚ) =
      ∑ k ∈ Ico 1 (n + 1), (k : ℚ) * (2 : ℚ) ^ k := by
  simp

/-- The exact natural identity is subtraction-free and includes `n=0`. -/
theorem weighted_two_identity (n : Nat) :
    (∑ k ∈ Ico 1 (n + 1), k * 2 ^ k) + 2 ^ (n + 1) = n * 2 ^ (n + 1) + 2 := by
  have hq : ((∑ k ∈ Ico 1 (n + 1), k * 2 ^ k : Nat) : ℚ) + (2 : ℚ) ^ (n + 1) =
      (n : ℚ) * (2 : ℚ) ^ (n + 1) + 2 := by
    rw [weighted_two_cast]
    have h := weighted_geom_scaled (2 : ℚ) n
    norm_num at h
    simp only [pow_succ] at h ⊢
    nlinarith [h]
  exact_mod_cast hq

/-- Both exponential comparisons hold at every index, including zero. -/
theorem weighted_two_bounds (n : Nat) :
    n * 2 ^ n ≤ (∑ k ∈ Ico 1 (n + 1), k * 2 ^ k) ∧
      (∑ k ∈ Ico 1 (n + 1), k * 2 ^ k) ≤ 2 * (n * 2 ^ n) := by
  constructor
  · cases n with
    | zero => simp
    | succ n =>
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
        omega
  · have h := weighted_two_identity n
    have hp : 1 ≤ (2 : Nat) ^ n := Nat.one_le_pow n 2 (by decide)
    simp only [pow_succ] at h
    nlinarith [h]


/-- Each half-series summand is the corresponding weighted geometric summand. -/
theorem half_sum_eq_weighted_geom (n : Nat) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) / (2 : ℚ) ^ k) =
      ∑ k ∈ Ico 1 (n + 1), (k : ℚ) * (1 / 2 : ℚ) ^ k := by
  apply Finset.sum_congr rfl
  intro k _
  simp [div_eq_mul_inv]

/-- Specialize the actual weighted polynomial identity and clear its positive power. -/
theorem half_sum_scaled (n : Nat) :
    (2 : ℚ) ^ n * (∑ k ∈ Ico 1 (n + 1), (k : ℚ) / (2 : ℚ) ^ k) + (n + 2 : ℚ) =
      (2 : ℚ) ^ (n + 1) := by
  have hpow : (1 / 2 : ℚ) ^ n * (2 : ℚ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have h := weighted_geom_scaled (1 / 2 : ℚ) n
  rw [← half_sum_eq_weighted_geom n] at h
  norm_num at h
  simp only [pow_succ] at h ⊢
  linear_combination (4 * (2 : ℚ) ^ n) * h - ((n : ℚ) + 2) * hpow

/-- The finite sum has an exact rational remainder at every index. -/
theorem half_sum_closed (n : Nat) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) / (2 : ℚ) ^ k) =
      2 - (n + 2 : ℚ) / (2 : ℚ) ^ n := by
  have h := half_sum_scaled n
  rw [pow_succ] at h
  have hp : (2 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hr : (n + 2 : ℚ) / (2 : ℚ) ^ n =
      2 - (∑ k ∈ Ico 1 (n + 1), (k : ℚ) / (2 : ℚ) ^ k) := by
    apply (div_eq_iff hp).2
    nlinarith [h]
  linarith

/-- Sum and exact remainder add to the limiting value, including at zero. -/
theorem half_sum_add_remainder (n : Nat) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) / (2 : ℚ) ^ k) +
      (n + 2 : ℚ) / (2 : ℚ) ^ n = 2 := by
  rw [half_sum_closed]
  ring

theorem half_remainder_pos (n : Nat) :
    0 < (n + 2 : ℚ) / (2 : ℚ) ^ n := by
  exact div_pos (by positivity) (pow_pos (by norm_num) n)

theorem half_sum_nonnegative (n : Nat) :
    0 ≤ ∑ k ∈ Ico 1 (n + 1), (k : ℚ) / (2 : ℚ) ^ k := by
  apply Finset.sum_nonneg
  intro k _
  exact div_nonneg (Nat.cast_nonneg k) (le_of_lt (pow_pos (by norm_num) k))

theorem half_sum_lt_two (n : Nat) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) / (2 : ℚ) ^ k) < 2 := by
  have h := half_sum_add_remainder n
  have hp := half_remainder_pos n
  linarith

/-- The successor term is nonnegative, so every positive partial sum increases. -/
theorem half_sum_step (n : Nat) :
    (∑ k ∈ Ico 1 (n + 1), (k : ℚ) / (2 : ℚ) ^ k) ≤
      ∑ k ∈ Ico 1 (n + 1 + 1), (k : ℚ) / (2 : ℚ) ^ k := by
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
  exact le_add_of_nonneg_right
    (div_nonneg (by positivity) (le_of_lt (pow_pos (by norm_num) (n + 1))))

theorem half_sum_mono :
    Monotone (fun n : Nat => ∑ k ∈ Ico 1 (n + 1), (k : ℚ) / (2 : ℚ) ^ k) :=
  monotone_nat_of_le_succ half_sum_step

/-- The exact error decreases at every later index, not only on an even subsequence. -/
theorem half_remainder_antitone :
    Antitone (fun n : Nat => (n + 2 : ℚ) / (2 : ℚ) ^ n) := by
  intro n m hnm
  have hm := half_sum_mono hnm
  have hn := half_sum_add_remainder n
  have hms := half_sum_add_remainder m
  linarith

/-- A finite power bound supplies the quantitative modulus. -/
theorem square_le_even_power (k : Nat) :
    (k + 1) * (k + 1) ≤ 2 ^ (2 * k) := by
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have hm := Nat.mul_le_mul hk hk
  simpa only [two_mul, pow_add] using hm

/-- Choose the parameter once from the precision; the strict bound covers every later index. -/
theorem half_remainder_lt (ε : ℚ) (hε : 0 < ε) (k : Nat)
    (hk : 2 < ε * (k + 1 : ℚ)) (n : Nat) (hn : 2 * k ≤ n) :
    0 < (n + 2 : ℚ) / (2 : ℚ) ^ n ∧
      (n + 2 : ℚ) / (2 : ℚ) ^ n < ε := by
  have hpow : (k + 1 : ℚ) * (k + 1 : ℚ) ≤ (2 : ℚ) ^ (2 * k) := by
    exact_mod_cast square_le_even_power k
  have hkp : (0 : ℚ) < k + 1 := by positivity
  have hm := mul_lt_mul_of_pos_right hk hkp
  have hu := mul_le_mul_of_nonneg_left hpow (le_of_lt hε)
  have hb : ((2 * k : Nat) + 2 : ℚ) / (2 : ℚ) ^ (2 * k) < ε := by
    apply (div_lt_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) (2 * k))).2
    push_cast
    nlinarith [hm, hu]
  exact ⟨half_remainder_pos n, lt_of_le_of_lt (half_remainder_antitone hn) hb⟩

/-- The source ceiling/natural-absolute-value witness supplies a strict finite precision bound. -/
theorem half_sum_ceiling_modulus (ε : ℚ) (hε : 0 < ε) (n : Nat)
    (hn : 2 * ((⌈(2 / ε : ℚ)⌉ : ℤ).natAbs + 1) ≤ n) :
    (0 < (n + 2 : ℚ) / (2 : ℚ) ^ n ∧
      (n + 2 : ℚ) / (2 : ℚ) ^ n < ε) ∧
    (2 - ε < (∑ k ∈ Ico 1 (n + 1), (k : ℚ) / (2 : ℚ) ^ k) ∧
      (∑ k ∈ Ico 1 (n + 1), (k : ℚ) / (2 : ℚ) ^ k) < 2 + ε) := by
  let k : Nat := (⌈(2 / ε : ℚ)⌉ : ℤ).natAbs + 1
  have hc : (2 / ε : ℚ) ≤ (⌈(2 / ε : ℚ)⌉ : ℚ) := Int.le_ceil _
  have ha : (⌈(2 / ε : ℚ)⌉ : ℚ) ≤ ((⌈(2 / ε : ℚ)⌉ : ℤ).natAbs : ℚ) := by
    simpa only [Int.cast_natCast] using
      ((Int.cast_le (R := ℚ)).mpr (Int.le_natAbs (a := (⌈(2 / ε : ℚ)⌉ : ℤ))))
  have hbig : (2 / ε : ℚ) < (k + 1 : ℚ) := by
    dsimp [k]
    push_cast
    linarith
  have hk : 2 < ε * (k + 1 : ℚ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hbig
  have hr := half_remainder_lt ε hε k hk n hn
  have hs := half_sum_add_remainder n
  have hu := half_sum_lt_two n
  exact ⟨hr, by linarith [hr.2], by linarith⟩

/-- Standard rational convergence has exactly the arbitrary-sequence rational epsilon meaning. -/
theorem tendsto_rat_iff_epsilon (f : Nat → ℚ) (a : ℚ) :
    Filter.Tendsto f Filter.atTop (nhds a) ↔
      ∀ ε : ℚ, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n →
        a - ε < f n ∧ f n < a + ε := by
  constructor
  · intro h ε hε
    have hl := (tendsto_order.mp h).1 (a - ε) (by linarith)
    have hu := (tendsto_order.mp h).2 (a + ε) (by linarith)
    exact Filter.eventually_atTop.mp (hl.and hu)
  · intro h
    apply tendsto_order.mpr
    constructor
    · intro b hb
      obtain ⟨N, hN⟩ := h (a - b) (sub_pos.mpr hb)
      apply Filter.eventually_atTop.mpr
      refine ⟨N, fun n hn => ?_⟩
      have hl := (hN n hn).1
      linarith
    · intro b hb
      obtain ⟨N, hN⟩ := h (b - a) (sub_pos.mpr hb)
      apply Filter.eventually_atTop.mpr
      refine ⟨N, fun n hn => ?_⟩
      have hu := (hN n hn).2
      linarith

/-- The rational limit follows from the explicit all-later-index modulus; no completeness is used. -/
theorem half_sum_tendsto :
    Filter.Tendsto
      (fun n : Nat => ∑ k ∈ Ico 1 (n + 1), (k : ℚ) / (2 : ℚ) ^ k)
      Filter.atTop (nhds (2 : ℚ)) := by
  apply (tendsto_rat_iff_epsilon _ 2).2
  intro ε hε
  refine ⟨2 * ((⌈(2 / ε : ℚ)⌉ : ℤ).natAbs + 1), ?_⟩
  intro n hn
  exact (half_sum_ceiling_modulus ε hε n hn).2

end SquareKit.FiniteSums
