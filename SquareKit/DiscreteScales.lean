import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite comparisons of natural logarithmic and square-root scales

The number functions and their basic brackets are native. The finite comparisons
retain their source thresholds; exact even-power roots include exponent zero.
These are mathematical estimates, with no execution-cost interpretation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.DiscreteScales

/-- From four onward, powers of two dominate the natural square. -/
theorem square_le_two_pow {k : ℕ} (hk : 4 ≤ k) : k * k ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk4 : 4 ≤ k
    · have hs : (k + 1) * (k + 1) ≤ 2 * (k * k) := by
        have hp : 3 * k ≤ k * k := Nat.mul_le_mul_right k (by omega)
        grind
      have hm := Nat.mul_le_mul_left 2 (ih hk4)
      rw [Nat.pow_succ]
      grind
    · have he : k = 3 := by omega
      subst k
      decide

/-- The floor logarithm is bounded by the floor square root from sixteen onward. -/
theorem log2_le_sqrt {n : ℕ} (hn : 16 ≤ n) : Nat.log2 n ≤ Nat.sqrt n := by
  have hk : 4 ≤ Nat.log2 n :=
    (Nat.le_log2 (by omega : n ≠ 0)).mpr (by simpa using hn)
  exact Nat.le_sqrt.mpr
    ((square_le_two_pow hk).trans (Nat.log2_self_le (by omega : n ≠ 0)))

/-- An even power of two is an exact natural square, including exponent zero. -/
theorem sqrt_two_pow_even (k : ℕ) : Nat.sqrt (2 ^ (2 * k)) = 2 ^ k := by
  have he : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [he, Nat.sqrt_eq]

/-- The lower terms stay within three copies of the cubic term, also at zero. -/
theorem cubic_lower_terms_bounds (n : ℕ) :
    n * n * n ≤ n * n * n + n * n + n * Nat.log2 n ∧
      n * n * n + n * n + n * Nat.log2 n ≤ 3 * (n * n * n) := by
  have hlog := Nat.log2_le_self n
  have hmul := Nat.mul_le_mul_left n hlog
  have hsq : n * n ≤ n * n * n := by
    cases n with
    | zero => simp
    | succ n =>
      have h := Nat.mul_le_mul_left ((n + 1) * (n + 1)) (show 1 ≤ n + 1 by omega)
      simpa only [Nat.mul_one] using h
  constructor <;> omega

/-- A rational log band is bounded by twice the floor logarithm from two onward. -/
theorem logBand_bounds {l : ℕ → ℚ}
    (hl : ∀ n, 1 ≤ n → l n ∈ Set.Icc (Nat.log2 n : ℚ) ((Nat.log2 n : ℚ) + 1))
    {n : ℕ} (hn : 2 ≤ n) :
    (Nat.log2 n : ℚ) ≤ l n ∧ l n ≤ 2 * (Nat.log2 n : ℚ) := by
  have hb := hl n (by omega)
  have hk : 1 ≤ Nat.log2 n :=
    (Nat.le_log2 (by omega : n ≠ 0)).mpr (by simpa using hn)
  have hkq : (1 : ℚ) ≤ (Nat.log2 n : ℚ) := by exact_mod_cast hk
  exact ⟨hb.1, by linarith [hb.2]⟩

/-- A rational root band is bounded by twice the floor root at every positive index. -/
theorem rootBand_bounds {s : ℕ → ℚ}
    (hs : ∀ n, 1 ≤ n → s n ∈ Set.Icc (Nat.sqrt n : ℚ) ((Nat.sqrt n : ℚ) + 1))
    {n : ℕ} (hn : 1 ≤ n) :
    (Nat.sqrt n : ℚ) ≤ s n ∧ s n ≤ 2 * (Nat.sqrt n : ℚ) := by
  have hb := hs n hn
  have hk : 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by simpa using hn)
  have hkq : (1 : ℚ) ≤ (Nat.sqrt n : ℚ) := by exact_mod_cast hk
  exact ⟨hb.1, by linarith [hb.2]⟩

/-- The finite log/root comparison transports to arbitrary rational bands. -/
theorem mul_logBand_le_two_mul_rootBand {l s : ℕ → ℚ}
    (hl : ∀ n, 1 ≤ n → l n ∈ Set.Icc (Nat.log2 n : ℚ) ((Nat.log2 n : ℚ) + 1))
    (hs : ∀ n, 1 ≤ n → s n ∈ Set.Icc (Nat.sqrt n : ℚ) ((Nat.sqrt n : ℚ) + 1))
    {n : ℕ} (hn : 16 ≤ n) : (n : ℚ) * l n ≤ 2 * ((n : ℚ) * s n) := by
  have hlog := logBand_bounds hl (show 2 ≤ n by omega)
  have hroot := (hs n (by omega)).1
  have hcompare : (Nat.log2 n : ℚ) ≤ (Nat.sqrt n : ℚ) := by
    exact_mod_cast log2_le_sqrt hn
  calc
    (n : ℚ) * l n ≤ (n : ℚ) * (2 * (Nat.log2 n : ℚ)) :=
      mul_le_mul_of_nonneg_left hlog.2 (Nat.cast_nonneg n)
    _ ≤ (n : ℚ) * (2 * s n) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hcompare.trans hroot) (by norm_num))
        (Nat.cast_nonneg n)
    _ = 2 * ((n : ℚ) * s n) := by ring

/-- Every positive rational coefficient and threshold has a strict finite counterexample. -/
theorem sqrt_log2_counterexample (C : ℚ) (hC : 0 < C) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      C * ((Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ)) < (n : ℚ) + (Nat.sqrt n : ℚ) := by
  obtain ⟨k, hk4, hkN, hkq⟩ :
      ∃ k : ℕ, 4 ≤ k ∧ N ≤ k ∧ 2 * C < (k : ℚ) := by
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt (2 * C)
    refine ⟨max 4 (max N k₀), le_max_left _ _, ?_, ?_⟩
    · exact (le_max_left N k₀).trans (le_max_right 4 (max N k₀))
    · exact hk₀.trans_le ((Nat.cast_le (α := ℚ)).mpr
        ((le_max_right N k₀).trans (le_max_right 4 (max N k₀))))
  have hkpos : (0 : ℚ) < (k : ℚ) :=
    (mul_pos (by norm_num : (0 : ℚ) < 2) hC).trans hkq
  have htq : (0 : ℚ) < ((2 ^ k : ℕ) : ℚ) := Nat.cast_pos.mpr (Nat.two_pow_pos k)
  have hsquare : (k : ℚ) * (k : ℚ) ≤ ((2 ^ k : ℕ) : ℚ) := by
    simpa only [Nat.cast_mul] using
      ((Nat.cast_le (α := ℚ)).mpr (square_le_two_pow hk4))
  have hsmall : C * (2 * (k : ℚ)) < ((2 ^ k : ℕ) : ℚ) := calc
    C * (2 * (k : ℚ)) = (2 * C) * (k : ℚ) := by
      rw [← mul_assoc, mul_comm C (2 : ℚ)]
    _ < (k : ℚ) * (k : ℚ) := mul_lt_mul_of_pos_right hkq hkpos
    _ ≤ ((2 ^ k : ℕ) : ℚ) := hsquare
  have hlarge := mul_lt_mul_of_pos_left hsmall htq
  have hn : N ≤ 2 ^ (2 * k) := by
    have hkp : k < 2 ^ k := Nat.lt_two_pow_self
    have hpow : 2 ^ k ≤ 2 ^ (2 * k) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    exact hkN.trans ((Nat.le_of_lt hkp).trans hpow)
  have he : (2 : ℕ) ^ (2 * k) = 2 ^ k * 2 ^ k := by
    rw [← Nat.pow_add]
    congr 1
    omega
  refine ⟨2 ^ (2 * k), hn, ?_⟩
  rw [sqrt_two_pow_even, Nat.log2_two_pow, he]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    C * (((2 ^ k : ℕ) : ℚ) * (2 * (k : ℚ))) =
        ((2 ^ k : ℕ) : ℚ) * (C * (2 * (k : ℚ))) := mul_left_comm _ _ _
    _ < ((2 ^ k : ℕ) : ℚ) * ((2 ^ k : ℕ) : ℚ) := hlarge
    _ ≤ ((2 ^ k : ℕ) : ℚ) * ((2 ^ k : ℕ) : ℚ) + ((2 ^ k : ℕ) : ℚ) :=
      le_add_of_nonneg_right htq.le

/-- The strict counterfamily persists for every pair of admissible rational bands. -/
theorem band_counterexample {l s : ℕ → ℚ}
    (hl : ∀ n, 1 ≤ n → l n ∈ Set.Icc (Nat.log2 n : ℚ) ((Nat.log2 n : ℚ) + 1))
    (hs : ∀ n, 1 ≤ n → s n ∈ Set.Icc (Nat.sqrt n : ℚ) ((Nat.sqrt n : ℚ) + 1))
    (C : ℚ) (hC : 0 < C) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ C * (s n * l n) < (n : ℚ) + s n := by
  have hfourC : (0 : ℚ) < 4 * C := mul_pos (by norm_num : (0 : ℚ) < 4) hC
  have hcounter : ∃ n : ℕ, max N 2 ≤ n ∧
      (4 * C) * ((Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ)) <
        (n : ℚ) + (Nat.sqrt n : ℚ) :=
    sqrt_log2_counterexample (4 * C) hfourC (max N 2)
  obtain ⟨n, hn, hstrict⟩ := hcounter
  have hnN : N ≤ n := (le_max_left N 2).trans hn
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
  have hlog : (Nat.log2 n : ℚ) ≤ l n ∧ l n ≤ 2 * (Nat.log2 n : ℚ) :=
    logBand_bounds (l := l) hl (n := n) hn2
  have hroot : (Nat.sqrt n : ℚ) ≤ s n ∧ s n ≤ 2 * (Nat.sqrt n : ℚ) :=
    rootBand_bounds (s := s) hs (n := n) (show 1 ≤ n by omega)
  have hl0 : (0 : ℚ) ≤ l n := (Nat.cast_nonneg (Nat.log2 n)).trans hlog.1
  have htwoRoot : (0 : ℚ) ≤ 2 * (Nat.sqrt n : ℚ) :=
    mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) (Nat.cast_nonneg (Nat.sqrt n))
  have hfirst : s n * l n ≤ (2 * (Nat.sqrt n : ℚ)) * l n :=
    mul_le_mul_of_nonneg_right hroot.2 hl0
  have hsecond : (2 * (Nat.sqrt n : ℚ)) * l n ≤
      (2 * (Nat.sqrt n : ℚ)) * (2 * (Nat.log2 n : ℚ)) :=
    mul_le_mul_of_nonneg_left hlog.2 htwoRoot
  have hfour : (2 : ℚ) * 2 = 4 := by norm_num
  have hproductEq : (2 * (Nat.sqrt n : ℚ)) * (2 * (Nat.log2 n : ℚ)) =
      4 * ((Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ)) := calc
    (2 * (Nat.sqrt n : ℚ)) * (2 * (Nat.log2 n : ℚ)) =
        ((2 : ℚ) * 2) * ((Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ)) :=
      mul_mul_mul_comm (2 : ℚ) (Nat.sqrt n : ℚ) 2 (Nat.log2 n : ℚ)
    _ = 4 * ((Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ)) :=
      congrArg (fun c : ℚ => c * ((Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ))) hfour
  have hprod : s n * l n ≤ 4 * ((Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ)) :=
    hfirst.trans (hsecond.trans_eq hproductEq)
  have hscaled : C * (s n * l n) ≤
      C * (4 * ((Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ))) :=
    mul_le_mul_of_nonneg_left hprod hC.le
  have hscaleEq : C * (4 * ((Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ))) =
      (4 * C) * ((Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ)) := by
    rw [← mul_assoc, mul_comm C (4 : ℚ)]
  have htotal : (n : ℚ) + (Nat.sqrt n : ℚ) ≤ (n : ℚ) + s n :=
    add_le_add (le_refl (n : ℚ)) hroot.1
  refine ⟨n, hnN, ?_⟩
  calc
    C * (s n * l n) ≤ C * (4 * ((Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ))) := hscaled
    _ = (4 * C) * ((Nat.sqrt n : ℚ) * (Nat.log2 n : ℚ)) := hscaleEq
    _ < (n : ℚ) + (Nat.sqrt n : ℚ) := hstrict
    _ ≤ (n : ℚ) + s n := htotal

end SquareKit.DiscreteScales
