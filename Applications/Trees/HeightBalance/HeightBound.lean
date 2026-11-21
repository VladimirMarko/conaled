import Applications.Trees.HeightBalance.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum.Basic

/-!
# Logarithmic height at a fixed balance tolerance

Every block of `d + 1` height levels forces both children to contribute to an
exponential lower bound on external leaves. Ceiling rounding gives a bound
without an additive constant, including the empty tree. Pure shape results
allow every natural tolerance, including zero. Stored-height consequences
add correctness of the complete supplied annotation.
Source correspondence: `docs/research/fdsa-height-bound.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.HeightBalance
universe u v
variable {α : Type u} {σ : Type v}

/-- Strictly exceeding `k` height blocks forces at least `2^(k+1)` leaves. -/
theorem two_pow_succ_le_numLeaves_of_mul_lt_height
    (d k : Nat) (t : BinaryTree α) (h : BalancedD d t)
    (hk : k * (d + 1) < t.height) :
    2 ^ (k + 1) ≤ t.numLeaves := by
  induction k generalizing t with
  | zero =>
      cases t with
      | nil =>
          simp only [BinaryTree.height, Nat.zero_mul] at hk
          omega
      | node a l r =>
          change 2 ≤ l.numLeaves + r.numLeaves
          have hl := BinaryTree.numLeaves_pos l
          have hr := BinaryTree.numLeaves_pos r
          omega
  | succ k ih =>
      cases t with
      | nil =>
          simp only [BinaryTree.height] at hk
          omega
      | node a l r =>
          rcases (balancedD_node d a l r).mp h with ⟨hl, hr, hlr, hrl⟩
          have leftHeight : max l.height r.height + 1 ≤ l.height + (d + 1) := by
            omega
          have rightHeight : max l.height r.height + 1 ≤ r.height + (d + 1) := by
            omega
          rw [Nat.succ_mul] at hk
          change k * (d + 1) + (d + 1) < max l.height r.height + 1 at hk
          have leftLower := ih l hl (by omega : k * (d + 1) < l.height)
          have rightLower := ih r hr (by omega : k * (d + 1) < r.height)
          change 2 ^ ((k + 1) + 1) ≤ l.numLeaves + r.numLeaves
          rw [Nat.pow_add_one']
          omega

/-- Rounding upward by a positive block size covers the original height. -/
private theorem height_le_mul_ceil (n d : Nat) :
    n ≤ (d + 1) * ((n + d) / (d + 1)) := by
  have remainder : (n + d) % (d + 1) < d + 1 :=
    Nat.mod_lt (n + d) (by omega)
  have decomposition := Nat.mod_add_div (n + d) (d + 1)
  omega

/-- The ceiling exponent, rather than the floor, supports the zero-additive log bound. -/
theorem two_pow_ceil_height_le_numLeaves
    (d : Nat) (t : BinaryTree α) (h : BalancedD d t) :
    2 ^ ((t.height + d) / (d + 1)) ≤ t.numLeaves := by
  cases quotient : (t.height + d) / (d + 1) with
  | zero =>
      change 1 ≤ t.numLeaves
      exact Nat.succ_le_of_lt (BinaryTree.numLeaves_pos t)
  | succ k =>
      apply two_pow_succ_le_numLeaves_of_mul_lt_height d k t h
      have decomposition := Nat.mod_add_div (t.height + d) (d + 1)
      rw [quotient, Nat.mul_succ, Nat.mul_comm (d + 1) k] at decomposition
      omega

/-- Integer logarithmic height for every natural tolerance, including zero.
Only actual shape balance is used; the payload has no additional assumptions. -/
theorem height_le_mul_clog_numLeaves
    (d : Nat) (t : BinaryTree α) (h : BalancedD d t) :
    t.height ≤ (d + 1) * Nat.clog 2 t.numLeaves := by
  have exponent : (t.height + d) / (d + 1) ≤ Nat.clog 2 t.numLeaves :=
    (Nat.le_log_of_pow_le (by decide : 1 < 2)
      (two_pow_ceil_height_le_numLeaves d t h)).trans (Nat.log_le_clog 2 t.numLeaves)
  exact (height_le_mul_ceil t.height d).trans (Nat.mul_le_mul_left (d + 1) exponent)

theorem height_le_mul_clog_numNodes_add_one
    (d : Nat) (t : BinaryTree α) (h : BalancedD d t) :
    t.height ≤ (d + 1) * Nat.clog 2 (t.numNodes + 1) := by
  simpa only [BinaryTree.numLeaves_eq_numNodes_succ] using
    height_le_mul_clog_numLeaves d t h

/-- Actual height is logarithmic in external leaves for each fixed natural tolerance. -/
theorem height_le_mul_logb_numLeaves
    (d : Nat) (t : BinaryTree α) (h : BalancedD d t) :
    (t.height : ℝ) ≤ ((d : ℝ) + 1) * Real.logb 2 (t.numLeaves : ℝ) := by
  let k := (t.height + d) / (d + 1)
  have powerNat : 2 ^ k ≤ t.numLeaves := two_pow_ceil_height_le_numLeaves d t h
  have powerReal : (2 : ℝ) ^ k ≤ (t.numLeaves : ℝ) := by
    have castPower : ((2 ^ k : Nat) : ℝ) ≤ (t.numLeaves : ℝ) :=
      Nat.cast_le.mpr powerNat
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using castPower
  have base : (1 : ℝ) < 2 := by norm_num
  have leaves : (0 : ℝ) < (t.numLeaves : ℝ) :=
    Nat.cast_pos.mpr (BinaryTree.numLeaves_pos t)
  have logBound := (Real.logb_le_logb base
    (pow_pos (by norm_num : (0 : ℝ) < 2) k) leaves).mpr powerReal
  rw [Real.logb_pow, Real.logb_self_eq_one base, mul_one] at logBound
  have roundingReal : (t.height : ℝ) ≤ ((d : ℝ) + 1) * (k : ℝ) := by
    have castRounding : (t.height : ℝ) ≤ (((d + 1) * k : Nat) : ℝ) :=
      Nat.cast_le.mpr (height_le_mul_ceil t.height d)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using castRounding
  exact roundingReal.trans (mul_le_mul_of_nonneg_left logBound
    (add_nonneg (Nat.cast_nonneg d) zero_le_one))

/-- Internal-node size enters the logarithm after adding one, also at nil. -/
theorem height_le_mul_logb_numNodes_add_one
    (d : Nat) (t : BinaryTree α) (h : BalancedD d t) :
    (t.height : ℝ) ≤ ((d : ℝ) + 1) * Real.logb 2 ((t.numNodes : ℝ) + 1) := by
  simpa only [BinaryTree.numLeaves_eq_numNodes_succ, Nat.cast_add, Nat.cast_one] using
    height_le_mul_logb_numLeaves d t h

/-- Erasure forgets annotations without changing height or external-leaf count. -/
theorem two_pow_ceil_height_le_numLeaves_of_valid
    (ann : HeightAnnotation α σ) (d : Nat) (t : BinaryTree (α × σ))
    (h : ValidD ann d t) :
    2 ^ ((t.height + d) / (d + 1)) ≤ t.numLeaves := by
  simpa only [Cached.height_erase, Cached.numLeaves_erase] using
    two_pow_ceil_height_le_numLeaves d (Cached.erase t) h.1

theorem height_le_mul_logb_numLeaves_of_valid
    (ann : HeightAnnotation α σ) (d : Nat) (t : BinaryTree (α × σ))
    (h : ValidD ann d t) :
    (t.height : ℝ) ≤ ((d : ℝ) + 1) * Real.logb 2 (t.numLeaves : ℝ) := by
  simpa only [Cached.height_erase, Cached.numLeaves_erase] using
    height_le_mul_logb_numLeaves d (Cached.erase t) h.1

theorem height_le_mul_logb_numNodes_add_one_of_valid
    (ann : HeightAnnotation α σ) (d : Nat) (t : BinaryTree (α × σ))
    (h : ValidD ann d t) :
    (t.height : ℝ) ≤ ((d : ℝ) + 1) * Real.logb 2 ((t.numNodes : ℝ) + 1) := by
  simpa only [Cached.height_erase, Cached.numNodes_erase] using
    height_le_mul_logb_numNodes_add_one d (Cached.erase t) h.1

/-- Replacing actual height by the stored projection requires the complete cache invariant. -/
theorem two_pow_ceil_ht_le_numLeaves
    (ann : HeightAnnotation α σ) (d : Nat) (t : BinaryTree (α × σ))
    (h : ValidD ann d t) :
    2 ^ ((ht ann t + d) / (d + 1)) ≤ t.numLeaves := by
  rw [ht_eq_height ann d t h]
  exact two_pow_ceil_height_le_numLeaves_of_valid ann d t h

theorem ht_le_mul_logb_numLeaves
    (ann : HeightAnnotation α σ) (d : Nat) (t : BinaryTree (α × σ))
    (h : ValidD ann d t) :
    (ht ann t : ℝ) ≤ ((d : ℝ) + 1) * Real.logb 2 (t.numLeaves : ℝ) := by
  rw [ht_eq_height ann d t h]
  exact height_le_mul_logb_numLeaves_of_valid ann d t h

theorem ht_le_mul_logb_numNodes_add_one
    (ann : HeightAnnotation α σ) (d : Nat) (t : BinaryTree (α × σ))
    (h : ValidD ann d t) :
    (ht ann t : ℝ) ≤ ((d : ℝ) + 1) * Real.logb 2 ((t.numNodes : ℝ) + 1) := by
  rw [ht_eq_height ann d t h]
  exact height_le_mul_logb_numNodes_add_one_of_valid ann d t h

end Trees.HeightBalance
