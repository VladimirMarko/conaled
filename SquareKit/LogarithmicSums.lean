import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Factorial logarithms and finite half intervals

These estimates use the native natural factorial and floor logarithm. Halving
is natural floor division, including odd inputs. They are finite mathematical
bounds; occurrence-count and asymptotic clients belong to their existing owners.
-/
set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace SquareKit.LogarithmicSums

open Finset

/-- The native logarithm halves its input once the input is at least two. -/
theorem log2_half (n : ℕ) (hn : 2 ≤ n) :
    n.log2 = (n / 2).log2 + 1 := by
  rw [Nat.log2_def, ite_eq_left hn]

/-- The three comparisons needed on the upper half of a natural interval. -/
theorem half_scale_bounds (n : ℕ) (hn : 4 ≤ n) :
    n ≤ 3 * (n / 2) ∧ n.log2 ≤ 2 * (n / 2).log2 ∧ 1 ≤ (n / 2).log2 := by
  have hh : 2 ≤ n / 2 := by omega
  have hl : 1 ≤ (n / 2).log2 :=
    (Nat.le_log2 (by omega : n / 2 ≠ 0)).mpr (by simpa only [Nat.pow_one] using hh)
  have he := log2_half n (by omega)
  omega

/-- The factorial contains a block long enough for this half-power, even at zero. -/
theorem factorial_half_power_lower (n : ℕ) :
    (n / 2) ^ (n / 2) ≤ Nat.factorial n := by
  let m := n / 2
  have hmn : m + m ≤ n := by dsimp [m]; omega
  have hf : 1 ≤ Nat.factorial m := Nat.succ_le_iff.mpr (Nat.factorial_pos m)
  calc
    (n / 2) ^ (n / 2) = m ^ m := rfl
    _ ≤ (m + 1) ^ m := Nat.pow_le_pow_left (Nat.le_succ m) m
    _ ≤ Nat.factorial m * (m + 1) ^ m := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right ((m + 1) ^ m) hf
    _ ≤ Nat.factorial (m + m) := Nat.factorial_mul_pow_le_factorial
    _ ≤ Nat.factorial n := Nat.factorial_le hmn

/-- A positive base supplies the lower logarithmic power bound. -/
theorem log2_power_lower (a k : ℕ) (ha : 1 ≤ a) :
    k * a.log2 ≤ (a ^ k).log2 := by
  have ha0 : a ≠ 0 := by omega
  have hpos : a ^ k ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (by omega : 0 < a))
  apply (Nat.le_log2 hpos).mpr
  calc
    2 ^ (k * a.log2) = (2 ^ a.log2) ^ k := by
      rw [Nat.mul_comm k, Nat.pow_mul]
    _ ≤ a ^ k := Nat.pow_le_pow_left (Nat.log2_self_le ha0) k

/-- The upper bound also covers zero bases and the native value `0 ^ 0 = 1`. -/
theorem log2_power_upper (a k : ℕ) :
    (a ^ k).log2 ≤ k * (a.log2 + 1) := by
  have ha : a ≤ 2 ^ (a.log2 + 1) := Nat.le_of_lt Nat.lt_log2_self
  have hp := Nat.pow_le_pow_left ha k
  have hm : (a ^ k).log2 ≤ ((2 ^ (a.log2 + 1)) ^ k).log2 := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hp
  calc
    (a ^ k).log2 ≤ ((2 ^ (a.log2 + 1)) ^ k).log2 := hm
    _ = k * (a.log2 + 1) := by
      rw [← Nat.pow_mul, Nat.log2_two_pow, Nat.mul_comm]

/-- Finite product bounds give both factorial-log comparisons from index four. -/
theorem factorial_log2_bounds (n : ℕ) (hn : 4 ≤ n) :
    n * n.log2 ≤ 6 * (Nat.factorial n).log2 ∧
      (Nat.factorial n).log2 ≤ 2 * (n * n.log2) := by
  rcases half_scale_bounds n hn with ⟨hhalf, hloghalf, _⟩
  have hp := log2_power_lower (n / 2) (n / 2) (by omega)
  have hf : ((n / 2) ^ (n / 2)).log2 ≤ (Nat.factorial n).log2 := by
    simpa only [Nat.log2_eq_log_two] using
      Nat.log_mono_right (b := 2) (factorial_half_power_lower n)
  have hlower : (n / 2) * (n / 2).log2 ≤ (Nat.factorial n).log2 := hp.trans hf
  have hupper : (Nat.factorial n).log2 ≤ (n ^ n).log2 := by
    simpa only [Nat.log2_eq_log_two] using
      Nat.log_mono_right (b := 2) (Nat.factorial_le_pow n)
  have hlog : 1 ≤ n.log2 :=
    (Nat.le_log2 (by omega : n ≠ 0)).mpr
      (by simpa only [Nat.pow_one] using (show 2 ≤ n by omega))
  constructor
  · calc
      n * n.log2 ≤ (3 * (n / 2)) * (2 * (n / 2).log2) :=
        Nat.mul_le_mul hhalf hloghalf
      _ = 6 * ((n / 2) * (n / 2).log2) := by ring
      _ ≤ 6 * (Nat.factorial n).log2 := Nat.mul_le_mul_left 6 hlower
  · calc
      (Nat.factorial n).log2 ≤ (n ^ n).log2 := hupper
      _ ≤ n * (n.log2 + 1) := log2_power_upper n n
      _ ≤ n * (2 * n.log2) := Nat.mul_le_mul_left n (by omega)
      _ = 2 * (n * n.log2) := by ring

/-- A constant bound on the positive indices accounts for exactly `n` terms. -/
theorem sum_Ico_one_le_constant (f : ℕ → ℕ) (n B : ℕ)
    (h : ∀ k, 1 ≤ k → k ≤ n → f k ≤ B) :
    (∑ k ∈ Ico 1 (n + 1), f k) ≤ n * B := by
  have hcard : (Ico 1 (n + 1)).card = n := by
    rw [Nat.card_Ico]
    omega
  have hb := Finset.sum_le_card_nsmul (Ico 1 (n + 1)) f B (by
    intro k hk
    rcases Finset.mem_Ico.mp hk with ⟨hlo, hhi⟩
    exact h k hlo (by omega))
  simpa only [hcard, Nat.nsmul_eq_mul] using hb

/-- Enlarging the positive interval preserves a sum of natural-valued terms. -/
theorem sum_Ico_one_mono (f : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    (∑ k ∈ Ico 1 (m + 1), f k) ≤ ∑ k ∈ Ico 1 (n + 1), f k := by
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rcases Finset.mem_Ico.mp hk with ⟨hlo, hhi⟩
  exact Finset.mem_Ico.mpr ⟨hlo, by omega⟩

/-- The shifted block contributes `k * B` in addition to the existing prefix. -/
theorem sum_Ico_one_lower_block (f : ℕ → ℕ) (m k B : ℕ)
    (h : ∀ i, 1 ≤ i → i ≤ k → B ≤ f (m + i)) :
    (∑ j ∈ Ico 1 (m + 1), f j) + k * B ≤
      ∑ j ∈ Ico 1 (m + k + 1), f j := by
  have hcard : (Ico (m + 1) (m + k + 1)).card = k := by
    rw [Nat.card_Ico]
    omega
  have hb := Finset.card_nsmul_le_sum (Ico (m + 1) (m + k + 1)) f B (by
    intro j hj
    rcases Finset.mem_Ico.mp hj with ⟨hlo, hhi⟩
    have he : m + (j - m) = j := by omega
    simpa only [he] using h (j - m) (by omega) (by omega))
  have hblock : k * B ≤ ∑ j ∈ Ico (m + 1) (m + k + 1), f j := by
    simpa only [hcard, Nat.nsmul_eq_mul] using hb
  calc
    (∑ j ∈ Ico 1 (m + 1), f j) + k * B ≤
        (∑ j ∈ Ico 1 (m + 1), f j) +
          ∑ j ∈ Ico (m + 1) (m + k + 1), f j := Nat.add_le_add_left hblock _
    _ = ∑ j ∈ Ico 1 (m + k + 1), f j :=
      Finset.sum_Ico_consecutive f (by omega) (by omega)

/-- Every weighted term is bounded by the last weighted term, including at zero. -/
theorem weighted_log_upper (n : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), k * k.log2) ≤ n * n * n.log2 := by
  have hb := sum_Ico_one_le_constant (fun k => k * k.log2) n (n * n.log2) (by
    intro k _ hkn
    have hl : k.log2 ≤ n.log2 := by
      simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hkn
    exact Nat.mul_le_mul hkn hl)
  simpa only [Nat.mul_assoc] using hb

/-- The upper half contains `n / 2` terms, each at least the half-scale weight. -/
theorem weighted_log_half_lower (n : ℕ) :
    (n / 2) * (n / 2) * (n / 2).log2 ≤
      ∑ k ∈ Ico 1 (n + 1), k * k.log2 := by
  let m := n / 2
  have hb := sum_Ico_one_lower_block (fun k => k * k.log2) m m (m * m.log2) (by
    intro i _ _
    have hmi : m ≤ m + i := by omega
    have hl : m.log2 ≤ (m + i).log2 := by
      simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hmi
    exact Nat.mul_le_mul hmi hl)
  calc
    (n / 2) * (n / 2) * (n / 2).log2 = m * (m * m.log2) := by
      dsimp [m]
      rw [Nat.mul_assoc]
    _ ≤ (∑ k ∈ Ico 1 (m + 1), k * k.log2) + m * (m * m.log2) := by omega
    _ ≤ ∑ k ∈ Ico 1 (m + m + 1), k * k.log2 := hb
    _ ≤ ∑ k ∈ Ico 1 (n + 1), k * k.log2 :=
      sum_Ico_one_mono (fun k => k * k.log2) (by dsimp [m]; omega)

/-- The finite weighted logarithmic sum has constants eighteen and one from four. -/
theorem weighted_log_bounds (n : ℕ) (hn : 4 ≤ n) :
    n * n * n.log2 ≤ 18 * (∑ k ∈ Ico 1 (n + 1), k * k.log2) ∧
      (∑ k ∈ Ico 1 (n + 1), k * k.log2) ≤ n * n * n.log2 := by
  rcases half_scale_bounds n hn with ⟨hhalf, hloghalf, _⟩
  constructor
  · calc
      n * n * n.log2 ≤
          (3 * (n / 2)) * (3 * (n / 2)) * (2 * (n / 2).log2) :=
        Nat.mul_le_mul (Nat.mul_le_mul hhalf hhalf) hloghalf
      _ = 18 * ((n / 2) * (n / 2) * (n / 2).log2) := by ring
      _ ≤ 18 * (∑ k ∈ Ico 1 (n + 1), k * k.log2) :=
        Nat.mul_le_mul_left 18 (weighted_log_half_lower n)
  · exact weighted_log_upper n

/-! Connected boundary specializations; canonical occurrence-count cases are clients. -/

example : 5 ≤ 3 * (5 / 2) ∧ (5 : ℕ).log2 ≤ 2 * (5 / 2 : ℕ).log2 ∧
    1 ≤ (5 / 2 : ℕ).log2 :=
  half_scale_bounds 5 (by decide)

example : (0 / 2 : ℕ) ^ (0 / 2) ≤ Nat.factorial 0 :=
  factorial_half_power_lower 0

example : (1 / 2 : ℕ) ^ (1 / 2) ≤ Nat.factorial 1 :=
  factorial_half_power_lower 1

example : ((0 : ℕ) ^ 0).log2 ≤ 0 * ((0 : ℕ).log2 + 1) :=
  log2_power_upper 0 0

example : ((0 : ℕ) ^ 3).log2 ≤ 3 * ((0 : ℕ).log2 + 1) :=
  log2_power_upper 0 3

example (n : ℕ) : Nat.factorial n ≤ Nat.factorial (n + 1) :=
  Nat.factorial_le (Nat.le_succ n)

/-! Positive-index and zero-weight boundaries remain connected to the general bounds. -/

example (n : ℕ) :
    (∑ k ∈ Ico 1 (n + 1), if k = 0 then 7 else 1) ≤ n := by
  have hb := sum_Ico_one_le_constant (fun k => if k = 0 then 7 else 1) n 1 (by
    intro k hk _
    have hk0 : k ≠ 0 := by omega
    simpa only [ite_eq_right hk0] using (Nat.le_refl 1))
  simpa only [Nat.mul_one] using hb

example (m k : ℕ) :
    (∑ _j ∈ Ico 1 (m + 1), (1 : ℕ)) + k ≤
      ∑ _j ∈ Ico 1 (m + k + 1), (1 : ℕ) := by
  have hb := sum_Ico_one_lower_block (fun _ => 1) m k 1 (by
    intro _ _ _
    exact Nat.le_refl 1)
  simpa only [Nat.mul_one] using hb

example : (∑ k ∈ Ico 1 ((0 : ℕ) + 1), k * k.log2) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa only [Nat.zero_mul] using weighted_log_upper 0

example : (∑ k ∈ Ico 1 ((1 : ℕ) + 1), k * k.log2) = 0 := by
  have hl : (1 : ℕ).log2 = 0 := by decide
  apply Nat.eq_zero_of_le_zero
  simpa only [hl, Nat.mul_zero] using weighted_log_upper 1

end SquareKit.LogarithmicSums
