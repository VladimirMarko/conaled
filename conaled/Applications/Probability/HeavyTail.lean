import Applications.Progress.Evaluation
import Mathlib.Probability.Distributions.Geometric
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Finite countdowns with infinite expected work

Draw `n` with probability `2⁻⁽ⁿ⁺¹⁾`, then decrement `2^n` to zero and return.
Every sample terminates in exactly `2^n + 1` atomic transitions, but their
expectation is infinite. Sampling the initial natural number is outside this
transition model; even without its cost, expected work is infinite.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityProgress.HeavyTail

/-- A decrement or return consumes one operational transition. -/
def countdown : Progress.Machine ℕ Unit
  | 0 => .inl ()
  | n + 1 => .inr n

theorem countdown_evaluates (n : ℕ) :
    Progress.Evaluates countdown n () (n + 1) := by
  induction n with
  | zero => exact .done rfl
  | succ n ih => exact .next rfl ih

noncomputable def fairHalf : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

/-- Failures before a fair success; the parameter is strictly positive. -/
noncomputable def sampleLaw : Measure ℕ := geometricMeasure fairHalf

instance : IsProbabilityMeasure sampleLaw := by unfold sampleLaw; infer_instance

theorem sample_evaluates (n : ℕ) :
    Progress.Evaluates countdown (2 ^ n) () (2 ^ n + 1) := countdown_evaluates _

theorem all_samples_terminate (n : ℕ) : Progress.Terminates countdown (2 ^ n) :=
  ⟨(), 2 ^ n + 1, sample_evaluates n⟩

/-- Operational uniqueness identifies the integrand with the transition count. -/
theorem actual_cost {n k : ℕ} {a : Unit}
    (h : Progress.Evaluates countdown (2 ^ n) a k) : k = 2 ^ n + 1 :=
  (h.unique (sample_evaluates n)).2

private theorem weighted_power (n : ℕ) :
    ((2 : ℝ≥0∞) ^ n) * sampleLaw {n} = ENNReal.ofReal (1 / 2) := by
  have hp : fairHalf ≠ 0 := by
    intro h
    have := congrArg (fun x : unitInterval => (x : ℝ)) h
    norm_num [fairHalf] at this
  rw [sampleLaw, geometricMeasure_singleton hp]
  change (2 : ℝ≥0∞) ^ n * ENNReal.ofReal ((1 - 1 / 2 : ℝ) ^ n * (1 / 2)) = _
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- Each power-of-two countdown contributes one half to the expected work. -/
theorem lintegral_cost_eq_top :
    ∫⁻ n, ((2 ^ n + 1 : ℕ) : ℝ≥0∞) ∂sampleLaw = ∞ := by
  have hpow : (∫⁻ n : ℕ, (2 : ℝ≥0∞) ^ n ∂sampleLaw) = ∞ := by
    rw [lintegral_countable']
    simp_rw [weighted_power]
    simp
  apply top_unique
  rw [← hpow]
  apply lintegral_mono
  intro n
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  exact le_self_add

/-- A checked specialization counts eight decrements and the final return. -/
theorem three_sample_evaluates : Progress.Evaluates countdown 8 () 9 := by
  simpa using sample_evaluates 3

/-- No single transition budget covers all the terminating samples. -/
theorem costs_unbounded (budget : ℕ) :
    ∃ n, ∀ a k, Progress.Evaluates countdown (2 ^ n) a k → budget < k := by
  refine ⟨budget, ?_⟩
  intro a k h
  rw [actual_cost h]
  exact lt_trans (Nat.lt_two_pow_self (n := budget)) (Nat.lt_succ_self _)

end ProbabilityProgress.HeavyTail
