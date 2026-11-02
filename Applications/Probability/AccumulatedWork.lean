import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Accumulated nonnegative work under integrated drift

The observations share one supplied measure. A one-step inequality between
their lower integrals yields geometric bounds on the means and on remaining
work. A separate almost-everywhere bound on the actual prefix yields an
excess-work tail bound. No independence or probability normalization is used.

The observations and their sum retain extended nonnegative values, including
infinity. Strict contraction and a finite initial bound establish a finite
integral; they do not establish that an execution has finitely many steps.
The tail theorem additionally requires a positive initial bound. Zero drift
is allowed throughout, and the mean bounds also allow a zero initial bound.

An algorithmic application must separately establish its conditional choice
law, derive integrated drift under that same law, and connect the sum to its
actual observed work. These analytic theorems introduce no sampling operation
or executor. Source correspondence belongs to the FDSA reconstruction map.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Applications.Probability.AccumulatedWork

open MeasureTheory
open scoped ENNReal BigOperators

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- Integrated one-step drift bounds every mean. No measurability, contraction,
or finiteness hypothesis is needed for this ordered-integral induction. -/
theorem lintegral_le_geometric (μ : Measure Ω) (X : Nat → Ω → ℝ≥0∞)
    {q N : ℝ≥0∞}
    (initial : (∫⁻ ω, X 0 ω ∂μ) ≤ N)
    (drift : ∀ t, (∫⁻ ω, X (t + 1) ω ∂μ) ≤ q * (∫⁻ ω, X t ω ∂μ))
    (t : Nat) : (∫⁻ ω, X t ω ∂μ) ≤ q ^ t * N := by
  induction t with
  | zero => simpa only [pow_zero, one_mul] using initial
  | succ t ih =>
      calc
        (∫⁻ ω, X (t + 1) ω ∂μ) ≤ q * (∫⁻ ω, X t ω ∂μ) := drift t
        _ ≤ q * (q ^ t * N) := mul_le_mul_left' ih q
        _ = q ^ (t + 1) * N := by rw [pow_succ', mul_assoc]

/-- The integral of the actual shifted sum is bounded by a geometric series.
This extended-valued inequality remains valid without strict contraction. -/
theorem lintegral_tsum_shift_le (μ : Measure Ω) (X : Nat → Ω → ℝ≥0∞)
    {q N : ℝ≥0∞}
    (hmeas : ∀ t, AEMeasurable (X t) μ)
    (initial : (∫⁻ ω, X 0 ω ∂μ) ≤ N)
    (drift : ∀ t, (∫⁻ ω, X (t + 1) ω ∂μ) ≤ q * (∫⁻ ω, X t ω ∂μ))
    (w : Nat) :
    (∫⁻ ω, (∑' j : Nat, X (w + j) ω) ∂μ) ≤ q ^ w * N / (1 - q) := by
  rw [lintegral_tsum (fun j => hmeas (w + j))]
  calc
    (∑' j : Nat, ∫⁻ ω, X (w + j) ω ∂μ) ≤ ∑' j : Nat, q ^ (w + j) * N :=
      ENNReal.tsum_le_tsum fun j => lintegral_le_geometric μ X initial drift (w + j)
    _ = ∑' j : Nat, (q ^ w * N) * q ^ j := by
      apply tsum_congr
      intro j
      rw [pow_add, mul_right_comm]
    _ = q ^ w * N / (1 - q) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, div_eq_mul_inv]

/-- The total-work bound is the zero-shift specialization, including a zero
initial bound and a zero drift factor. -/
theorem lintegral_tsum_le (μ : Measure Ω) (X : Nat → Ω → ℝ≥0∞)
    {q N : ℝ≥0∞}
    (hmeas : ∀ t, AEMeasurable (X t) μ)
    (initial : (∫⁻ ω, X 0 ω ∂μ) ≤ N)
    (drift : ∀ t, (∫⁻ ω, X (t + 1) ω ∂μ) ≤ q * (∫⁻ ω, X t ω ∂μ)) :
    (∫⁻ ω, (∑' t : Nat, X t ω) ∂μ) ≤ N / (1 - q) := by
  simpa only [zero_add, pow_zero, one_mul] using
    lintegral_tsum_shift_le μ X hmeas initial drift 0

/-- Strict contraction and a finite initial bound make the total-work integral
finite. This is not a finite-step termination theorem. -/
theorem lintegral_tsum_lt_top (μ : Measure Ω) (X : Nat → Ω → ℝ≥0∞)
    {q N : ℝ≥0∞}
    (hmeas : ∀ t, AEMeasurable (X t) μ)
    (initial : (∫⁻ ω, X 0 ω ∂μ) ≤ N)
    (drift : ∀ t, (∫⁻ ω, X (t + 1) ω ∂μ) ≤ q * (∫⁻ ω, X t ω ∂μ))
    (hq : q < 1) (hNtop : N ≠ ∞) :
    (∫⁻ ω, (∑' t : Nat, X t ω) ∂μ) < ∞ := by
  have hden : (1 - q) ≠ 0 := (tsub_pos_iff_lt.mpr hq).ne'
  exact (lintegral_tsum_le μ X hmeas initial drift).trans_lt
    (ENNReal.div_lt_top hNtop hden)

/-- A bound on this one actual prefix suffices for the excess-work tail.
The positive finite initial bound makes the Markov threshold cancellable;
there is no positivity assumption on the drift factor. -/
theorem measure_tsum_ge_le (μ : Measure Ω) (X : Nat → Ω → ℝ≥0∞)
    {q N : ℝ≥0∞}
    (hmeas : ∀ t, AEMeasurable (X t) μ)
    (initial : (∫⁻ ω, X 0 ω ∂μ) ≤ N)
    (drift : ∀ t, (∫⁻ ω, X (t + 1) ω ∂μ) ≤ q * (∫⁻ ω, X t ω ∂μ))
    (w : Nat) (hq : q < 1) (hNzero : N ≠ 0) (hNtop : N ≠ ∞)
    (prefix : ∀ᵐ ω ∂μ, (∑ t ∈ Finset.range w, X t ω) ≤ (w : ℝ≥0∞) * N) :
    μ {ω | (w : ℝ≥0∞) * N + N / (1 - q) ≤ ∑' t : Nat, X t ω} ≤ q ^ w := by
  have hdenzero : (1 - q) ≠ 0 := (tsub_pos_iff_lt.mpr hq).ne'
  have hdentop : (1 - q) ≠ ∞ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hthreshold : 0 < N / (1 - q) := ENNReal.div_pos hNzero hdentop
  have hthresholdTop : N / (1 - q) ≠ ∞ := ENNReal.div_ne_top hNtop hdenzero
  have hprefixTop : (w : ℝ≥0∞) * N ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top w) hNtop
  have hremaining : AEMeasurable (fun ω => ∑' j : Nat, X (w + j) ω) μ :=
    AEMeasurable.tsum fun j => hmeas (w + j)
  calc
    μ {ω | (w : ℝ≥0∞) * N + N / (1 - q) ≤ ∑' t : Nat, X t ω} ≤
        μ {ω | N / (1 - q) ≤ ∑' j : Nat, X (w + j) ω} := by
      apply measure_mono_ae
      filter_upwards [prefix] with ω hprefix
      intro htotal
      change (w : ℝ≥0∞) * N + N / (1 - q) ≤ ∑' t : Nat, X t ω at htotal
      change N / (1 - q) ≤ ∑' j : Nat, X (w + j) ω
      have hsplit : (∑ t ∈ Finset.range w, X t ω) +
          (∑' j : Nat, X (w + j) ω) = ∑' t : Nat, X t ω := by
        simpa only [Nat.add_comm] using
          (Summable.sum_add_tsum_nat_add' (f := fun t : Nat => X t ω) (k := w)
            (ENNReal.summable : Summable (fun j : Nat => X (j + w) ω)))
      apply ENNReal.le_of_add_le_add_left hprefixTop
      apply htotal.trans
      rw [← hsplit]
      exact add_le_add_right hprefix _
    _ ≤ (∫⁻ ω, (∑' j : Nat, X (w + j) ω) ∂μ) / (N / (1 - q)) :=
      meas_ge_le_lintegral_div hremaining hthreshold.ne' hthresholdTop
    _ ≤ (q ^ w * N / (1 - q)) / (N / (1 - q)) :=
      ENNReal.div_le_div_right (lintegral_tsum_shift_le μ X hmeas initial drift w) _
    _ = (q ^ w * (N / (1 - q))) / (N / (1 - q)) := by rw [mul_div_assoc]
    _ = q ^ w := ENNReal.mul_div_cancel_right hthreshold.ne' hthresholdTop

/-- A common almost-everywhere stage bound supplies the required prefix bound.
The preceding theorem remains available when only one prefix is controlled. -/
theorem measure_tsum_ge_le_of_stage_le (μ : Measure Ω) (X : Nat → Ω → ℝ≥0∞)
    {q N : ℝ≥0∞}
    (hmeas : ∀ t, AEMeasurable (X t) μ)
    (initial : (∫⁻ ω, X 0 ω ∂μ) ≤ N)
    (drift : ∀ t, (∫⁻ ω, X (t + 1) ω ∂μ) ≤ q * (∫⁻ ω, X t ω ∂μ))
    (w : Nat) (hq : q < 1) (hNzero : N ≠ 0) (hNtop : N ≠ ∞)
    (stageBound : ∀ t, X t ≤ᵐ[μ] (fun _ => N)) :
    μ {ω | (w : ℝ≥0∞) * N + N / (1 - q) ≤ ∑' t : Nat, X t ω} ≤ q ^ w := by
  apply measure_tsum_ge_le μ X hmeas initial drift w hq hNzero hNtop
  filter_upwards [ae_all_iff.mpr stageBound] with ω hω
  calc
    (∑ t ∈ Finset.range w, X t ω) ≤ ∑ _t ∈ Finset.range w, N :=
      Finset.sum_le_sum fun t _ => hω t
    _ = (w : ℝ≥0∞) * N := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Applications.Probability.AccumulatedWork
