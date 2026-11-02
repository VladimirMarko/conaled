import Applications.Probability.AccumulatedWork
import Applications.Resources.CallCount
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.UniformOn
import Mathlib.Tactic.NormNum

/-!
# Boundaries of accumulated-work estimates

An actual measured computation supplies the deterministic one-stage work.
The other cases distinguish the hypotheses of the analytic estimates:
zero drift permits finite work, a zero initial bound does not permit the
non-strict zero-threshold tail, integrated drift does not supply a prefix
bound, and a noncontracting sequence can have infinite total work.

The finite laws here are the standard Dirac and uniform measures. No sampling
algorithm or conditional pivot law is certified by these examples.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.AccumulatedWorkBoundary

open MeasureTheory
open Applications.Probability
open scoped ENNReal BigOperators

local notation "μ₁" => (Measure.dirac () : Measure Unit)
local notation "μ₃" => ProbabilityTheory.uniformOn (Set.univ : Set (Fin 3))

/-- The bound expression is evaluated once and passed to a two-entry body.
The independently specified result is seven, with three observed entries. -/
def oneStageRun : Resources.Measured Nat Nat :=
  Resources.bind (Resources.CallCount.tick (Resources.pure 4))
    (fun n => Resources.CallCount.tick
      (Resources.CallCount.tick (Resources.pure (n + 3))))

theorem oneStageRun_value : oneStageRun.1 = 7 := rfl

theorem oneStageRun_cost : oneStageRun.2 = 3 := rfl

/-- This is the observation of the actual computation, followed by no work. -/
def singleWork (t : Nat) (_ : Unit) : ℝ≥0∞ :=
  if t = 0 then (oneStageRun.2 : ℝ≥0∞) else 0

theorem singleWork_measurable (t : Nat) : AEMeasurable (singleWork t) μ₁ :=
  (measurable_of_countable _).aemeasurable

theorem singleWork_total (ω : Unit) : (∑' t : Nat, singleWork t ω) = 3 := by
  simp [singleWork, oneStageRun_cost]

theorem oneStageRun_observed (ω : Unit) :
    (oneStageRun.2 : ℝ≥0∞) = ∑' t : Nat, singleWork t ω := by
  rw [oneStageRun_cost, singleWork_total]

theorem singleWork_initial : (∫⁻ ω, singleWork 0 ω ∂μ₁) = 3 := by
  simp [singleWork, oneStageRun_cost]

theorem singleWork_drift (t : Nat) :
    (∫⁻ ω, singleWork (t + 1) ω ∂μ₁) ≤ 0 * (∫⁻ ω, singleWork t ω ∂μ₁) := by
  simp [singleWork]

theorem singleWork_stage_le (t : Nat) :
    singleWork t ≤ᵐ[μ₁] (fun _ => (3 : ℝ≥0∞)) := by
  apply Filter.Eventually.of_forall
  intro ω
  by_cases ht : t = 0 <;> simp [singleWork, ht, oneStageRun_cost]

/-- Zero drift is admitted by the public total-work theorem. -/
theorem singleWork_integral_le :
    (∫⁻ ω, (∑' t : Nat, singleWork t ω) ∂μ₁) ≤ 3 := by
  simpa using AccumulatedWork.lintegral_tsum_le μ₁ singleWork (q := 0) (N := 3)
    singleWork_measurable singleWork_initial.le singleWork_drift

theorem singleWork_integral_finite :
    (∫⁻ ω, (∑' t : Nat, singleWork t ω) ∂μ₁) < ∞ :=
  AccumulatedWork.lintegral_tsum_lt_top μ₁ singleWork (q := 0) (N := 3)
    singleWork_measurable singleWork_initial.le singleWork_drift
    (by norm_num) (by simp)

theorem singleWork_tail (w : Nat) :
    μ₁ {ω | (w : ℝ≥0∞) * 3 + 3 ≤ ∑' t : Nat, singleWork t ω} ≤ (0 : ℝ≥0∞) ^ w := by
  simpa using AccumulatedWork.measure_tsum_ge_le_of_stage_le μ₁ singleWork
    (q := 0) (N := 3) singleWork_measurable singleWork_initial.le singleWork_drift
    w (by norm_num) (by norm_num) (by simp) singleWork_stage_le

/-- At zero shift the non-strict event has full mass, and the bound is `0^0=1`. -/
theorem singleWork_tail_zero :
    μ₁ {ω | 3 ≤ ∑' t : Nat, singleWork t ω} = 1 ∧
      μ₁ {ω | 3 ≤ ∑' t : Nat, singleWork t ω} ≤ (0 : ℝ≥0∞) ^ 0 := by
  constructor
  · simp [singleWork_total]
  · simpa using singleWork_tail 0

/-- For a positive shift the generic zero-drift tail bound forces zero mass. -/
theorem singleWork_tail_pos (w : Nat) (hw : 0 < w) :
    μ₁ {ω | (w : ℝ≥0∞) * 3 + 3 ≤ ∑' t : Nat, singleWork t ω} = 0 := by
  apply le_antisymm ?_ bot_le
  simpa only [zero_pow (ne_of_gt hw)] using singleWork_tail w

def zeroWork : Nat → Unit → ℝ≥0∞ := fun _ _ => 0

/-- The zero initial bound remains valid for the total-work theorem. -/
theorem zeroWork_integral :
    (∫⁻ ω, (∑' t : Nat, zeroWork t ω) ∂μ₁) = 0 := by
  apply le_antisymm ?_ bot_le
  simpa using AccumulatedWork.lintegral_tsum_le μ₁ zeroWork
    (q := 1 / 2) (N := 0) (fun _ => aemeasurable_const)
    (by simp [zeroWork]) (fun _ => by simp [zeroWork])

/-- Removing positive `N` makes the proposed non-strict tail false:
the zero-threshold event has mass one, exceeding one-half. -/
theorem zeroWork_non_strict_tail_fails :
    ¬ μ₁ {ω | (1 : ℝ≥0∞) * 0 + 0 / (1 - (1 / 2 : ℝ≥0∞)) ≤
      ∑' t : Nat, zeroWork t ω} ≤ (1 / 2 : ℝ≥0∞) ^ 1 := by
  have half_lt_one : (1 / 2 : ℝ≥0∞) < 1 := by
    simpa only [one_div] using ENNReal.one_half_lt_one
  simpa [zeroWork] using not_le_of_gt half_lt_one

/-- Only one of the three equally likely outcomes incurs the initial work. -/
def rareWork (t : Nat) (ω : Fin 3) : ℝ≥0∞ :=
  if t = 0 then (if ω = 0 then 3 else 0) else 0

theorem uniform_three_singleton (ω : Fin 3) : μ₃ {ω} = (1 : ℝ≥0∞) / 3 := by
  simp [ProbabilityTheory.uniformOn_univ, Measure.count_singleton]

theorem rareWork_measurable (t : Nat) : AEMeasurable (rareWork t) μ₃ :=
  (measurable_of_countable _).aemeasurable

theorem rareWork_initial : (∫⁻ ω, rareWork 0 ω ∂μ₃) = 1 := by
  classical
  rw [lintegral_fintype, Finset.sum_eq_single (0 : Fin 3)]
  · change (3 : ℝ≥0∞) * μ₃ {(0 : Fin 3)} = 1
    rw [uniform_three_singleton, one_div]
    exact ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top
  · intro ω _ hω
    simp [rareWork, hω]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem rareWork_drift (t : Nat) :
    (∫⁻ ω, rareWork (t + 1) ω ∂μ₃) ≤ 0 * (∫⁻ ω, rareWork t ω ∂μ₃) := by
  simp [rareWork]

theorem rareWork_total (ω : Fin 3) :
    (∑' t : Nat, rareWork t ω) = if ω = 0 then 3 else 0 := by
  simp [rareWork]

theorem rareWork_integral :
    (∫⁻ ω, (∑' t : Nat, rareWork t ω) ∂μ₃) = 1 := by
  calc
    _ = ∫⁻ ω, rareWork 0 ω ∂μ₃ := lintegral_congr fun ω => by simp [rareWork]
    _ = 1 := rareWork_initial

/-- The integrated hypotheses hold with `N=1,q=0`, despite a cost-three sample. -/
theorem rareWork_integral_le :
    (∫⁻ ω, (∑' t : Nat, rareWork t ω) ∂μ₃) ≤ 1 := by
  simpa using AccumulatedWork.lintegral_tsum_le μ₃ rareWork (q := 0) (N := 1)
    rareWork_measurable rareWork_initial.le rareWork_drift

theorem rareWork_tail_event :
    {ω | (2 : ℝ≥0∞) ≤ ∑' t : Nat, rareWork t ω} = ({0} : Set (Fin 3)) := by
  apply Set.ext
  intro ω
  by_cases hω : ω = 0 <;> norm_num [rareWork_total, hω]

theorem rareWork_tail_mass :
    μ₃ {ω | (2 : ℝ≥0∞) ≤ ∑' t : Nat, rareWork t ω} = (1 : ℝ≥0∞) / 3 := by
  rw [rareWork_tail_event, uniform_three_singleton]

theorem rareWork_tail_positive :
    0 < μ₃ {ω | (2 : ℝ≥0∞) ≤ ∑' t : Nat, rareWork t ω} := by
  rw [rareWork_tail_mass]
  exact ENNReal.div_pos one_ne_zero ENNReal.ofNat_ne_top

/-- This is the proposed `w=1,N=1,q=0` tail without its prefix hypothesis. -/
theorem rareWork_tail_without_prefix_fails :
    ¬ μ₃ {ω | (2 : ℝ≥0∞) ≤ ∑' t : Nat, rareWork t ω} ≤ (0 : ℝ≥0∞) ^ 1 := by
  simpa only [pow_one] using not_le_of_gt rareWork_tail_positive

/-- The failed tail and the public theorem also show that the actual prefix
bound is unavailable; it cannot be inferred from these integrated hypotheses. -/
theorem rareWork_prefix_fails :
    ¬ ∀ᵐ ω ∂μ₃, (∑ t ∈ Finset.range 1, rareWork t ω) ≤ (1 : ℝ≥0∞) * 1 := by
  intro prefix
  have bound := AccumulatedWork.measure_tsum_ge_le μ₃ rareWork
    (q := 0) (N := 1) rareWork_measurable rareWork_initial.le rareWork_drift
    1 (by norm_num) (by norm_num) (by simp) prefix
  apply rareWork_tail_without_prefix_fails
  simpa only [Nat.cast_one, one_mul, tsub_zero, div_one, one_add_one_eq_two] using bound

def constantWork : Nat → Unit → ℝ≥0∞ := fun _ _ => 1

theorem constantWork_initial : (∫⁻ ω, constantWork 0 ω ∂μ₁) = 1 := by
  simp [constantWork]

theorem constantWork_drift (t : Nat) :
    (∫⁻ ω, constantWork (t + 1) ω ∂μ₁) ≤
      (1 : ℝ≥0∞) * (∫⁻ ω, constantWork t ω ∂μ₁) := by
  simp [constantWork]

theorem constantWork_total (ω : Unit) : (∑' t : Nat, constantWork t ω) = ∞ :=
  ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

/-- Without contraction the same initial/drift shape permits infinite work. -/
theorem constantWork_integral :
    (∫⁻ ω, (∑' t : Nat, constantWork t ω) ∂μ₁) = ∞ := by
  simp [constantWork_total]

/-- The extended-valued generic bound still applies at `q=1`; its denominator
is zero, so it supplies no finite upper bound. -/
theorem constantWork_extended_bound :
    (∫⁻ ω, (∑' t : Nat, constantWork t ω) ∂μ₁) ≤
      (1 : ℝ≥0∞) / (1 - (1 : ℝ≥0∞)) :=
  AccumulatedWork.lintegral_tsum_le μ₁ constantWork (q := 1) (N := 1)
    (fun _ => aemeasurable_const) constantWork_initial.le constantWork_drift

end Examples.AccumulatedWorkBoundary
