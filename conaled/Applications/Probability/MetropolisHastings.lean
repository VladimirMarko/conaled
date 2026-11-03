import Applications.Probability.FiniteKernel
import Applications.Probability.AcceptReject

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Applications.Probability
namespace FiniteMH
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
  [MeasurableSpace α] [MeasurableSingletonClass α] (m : FiniteMH α)

/-- The normalized exact target, as a constant stochastic table. -/
def targetTable : Table Unit α where
  entry _ := m.target
  nonneg _ := m.target_nonneg
  sum_row _ := m.target_sum

noncomputable def targetMeasure : Measure α := m.targetTable.kernel ()

instance : IsProbabilityMeasure m.targetMeasure := by
  unfold targetMeasure
  infer_instance

/-- The explicit rational acceptance convention interpreted as measurable mass. -/
noncomputable def acceptanceMass (x y : α) : ℝ≥0∞ := mass (m.acceptance x y)

omit [Nonempty α] [DecidableEq α] in
theorem acceptanceMass_measurable : Measurable (Function.uncurry m.acceptanceMass) :=
  measurable_of_countable _

omit [Nonempty α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem acceptanceMass_le_one (x y : α) : m.acceptanceMass x y ≤ 1 := by
  change ENNReal.ofReal (m.acceptance x y : ℝ) ≤ 1
  rw [ENNReal.ofReal_le_one]
  exact_mod_cast m.acceptance_le_one x y

omit [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem accepted_target_balance (x y : α) :
    mass (m.target x) * (mass (m.proposal.entry x y) * m.acceptanceMass x y) =
      mass (m.target y) * (mass (m.proposal.entry y x) * m.acceptanceMass y x) := by
  simp only [acceptanceMass, ← mass_mul _ _ (m.proposal.nonneg _ _),
    ← mass_mul _ _ (m.target_nonneg _)]
  congr 1
  simpa only [target, accepted, div_mul_eq_mul_div] using
    congrArg (fun z => z / m.normalizer) (m.accepted_balance x y)

omit [DecidableEq α] in
theorem accepted_reversible :
    (m.proposal.kernel.withDensity m.acceptanceMass).IsReversible m.targetMeasure := by
  intro A B hA hB
  simp only [Kernel.withDensity_apply' _ m.acceptanceMass_measurable]
  rw [← lintegral_indicator hA, ← lintegral_indicator hB]
  change (∫⁻ x, A.indicator (fun x => ∫⁻ y in B, m.acceptanceMass x y ∂m.proposal.kernel x)
    x ∂m.targetTable.kernel ()) =
    ∫⁻ x, B.indicator (fun x => ∫⁻ y in A, m.acceptanceMass x y ∂m.proposal.kernel x)
      x ∂m.targetTable.kernel ()
  simp_rw [Table.lintegral_kernel, ← lintegral_indicator hB,
    ← lintegral_indicator hA, Table.lintegral_kernel]
  simp only [targetTable]
  have distribute (S : Set α) (f : α → α → ℝ≥0∞) (x : α) :
      S.indicator (fun x => ∑ y, f x y) x = ∑ y, S.indicator (fun x => f x y) x := by
    by_cases h : x ∈ S <;> simp [h]
  simp_rw [distribute, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ A <;>
    simp [hx, hy, m.accepted_target_balance y x]

omit [Nonempty α] [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem rejection_mass (x : α) : mass (m.rejection x) =
    1 - ∑ y, mass (m.proposal.entry x y) * m.acceptanceMass x y := by
  have hn : 0 ≤ ∑ y, m.accepted x y := Finset.sum_nonneg (fun y _ => m.accepted_nonneg x y)
  change ENNReal.ofReal ((1 - ∑ y, m.accepted x y : ℚ) : ℝ) = _
  rw [Rat.cast_sub, ENNReal.ofReal_sub _ (by exact_mod_cast hn)]
  simp only [Rat.cast_one, ENNReal.ofReal_one]
  change 1 - mass (∑ y, m.accepted x y) = _
  rw [mass_sum _ _ (fun y _ => m.accepted_nonneg x y)]
  simp_rw [accepted, mass_mul _ _ (m.proposal.nonneg _ _)]
  rfl

omit [Nonempty α] in
/-- The executable rational table denotes the reusable measurable accept/reject step. -/
theorem transition_kernel : m.transition.kernel =
    acceptReject m.proposal.kernel m.acceptanceMass := by
  apply Kernel.ext
  intro x
  apply Measure.ext_of_singleton
  intro y
  rw [Table.kernel_singleton, acceptReject_apply _ _ m.acceptanceMass_measurable,
    lintegral_singleton, Table.kernel_singleton, Table.lintegral_kernel]
  have hadd (a b : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      mass (a + b) = mass a + mass b := by
    simp only [mass, Rat.cast_add]
    exact ENNReal.ofReal_add (by exact_mod_cast ha) (by exact_mod_cast hb)
  change mass (m.accepted x y + if x = y then m.rejection x else 0) = _
  by_cases h : x = y
  · subst y
    rw [ite_eq_left rfl, hadd _ _ (m.accepted_nonneg x x) (m.rejection_nonneg x),
      m.rejection_mass]
    simp only [accepted, mass_mul _ _ (m.proposal.nonneg _ _)]
    simp [acceptanceMass, mul_comm]
  · simp only [h, ite_false, add_zero, accepted, mass_mul _ _ (m.proposal.nonneg _ _)]
    simp [acceptanceMass, h, mul_comm]

theorem reversible : m.transition.kernel.IsReversible m.targetMeasure := by
  rw [m.transition_kernel]
  exact acceptReject_reversible _ _ _ m.accepted_reversible

/-- Stationarity follows from Mathlib's reversible-kernel theorem through accept/reject. -/
theorem invariant : m.transition.kernel.Invariant m.targetMeasure := by
  rw [m.transition_kernel]
  exact acceptReject_invariant _ _ m.acceptanceMass_measurable
    m.acceptanceMass_le_one _ m.accepted_reversible

end FiniteMH

namespace FiniteMHExamples

/-- The asymmetric exact computation also satisfies the measure-level invariant contract. -/
theorem asymmetric_kernel_invariant [MeasurableSpace Bool] [MeasurableSingletonClass Bool] :
    asymmetric.transition.kernel.Invariant asymmetric.targetMeasure := asymmetric.invariant

end FiniteMHExamples
end Applications.Probability
