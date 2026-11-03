import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.WithDensity

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Applications.Probability

variable {α : Type*} [MeasurableSpace α]

/-- Complete an accepted-move subkernel by retaining rejected mass at the current state. -/
noncomputable def complete (accepted : Kernel α α) : Kernel α α where
  toFun x := accepted x + (1 - accepted x Set.univ) • Measure.dirac x
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact (accepted.measurable_coe hs).add
      ((measurable_const.sub (accepted.measurable_coe MeasurableSet.univ)).mul
        (Kernel.id.measurable_coe hs))

theorem complete_apply (accepted : Kernel α α) (x : α) (s : Set α) :
    complete accepted x s = accepted x s +
      (1 - accepted x Set.univ) * Measure.dirac x s := by
  rfl

theorem complete_markov (accepted : Kernel α α)
    (h : ∀ x, accepted x Set.univ ≤ 1) : IsMarkovKernel (complete accepted) := by
  constructor
  intro x
  constructor
  simpa [complete_apply] using add_tsub_cancel_of_le (h x)

/-- Diagonal rejection is symmetric; all balance obligations concern accepted moves. -/
theorem complete_reversible (accepted : Kernel α α) (π : Measure α)
    (h : accepted.IsReversible π) : (complete accepted).IsReversible π := by
  intro A B hA hB
  simp only [complete_apply]
  rw [lintegral_add_left (accepted.measurable_coe hB),
    lintegral_add_left (accepted.measurable_coe hA), h hA hB]
  congr 1
  have eq_indicator (s : Set α) (hs : MeasurableSet s) :
      (fun x => (1 - accepted x Set.univ) * Measure.dirac x s) =
        s.indicator (fun x => 1 - accepted x Set.univ) := by
    funext x
    by_cases hx : x ∈ s <;> simp [Measure.dirac_apply' x hs, hx]
  rw [eq_indicator B hB, eq_indicator A hA,
    setLIntegral_indicator hB, setLIntegral_indicator hA, Set.inter_comm B A]

theorem complete_invariant (accepted : Kernel α α) (π : Measure α)
    (mass : ∀ x, accepted x Set.univ ≤ 1) (balance : accepted.IsReversible π) :
    (complete accepted).Invariant π := by
  let := complete_markov accepted mass
  exact (complete_reversible accepted π balance).invariant

/-- General measurable accept/reject step, including its diagonal rejection mass. -/
noncomputable def acceptReject (proposal : Kernel α α) [IsMarkovKernel proposal]
    (acceptance : α → α → ℝ≥0∞) : Kernel α α :=
  complete (proposal.withDensity acceptance)

theorem accepted_mass_le_one (proposal : Kernel α α) [IsMarkovKernel proposal]
    (acceptance : α → α → ℝ≥0∞) (hm : Measurable (Function.uncurry acceptance))
    (hb : ∀ x y, acceptance x y ≤ 1) (x : α) :
    proposal.withDensity acceptance x Set.univ ≤ 1 := by
  rw [Kernel.withDensity_apply' _ hm, setLIntegral_univ]
  calc
    ∫⁻ y, acceptance x y ∂proposal x ≤ ∫⁻ _, 1 ∂proposal x := lintegral_mono (hb x)
    _ = 1 := by simp

theorem acceptReject_markov (proposal : Kernel α α) [IsMarkovKernel proposal]
    (acceptance : α → α → ℝ≥0∞) (hm : Measurable (Function.uncurry acceptance))
    (hb : ∀ x y, acceptance x y ≤ 1) : IsMarkovKernel (acceptReject proposal acceptance) :=
  complete_markov _ (accepted_mass_le_one proposal acceptance hm hb)

theorem acceptReject_apply (proposal : Kernel α α) [IsMarkovKernel proposal]
    (acceptance : α → α → ℝ≥0∞) (hm : Measurable (Function.uncurry acceptance))
    (x : α) (s : Set α) :
    acceptReject proposal acceptance x s = (∫⁻ y in s, acceptance x y ∂proposal x) +
      (1 - ∫⁻ y, acceptance x y ∂proposal x) * Measure.dirac x s := by
  simp [acceptReject, complete_apply, Kernel.withDensity_apply' _ hm]

theorem acceptReject_reversible (proposal : Kernel α α) [IsMarkovKernel proposal]
    (acceptance : α → α → ℝ≥0∞) (π : Measure α)
    (balance : (proposal.withDensity acceptance).IsReversible π) :
    (acceptReject proposal acceptance).IsReversible π :=
  complete_reversible _ π balance

theorem acceptReject_invariant (proposal : Kernel α α) [IsMarkovKernel proposal]
    (acceptance : α → α → ℝ≥0∞) (hm : Measurable (Function.uncurry acceptance))
    (hb : ∀ x y, acceptance x y ≤ 1) (π : Measure α)
    (balance : (proposal.withDensity acceptance).IsReversible π) :
    (acceptReject proposal acceptance).Invariant π :=
  complete_invariant _ π (accepted_mass_le_one proposal acceptance hm hb) balance

/-- An integral balance condition on accepted proposal flow suffices, without densities
for the target or a dominating reference measure. -/
theorem acceptReject_invariant_of_flow (proposal : Kernel α α) [IsMarkovKernel proposal]
    (acceptance : α → α → ℝ≥0∞) (hm : Measurable (Function.uncurry acceptance))
    (hb : ∀ x y, acceptance x y ≤ 1) (π : Measure α)
    (flow : ∀ A B, MeasurableSet A → MeasurableSet B →
      (∫⁻ x in A, ∫⁻ y in B, acceptance x y ∂proposal x ∂π) =
      ∫⁻ x in B, ∫⁻ y in A, acceptance x y ∂proposal x ∂π) :
    (acceptReject proposal acceptance).Invariant π := by
  apply acceptReject_invariant proposal acceptance hm hb π
  intro A B hA hB
  simp only [Kernel.withDensity_apply' _ hm]
  exact flow A B hA hB

/-- Accepting every proposal recovers the proposal itself. -/
theorem acceptReject_one (proposal : Kernel α α) [IsMarkovKernel proposal] :
    acceptReject proposal (fun _ _ => 1) = proposal := by
  ext x s hs
  simp [acceptReject_apply proposal (fun _ _ => 1) measurable_const]

/-- Rejecting every proposal is the identity transition, not a missing transition. -/
theorem acceptReject_zero (proposal : Kernel α α) [IsMarkovKernel proposal] :
    acceptReject proposal (fun _ _ => 0) = Kernel.id := by
  ext x s hs
  simp [acceptReject_apply proposal (fun _ _ => 0) measurable_const, Kernel.id_apply]

/-- A degenerate rejection-only step preserves every measure. -/
theorem reject_all_invariant (proposal : Kernel α α) [IsMarkovKernel proposal]
    (π : Measure α) : (acceptReject proposal (fun _ _ => 0)).Invariant π := by
  apply acceptReject_invariant_of_flow proposal _ measurable_const (by simp) π
  intros
  simp

end Applications.Probability
