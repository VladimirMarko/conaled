import Applications.Probability.TableSamplerIteration
import Applications.Probability.MetropolisHastings

/-!
# Operational finite Metropolis–Hastings

Prepared transition rows realize the existing rational MH construction. Finite
chains are actual repeated tape executions; stationarity is reused from the
existing kernel proof and is not a mixing assertion.
-/
namespace Applications.Probability.FiniteMH
open CoinPaths MeasureTheory
open scoped ENNReal
variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (m : FiniteMH α) {d : ℕ} (e : Fin d ≃ α)

omit [Nonempty α] in
theorem sampler_transition (x y : α) (s : ℕ) :
    law ((m.transition.prepare e x).returns s y)=m.transition.kernel x {y} :=
  m.transition.prepare_kernel e x s y

theorem sampler_iteration (X : FiniteSpace) (m : FiniteMH X) {d : ℕ}
    (e : Fin d ≃ X) (n : ℕ) (x y : X) (s : ℕ) :
    law (RowChain.finalEvent (m.transition.prepare e) n x s y)=
      kernelSteps m.transition.kernel n x {y} := by
  rw [RowChain.table_final_mass,← table_steps_meaning X,Table.kernel_singleton]

/-- Every finite operational chain has the stationary target kernel law. -/
theorem sampler_stationary (n : ℕ) :
    (kernelSteps m.transition.kernel n).Invariant m.targetMeasure :=
  invariant_steps m.invariant n

/-- Starting from the target, the actual finite chain has the same final law.
This statement integrates operational probabilities, not merely a named kernel. -/
theorem operational_stationary (X : FiniteSpace) (m : FiniteMH X) [Nonempty X]
    {d : ℕ} (e : Fin d ≃ X) (n : ℕ) (y : X) (s : ℕ) :
    ∑ x, mass (m.target x)*law (RowChain.finalEvent (m.transition.prepare e) n x s y)=
      mass (m.target y) := by
  simp_rw [sampler_iteration X m e n]
  have hi := invariant_steps m.invariant n
  have he := congrArg (fun μ : Measure X => μ {y}) hi
  rw [Measure.bind_apply (measurableSet_singleton y)
    (measurable_of_countable _).aemeasurable] at he
  change (∫⁻ x, kernelSteps m.transition.kernel n x {y} ∂m.targetTable.kernel ())=_ at he
  rw [Table.lintegral_kernel] at he
  simpa [targetMeasure,Table.kernel_singleton,targetTable] using he

end Applications.Probability.FiniteMH
