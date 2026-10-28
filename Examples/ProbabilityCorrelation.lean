import Applications.Probability.FiniteKernel
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Examples.ProbabilityCorrelation

noncomputable def fair : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true

instance : IsProbabilityMeasure fair := by
  constructor
  norm_num [fair, ← ENNReal.coe_div, ← ENNReal.coe_add, ENNReal.inv_two_add_inv_two]

/-- Copying one fair draw retains its correlation. -/
noncomputable def shared : Measure (Bool × Bool) := fair.map (fun x => (x, x))

/-- Independent draws use the product measure. -/
noncomputable def independent : Measure (Bool × Bool) := fair.prod fair

theorem shared_first : shared.map Prod.fst = fair := by
  rw [shared, Measure.map_map measurable_fst (by fun_prop)]
  exact Measure.map_id

theorem shared_second : shared.map Prod.snd = fair := by
  rw [shared, Measure.map_map measurable_snd (by fun_prop)]
  exact Measure.map_id

theorem independent_first : independent.map Prod.fst = fair := by
  rw [independent, Measure.map_fst_prod, measure_univ, one_smul]

theorem independent_second : independent.map Prod.snd = fair := by
  rw [independent, Measure.map_snd_prod, measure_univ, one_smul]

theorem shared_off_diagonal : shared {(false, true)} = 0 := by
  rw [shared, Measure.map_apply (by fun_prop) (MeasurableSet.singleton _)]
  have h : (fun x : Bool => (x, x)) ⁻¹' {(false, true)} = ∅ := by
    ext x
    cases x <;> simp
  simp [h]

theorem independent_off_diagonal : independent {(false, true)} = 1 / 4 := by
  rw [independent, ← Set.singleton_prod_singleton, Measure.prod_prod]
  norm_num [fair, Measure.add_apply, Measure.smul_apply, ← ENNReal.coe_div, ← ENNReal.coe_mul, ← ENNReal.mul_inv]

theorem joint_distributions_differ : shared ≠ independent := by
  intro h
  have := congrArg (fun μ : Measure (Bool × Bool) => μ {(false, true)}) h
  rw [shared_off_diagonal, independent_off_diagonal] at this
  exact (ENNReal.inv_ne_zero.mpr (by simp) : (4 : ℝ≥0∞)⁻¹ ≠ 0) (by simpa using this.symm)

noncomputable def draw : Kernel Unit Bool := Kernel.const Unit fair

instance : IsMarkovKernel draw := inferInstanceAs (IsMarkovKernel (Kernel.const Unit fair))

theorem copy_after_draw : (Kernel.copy Bool ∘ₖ draw) () = shared := by
  rw [Kernel.copy, Kernel.deterministic_comp_eq_map, Kernel.map_apply _ (by fun_prop)]
  rfl

theorem draw_twice : (draw ×ₖ draw) () = independent := by
  rw [Kernel.prod_apply]
  rfl

/-- The identity kernel preserves fair probabilities but never leaves the initial state. -/
theorem identity_invariant : (Kernel.id : Kernel Bool Bool).Invariant fair :=
  Measure.bind_dirac

theorem identity_steps (n : ℕ) :
    Applications.Probability.kernelSteps (Kernel.id : Kernel Bool Bool) n = Kernel.id := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Applications.Probability.kernelSteps, ih]

/-- Stationarity does not make an identity orbit converge from a fixed initial state. -/
theorem identity_does_not_converge_to_fair :
    ¬ Filter.Tendsto
      (fun n => Applications.Probability.kernelSteps (Kernel.id : Kernel Bool Bool) n
        false {false}) Filter.atTop (nhds (fair {false})) := by
  intro h
  have hm : fair {false} ∈ ({1} : Set ℝ≥0∞) :=
    isClosed_singleton.mem_of_tendsto h (Filter.Eventually.of_forall fun n => by
      simp [identity_steps, Kernel.id_apply])
  norm_num [fair, Measure.add_apply, Measure.smul_apply] at hm

noncomputable def flip : Kernel Bool Bool := Kernel.deterministic Bool.not (by fun_prop)

theorem flip_period_two : flip ∘ₖ flip = Kernel.id := by
  rw [flip, Kernel.deterministic_comp_deterministic]
  congr 1
  funext x
  cases x <;> rfl

theorem flip_preserves_fair : flip.Invariant fair := by
  change fair.bind (fun x => Measure.dirac (!x)) = fair
  rw [Measure.bind_dirac_eq_map fair (f := Bool.not) (by fun_prop)]
  unfold fair
  rw [Measure.map_add _ _ (show Measurable Bool.not by fun_prop)]
  rw [Measure.map_smul _ (show Measurable Bool.not by fun_prop).aemeasurable,
    Measure.map_smul _ (show Measurable Bool.not by fun_prop).aemeasurable]
  simp only [Measure.map_dirac' (show Measurable Bool.not by fun_prop),
    Bool.not_false, Bool.not_true]
  exact add_comm _ _

theorem flip_steps (n : ℕ) : Applications.Probability.kernelSteps flip n =
    Kernel.deterministic (Bool.not^[n]) (by fun_prop) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Applications.Probability.kernelSteps, ih, flip,
      Kernel.deterministic_comp_deterministic]
    congr 1
    funext x
    exact (Function.iterate_succ_apply' Bool.not n x).symm

/-- Singleton observations of the orbit started at `false`. -/
noncomputable def orbitMass (n : ℕ) : ℝ≥0∞ :=
  Measure.dirac ((Bool.not^[n]) false) {false}

theorem orbitMass_eq_steps (n : ℕ) : orbitMass n =
    Applications.Probability.kernelSteps flip n false {false} := by
  rw [flip_steps]
  rfl

theorem orbit_does_not_converge_to_fair :
    ¬ Filter.Tendsto orbitMass Filter.atTop (nhds (fair {false})) := by
  intro h
  have hm : fair {false} ∈ ({0, 1} : Set ℝ≥0∞) :=
    (Set.toFinite ({0, 1} : Set ℝ≥0∞)).isClosed.mem_of_tendsto h
      (Filter.Eventually.of_forall fun n => by
        simp only [orbitMass]
        cases (Bool.not^[n]) false <;> simp)
  norm_num [fair, Measure.add_apply, Measure.smul_apply] at hm

end Examples.ProbabilityCorrelation
