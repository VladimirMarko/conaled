import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-! Independent finite sampling contract for the represented-sampler comparison. -/
open MeasureTheory
open scoped ENNReal
namespace Applications.Probability.SamplerClient

noncomputable def fair : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true

def function (b x : Bool) : Bool := b ^^ x

@[simp] theorem function_false (b : Bool) : function b false = b := by cases b <;> rfl

def selected (b t u : Bool) : Bool × Bool × Bool × Bool :=
  (b, t, function b t, function (function b t) u)

noncomputable def pairMeaning : Measure (Bool × Bool) :=
  (1 / 4 : ℝ≥0∞) • Measure.dirac (false, false) +
  (1 / 4 : ℝ≥0∞) • Measure.dirac (false, true) +
  (1 / 4 : ℝ≥0∞) • Measure.dirac (true, false) +
  (1 / 4 : ℝ≥0∞) • Measure.dirac (true, true)

noncomputable def tripleMeaning : Measure (Bool × Bool × Bool) :=
  (fair.prod fair).prod fair |>.map (fun p => (p.1.1, p.1.2, p.2))

example : selected false true true = (false, true, true, false) := rfl
example : selected true false true = (true, false, true, false) := rfl
example (b : Bool) : function b b = false := by cases b <;> rfl
example : function false ≠ function true := by
  intro h
  have := congrFun h false
  contradiction

instance : IsProbabilityMeasure fair where
  measure_univ := by
    simpa [fair] using ENNReal.add_halves 1

@[simp] theorem fair_not : fair.map Bool.not = fair := by
  simp only [fair, Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_dirac' (measurable_of_countable _), Bool.not_false, Bool.not_true]
  exact add_comm _ _

@[simp] theorem fair_function (b : Bool) : fair.map (function b) = fair := by
  cases b
  · have h : function false = id := by funext b; cases b <;> rfl
    rw [h, Measure.map_id]
  · have h : function true = Bool.not := by funext b; cases b <;> rfl
    rw [h, fair_not]

/-- Ordinary Markov transition, defined without the QBS model. -/
noncomputable def transition : ProbabilityTheory.Kernel Bool Bool where
  toFun b := fair.map (function b)
  measurable' := measurable_of_countable _

instance : ProbabilityTheory.IsMarkovKernel transition := ⟨fun b => by
  change IsProbabilityMeasure (fair.map (function b))
  rw [fair_function]
  infer_instance⟩

theorem transition_apply (b : Bool) : transition b = fair := fair_function b

theorem native_pair : (fair.prod fair).map (fun p => (p.1, function p.1 p.2)) =
    fair.prod fair := by
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply (measurable_of_countable _) hE, Measure.prod_apply
    ((measurable_of_countable _) hE), Measure.prod_apply hE]
  apply lintegral_congr
  intro b
  have h := congrArg (fun m : Measure Bool => m (Prod.mk b ⁻¹' E)) (fair_function b)
  rw [Measure.map_apply (measurable_of_countable _) (measurable_of_countable _ hE)] at h
  exact h

theorem kernel_pair : fair.compProd transition = fair.prod fair := by
  apply Measure.ext
  intro E hE
  rw [Measure.compProd_apply hE, Measure.prod_apply hE]
  simp only [transition_apply]

/-- Fresh fair noise remains fair even when its flip is selected by the retained input. -/
theorem fresh_noise {A : Type} [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]
    (μ : Measure A) (q : A → Bool) :
    (μ.prod fair).map (fun p => (p.1, function (q p.1) p.2)) = μ.prod fair := by
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply (measurable_of_countable _) hE, Measure.prod_apply
    ((measurable_of_countable _) hE), Measure.prod_apply hE]
  apply lintegral_congr
  intro b
  have h := congrArg (fun m : Measure Bool => m (Prod.mk b ⁻¹' E)) (fair_function (q b))
  rw [Measure.map_apply (measurable_of_countable _) (measurable_of_countable _ hE)] at h
  exact h

theorem pair_meaning : fair.prod fair = pairMeaning := by
  simp only [fair, Measure.add_prod, Measure.prod_add, Measure.prod_smul_left,
    Measure.prod_smul_right, Measure.dirac_prod_dirac, smul_add, smul_smul]
  have hi : (2 : ℝ≥0∞)⁻¹ * 2⁻¹ = 4⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  simp only [one_div, hi, pairMeaning]
  ac_rfl

theorem native_three :
    ((fair.prod fair).prod fair).map
      (fun p => (p.1.1, function p.1.1 p.1.2, function (function p.1.1 p.1.2) p.2)) =
    tripleMeaning := by
  let f : Bool × Bool → Bool × Bool := fun p => (p.1, function p.1 p.2)
  let g : (Bool × Bool) × Bool → (Bool × Bool) × Bool :=
    fun p => (p.1, function p.1.2 p.2)
  let flatten : (Bool × Bool) × Bool → Bool × Bool × Bool := fun p => (p.1.1,p.1.2,p.2)
  have first : ((fair.prod fair).prod fair).map (Prod.map f id) = (fair.prod fair).prod fair := by
    rw [← Measure.map_prod_map _ _ (measurable_of_countable _) measurable_id,
      Measure.map_id, native_pair]
  have second : ((fair.prod fair).prod fair).map g = (fair.prod fair).prod fair :=
    fresh_noise (fair.prod fair) Prod.snd
  change ((fair.prod fair).prod fair).map (flatten ∘ g ∘ Prod.map f id) = _
  rw [← Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
    ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _), first, second]
  rfl

/-- Ordinary second-stage kernel retains the earlier pair in compProd. -/
noncomputable def secondTransition : ProbabilityTheory.Kernel (Bool × Bool) Bool where
  toFun p := transition p.2
  measurable' := measurable_of_countable _

instance : ProbabilityTheory.IsMarkovKernel secondTransition := ⟨fun p => by
  change IsProbabilityMeasure (transition p.2)
  infer_instance⟩

theorem kernel_three :
    ((fair.compProd transition).compProd secondTransition).map
      (fun p => (p.1.1,p.1.2,p.2)) = tripleMeaning := by
  rw [kernel_pair]
  have h : (fair.prod fair).compProd secondTransition = (fair.prod fair).prod fair := by
    apply Measure.ext
    intro E hE
    rw [Measure.compProd_apply hE, Measure.prod_apply hE]
    simp only [secondTransition, ProbabilityTheory.Kernel.coe_mk, transition_apply]
  rw [h]
  rfl


noncomputable def copied : Measure (Bool × Bool) := fair.map (fun b => (b,b))

/-- Copying and fresh sampling agree at each marginal. -/
theorem copied_marginals : copied.map Prod.fst = fair ∧ copied.map Prod.snd = fair := by
  constructor <;> rw [copied, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] <;>
    exact Measure.map_id

theorem fresh_marginals : (fair.prod fair).map Prod.fst = fair ∧
    (fair.prod fair).map Prod.snd = fair := by
  constructor
  · rw [Measure.map_fst_prod, measure_univ, one_smul]
  · rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- The complete law detects copying, even though both marginals agree. -/
theorem copied_not_fresh : copied ≠ fair.prod fair := by
  intro h
  have he := congrArg (fun m : Measure (Bool × Bool) => m {(false,true)}) h
  rw [pair_meaning] at he
  norm_num [copied, Measure.map_apply (measurable_of_countable _), fair, pairMeaning,
    Measure.dirac_apply', Set.preimage] at he
  exact (by norm_num : (4 : ℝ≥0∞) ≠ ∞) (ENNReal.inv_eq_zero.mp he.symm)

/-- Reusing the first bit as its own query noise forces false. -/
theorem reused_seed : fair.map (fun b => function b b) = Measure.dirac false := by
  have h : (fun b => function b b) = fun _ : Bool => false := by
    funext b; cases b <;> rfl
  rw [h]
  simp only [Measure.map_const, measure_univ, one_smul]

theorem reused_seed_wrong : fair.map (fun b => function b b) ≠ fair := by
  rw [reused_seed]
  intro h
  have he := congrArg (fun m : Measure Bool => m {true}) h
  norm_num [fair, Measure.dirac_apply'] at he
  exact (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (ENNReal.inv_eq_zero.mp he.symm)

end Applications.Probability.SamplerClient
