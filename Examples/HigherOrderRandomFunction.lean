import Applications.Probability.RandomFunction
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Checked joint-law and nonlinear controls for #370. -/

open MeasureTheory
open scoped ENNReal
open Applications.Probability.QuasiBorel

namespace Examples.HigherOrderRandomFunction

/-- Independent meaning, fixed without using the higher-order evaluator. -/
noncomputable def sharedMeaning : Measure (ℝ × ℝ) :=
  coefficientLaw.map (fun e => (e.2, e.1 + e.2))
noncomputable def freshMeaning : Measure (ℝ × ℝ) :=
  (coefficientLaw.prod coefficientLaw).map (fun e => (e.1.2, e.2.1 + e.2.2))

theorem shared_interpretation :
    @Measure.map functionSpace (ℝ × ℝ) (sigma functionSpace) _ (observe 0 1)
      (law coefficientLaw affine) = sharedMeaning := by
  simpa [sharedMeaning] using shared_law coefficientLaw 0 1

theorem fresh_interpretation :
    @Measure.map (prod functionSpace functionSpace) (ℝ × ℝ)
      (sigma (prod functionSpace functionSpace)) _ (observeIndependent 0 1)
      (law (coefficientLaw.prod coefficientLaw) independentFamily) = freshMeaning := by
  simpa [freshMeaning] using independent_law coefficientLaw 0 1

theorem uniform01_open : uniform01 = volume.restrict (Set.Ioo 0 1) :=
  restrict_Ioo_eq_restrict_Icc.symm

theorem triangle_mass (b : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    coefficientLaw {p | p.1 + p.2 < b} = ENNReal.ofReal (b ^ 2 / 2) := by
  rw [coefficientLaw, uniform01_open, Measure.prod_restrict,
    Measure.restrict_apply (by measurability)]
  have hs : {p : ℝ × ℝ | p.1 + p.2 < b} ∩ (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) =
      regionBetween (fun _ : ℝ => 0) (fun a => b - a) (Set.Ioo 0 b) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Ioo,
      regionBetween]
    constructor <;> rintro ⟨h, h'⟩
    · rcases h' with ⟨⟨ha, ha'⟩, ⟨hc, hc'⟩⟩
      exact ⟨⟨ha, by linarith⟩, hc, by linarith⟩
    · rcases h with ⟨ha, ha'⟩
      rcases h' with ⟨hc, hc'⟩
      exact ⟨by linarith, ⟨ha, by linarith [hb.2]⟩, hc, by linarith [hb.2]⟩
  rw [hs, volume_regionBetween_eq_integral]
  · congr 1
    simp only [Pi.sub_apply, sub_zero]
    rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hb.1,
      intervalIntegral.integral_sub (f := fun _ : ℝ => b) (g := fun x : ℝ => x)
        (continuous_const.intervalIntegrable _ _)
        (continuous_id.intervalIntegrable _ _)]
    simp [integral_id]
    ring
  · exact continuous_const.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  · exact (continuous_const.sub continuous_id).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  · exact measurableSet_Ioo
  · intro x hx; linarith [hx.2]

theorem coefficients_mem : ∀ᵐ e ∂coefficientLaw,
    e.1 ∈ Set.Icc (0 : ℝ) 1 ∧ e.2 ∈ Set.Icc (0 : ℝ) 1 := by
  change ∀ᵐ e ∂uniform01.prod uniform01, _
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))] with a ha
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1))] with b hb
  exact ⟨ha, hb⟩

theorem shared_event : sharedMeaning {p | p.2 < p.1} = 0 := by
  rw [sharedMeaning, Measure.map_apply (by fun_prop) (by measurability)]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [coefficients_mem] with e he
  change ¬ e.1 + e.2 < e.2
  linarith [he.1.1]

theorem fresh_event : freshMeaning {p | p.2 < p.1} = 1 / 6 := by
  rw [freshMeaning, Measure.map_apply (by fun_prop) (by measurability),
    Measure.prod_apply (by measurability)]
  have he : (fun e : ℝ × ℝ => coefficientLaw {p | p.1 + p.2 < e.2}) =ᵐ[coefficientLaw]
      (fun e => ENNReal.ofReal (e.2 ^ 2 / 2)) := by
    filter_upwards [coefficients_mem] with e he
    exact triangle_mass e.2 he.2
  change (∫⁻ e, coefficientLaw {p | p.1 + p.2 < e.2} ∂coefficientLaw) = _
  rw [lintegral_congr_ae he, coefficientLaw, lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [uniform01, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [← restrict_Ioc_eq_restrict_Icc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_div, integral_pow]
    norm_num [ENNReal.ofReal_div_of_pos]
  · exact (by fun_prop : Continuous (fun x : ℝ => x ^ 2 / 2)).integrableOn_Icc
  · exact Filter.Eventually.of_forall fun x => by positivity

theorem joint_laws_differ : sharedMeaning ≠ freshMeaning := by
  intro h
  have he := congrArg (fun μ : Measure (ℝ × ℝ) => μ {p | p.2 < p.1}) h
  rw [shared_event, fresh_event] at he
  exact (ENNReal.inv_ne_zero.mpr (by simp) : (6 : ℝ≥0∞)⁻¹ ≠ 0) (by simpa using he.symm)

theorem shared_first : sharedMeaning.map Prod.fst = uniform01 := by
  rw [sharedMeaning, Measure.map_map measurable_fst (by fun_prop)]
  change coefficientLaw.map Prod.snd = _
  rw [coefficientLaw, Measure.map_snd_prod, measure_univ, one_smul]

theorem same_first_marginal : freshMeaning.map Prod.fst = sharedMeaning.map Prod.fst := by
  rw [shared_first, freshMeaning, Measure.map_map measurable_fst (by fun_prop)]
  change (coefficientLaw.prod coefficientLaw).map (Prod.snd ∘ Prod.fst) = _
  rw [← Measure.map_map measurable_snd measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul, coefficientLaw, Measure.map_snd_prod, measure_univ, one_smul]

theorem same_second_marginal : freshMeaning.map Prod.snd = sharedMeaning.map Prod.snd := by
  rw [freshMeaning, sharedMeaning, Measure.map_map measurable_snd (by fun_prop),
    Measure.map_map measurable_snd (by fun_prop)]
  change (coefficientLaw.prod coefficientLaw).map ((fun e : ℝ × ℝ => e.1 + e.2) ∘ Prod.snd) = _
  rw [← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod,
    measure_univ, one_smul]
  rfl

def squareOutputs (p : ℝ × ℝ) : ℝ × ℝ := (p.1^2, p.2^2)

/-- The selected event is preserved by squaring only on nonnegative outputs. -/
theorem square_event (μ : Measure (ℝ × ℝ))
    (h : ∀ᵐ p ∂μ, 0 ≤ p.1 ∧ 0 ≤ p.2) :
    μ.map squareOutputs {p | p.2 < p.1} = μ {p | p.2 < p.1} := by
  rw [Measure.map_apply (by unfold squareOutputs; fun_prop) (by measurability)]
  apply measure_congr
  filter_upwards [h] with p hp
  exact propext (sq_lt_sq₀ hp.2 hp.1)

theorem nonlinear_shared_event : sharedMeaning.map squareOutputs {p | p.2 < p.1} = 0 := by
  rw [square_event, shared_event]
  unfold sharedMeaning
  apply (ae_map_iff (by fun_prop) (by measurability)).mpr
  filter_upwards [coefficients_mem] with e he
  exact ⟨he.2.1, add_nonneg he.1.1 he.2.1⟩

theorem nonlinear_fresh_event : freshMeaning.map squareOutputs {p | p.2 < p.1} = 1 / 6 := by
  rw [square_event, fresh_event]
  unfold freshMeaning
  apply (ae_map_iff (by fun_prop) (by measurability)).mpr
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [coefficients_mem] with e he
  filter_upwards [coefficients_mem] with e' he'
  exact ⟨he.2.1, add_nonneg he'.1.1 he'.2.1⟩

/-- The nonlinear higher-order consumer has exactly the squared independent meaning. -/
theorem nonlinear_shared_interpretation :
    @Measure.map functionSpace (ℝ × ℝ) (sigma functionSpace) _ (observe 0 1)
      (law coefficientLaw (squareFunction.comp affine)) = sharedMeaning.map squareOutputs := by
  rw [law_observe, sharedMeaning, Measure.map_map (by unfold squareOutputs; fun_prop) (by fun_prop)]
  congr 1
  funext e
  simp [observe, Hom.comp, squareOutputs]

/-- Independence is kept through squaring each separately sampled function. -/
theorem nonlinear_fresh_interpretation :
    @Measure.map (prod functionSpace functionSpace) (ℝ × ℝ)
      (sigma (prod functionSpace functionSpace)) _
      ((observeIndependent 0 1).comp
        (pair (squareFunction.comp (fst _ _)) (squareFunction.comp (snd _ _))))
      (law (coefficientLaw.prod coefficientLaw) independentFamily) = freshMeaning.map squareOutputs := by
  rw [law_observe, freshMeaning, Measure.map_map (by unfold squareOutputs; fun_prop) (by fun_prop)]
  congr 1
  funext e
  simp [observeIndependent, Hom.comp, pair, fst, snd, independentFamily, measurableHom, squareOutputs]

/-- Three observations use the repaired distribution on the same independent meaning. -/
theorem repaired_three_observations :
    @Measure.map functionSpace (ℝ × ℝ × ℝ) (sigma functionSpace) _ (observeThree 0 1 2)
      (law (coefficientLaw.map repair) polynomial) =
      coefficientLaw.map (fun e => (e.2^2, (e.1 + e.2)^2, (2 * e.1 + e.2)^2)) := by
  rw [repaired_law, nonlinear_law]
  simp [mul_comm]

/-- Admission includes jointly varying arguments, not only fixed evaluations. -/
example (a b x : ℝ → ℝ) (ha : Measurable a) (hb : Measurable b) (hx : Measurable x) :
    Measurable (fun t => squareFunction (affine (a t, b t)) (x t)) :=
  (squareFunction.comp affine).preserves (ha.prodMk hb) id measurable_id x hx

/-- Dropping the nonnegative hypothesis in square_event would be false. -/
example : (squareOutputs (-2, 1)).2 < (squareOutputs (-2, 1)).1 ∧ ¬ (1 : ℝ) < -2 := by
  norm_num [squareOutputs]

/-- Squaring is admitted on the unchanged function carrier. -/
example : squareFunction (affine (1, 0)) 2 = 4 := by norm_num

/-- An affine value cannot realize the nonlinear function at all three selected inputs. -/
theorem square_not_affine : ¬ ∃ a b : ℝ,
    affine (a, b) 0 = 0 ∧ affine (a, b) 1 = 1 ∧ affine (a, b) 2 = 4 := by
  rintro ⟨a, b, h0, h1, h2⟩
  simp only [affine_apply] at *
  nlinarith

/-- The polynomial repair preserves the entire function, for arbitrary inputs. -/
example (e : ℝ × ℝ) (x : ℝ) : polynomial (repair e) x = (affine e x)^2 := by
  have h := congrArg (fun f : Hom coefficients functionSpace => f e x) repair_meaning
  exact h

/-- The selected sample is retained separately from its output law. -/
example (e : ℝ × ℝ) : (e, squareFunction (affine e)).1 = e := rfl

/-- Genuine repaired coefficients are correlated. -/
theorem repair_relation (e : ℝ × ℝ) :
    (repair e).2.1 ^ 2 = 4 * (repair e).1 * (repair e).2.2 := by
  change (2 * e.1 * e.2)^2 = 4 * e.1^2 * e.2^2
  ring

/-- Mixing individually attainable coefficient coordinates need not preserve that relation. -/
example : ¬ (0 : ℝ)^2 = 4 * (repair (1, 0)).1 * (repair (0, 1)).2.2 := by
  norm_num [repair, measurableHom]

end Examples.HigherOrderRandomFunction
