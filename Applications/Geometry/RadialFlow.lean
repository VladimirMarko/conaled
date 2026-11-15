import Applications.Geometry.RadialMetric
import Mathlib.Analysis.ODE.ExistUnique

/-! A bounded selected flow for the fixed radial metric. Initial-data
smoothness and local displacement require further proofs beyond this module. -/
noncomputable section
namespace RadialMetric
open Complex Metric Set
open scoped NNReal ComplexConjugate

abbrev State := ℂ × ℂ

lemma components_le {p : State} (hp : p ∈ closedBall 0 (1/4 : ℝ)) :
    ‖p.1‖ ≤ 1/4 ∧ ‖p.2‖ ≤ 1/4 := by
  simpa only [mem_closedBall, dist_zero_right, norm_prod_le_iff] using hp

lemma weightedField_norm {p : State} (hp : p ∈ closedBall 0 (1/4 : ℝ)) :
    ‖weightedField p‖ ≤ 1/8 := by
  obtain ⟨hz,hw⟩ := components_le hp
  rw [norm_prod_le_iff]
  constructor
  · change ‖p.2 / (2 : ℂ)‖ ≤ _
    rw [norm_div]
    norm_num
    linarith
  · change ‖-conj p.1 * p.2 ^ 2‖ ≤ _
    rw [norm_mul, norm_neg, norm_conj, norm_pow]
    calc
      ‖p.1‖ * ‖p.2‖ ^ 2 ≤ (1/4 : ℝ) * (1/4)^2 := by gcongr
      _ ≤ 1/8 := by norm_num

lemma cubic_difference {p q : State}
    (hp : p ∈ closedBall 0 (1/4 : ℝ)) (hq : q ∈ closedBall 0 (1/4 : ℝ)) :
    ‖-conj p.1 * p.2^2 - (-conj q.1 * q.2^2)‖ ≤ (3/16 : ℝ) * ‖p-q‖ := by
  obtain ⟨hpz,hpw⟩ := components_le hp
  obtain ⟨hqz,hqw⟩ := components_le hq
  have hz : ‖p.1-q.1‖ ≤ ‖p-q‖ := norm_fst_le (p-q)
  have hw : ‖p.2-q.2‖ ≤ ‖p-q‖ := norm_snd_le (p-q)
  have alg : -conj p.1 * p.2^2 - (-conj q.1 * q.2^2) =
      -(conj (p.1-q.1)*p.2*p.2 + conj q.1*(p.2-q.2)*p.2 +
        conj q.1*q.2*(p.2-q.2)) := by simp only [map_sub]; ring
  rw [alg, norm_neg]
  calc
    _ ≤ ‖conj (p.1-q.1)*p.2*p.2 + conj q.1*(p.2-q.2)*p.2‖ +
        ‖conj q.1*q.2*(p.2-q.2)‖ := norm_add_le _ _
    _ ≤ (‖conj (p.1-q.1)*p.2*p.2‖ + ‖conj q.1*(p.2-q.2)*p.2‖) +
        ‖conj q.1*q.2*(p.2-q.2)‖ := by gcongr; exact norm_add_le _ _
    _ = (‖p.1-q.1‖*‖p.2‖*‖p.2‖ + ‖q.1‖*‖p.2-q.2‖*‖p.2‖) +
        ‖q.1‖*‖q.2‖*‖p.2-q.2‖ := by simp only [norm_mul, norm_conj]
    _ ≤ (‖p-q‖*(1/4)*(1/4) + (1/4)*‖p-q‖*(1/4)) +
        (1/4)*(1/4)*‖p-q‖ := by gcongr
    _ = _ := by ring

lemma weightedField_lipschitz : LipschitzOnWith (1/2 : ℝ≥0) weightedField
    (closedBall (0 : State) (1/4 : ℝ)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(p.2/2-q.2/2, -conj p.1*p.2^2-(-conj q.1*q.2^2))‖ ≤ _
  rw [norm_prod_le_iff]
  constructor
  · rw [← sub_div, norm_div]
    have h := norm_snd_le (p-q)
    norm_num at *
    linarith
  · have h := cubic_difference hp hq
    norm_num at *
    nlinarith [norm_nonneg (p-q)]

def initialTime : Icc (-5/4 : ℝ) (5/4) := ⟨0, by norm_num⟩

theorem picard : IsPicardLindelof (fun _ => weightedField) initialTime (0 : State)
    (1/4) (1/16) (1/8) (1/2) where
  lipschitzOnWith := fun _ _ => weightedField_lipschitz
  continuousOn := fun _ _ => continuousOn_const
  norm_le := by intro t ht p hp; exact weightedField_norm hp
  mul_max_le := by norm_num [initialTime]

abbrev Initial := closedBall (0 : State) (1/16 : ℝ)

/-- Retain the bounded fixed-point witness rather than selecting an unrelated ODE solution. -/
def boundedCurve (p : Initial) : ODE.FunSpace initialTime (0 : State) (1/16) (1/8) :=
  (ODE.FunSpace.exists_isFixedPt_next picard p.property).choose

theorem boundedCurve_fixed (p : Initial) :
    Function.IsFixedPt (ODE.FunSpace.next picard p.property) (boundedCurve p) :=
  (ODE.FunSpace.exists_isFixedPt_next picard p.property).choose_spec

def boundedFlow (p : Initial) : ℝ → State := (boundedCurve p).compProj

theorem boundedFlow_initial (p : Initial) : boundedFlow p 0 = p.val := by
  change (boundedCurve p).compProj initialTime = p.val
  rw [ODE.FunSpace.compProj_val, ← boundedCurve_fixed p]
  exact ODE.FunSpace.next_apply₀ picard p.property (boundedCurve p)

theorem boundedFlow_mem (p : Initial) (t : ℝ) :
    boundedFlow p t ∈ closedBall (0 : State) (1/4 : ℝ) :=
  (boundedCurve p).compProj_mem_closedBall picard.mul_max_le

theorem boundedFlow_continuous (p : Initial) : Continuous (boundedFlow p) :=
  (boundedCurve p).continuous_compProj

theorem boundedFlow_derivWithin (p : Initial) {t : ℝ} (ht : t ∈ Icc (-5/4 : ℝ) (5/4)) :
    HasDerivWithinAt (boundedFlow p) (weightedField (boundedFlow p t))
      (Icc (-5/4 : ℝ) (5/4)) t := by
  apply ODE.hasDerivWithinAt_picard_Icc initialTime.property picard.continuousOn_uncurry
    (boundedFlow_continuous p).continuousOn (fun t _ => boundedFlow_mem p t)
    p.val ht |>.congr_of_mem _ ht
  intro t' ht'
  change (boundedCurve p).compProj t' = _
  nth_rw 1 [← boundedCurve_fixed p]
  rw [ODE.FunSpace.compProj_of_mem ht']
  exact ODE.FunSpace.next_apply picard p.property (boundedCurve p)

theorem boundedFlow_deriv (p : Initial) {t : ℝ} (ht : t ∈ Ioo (-5/4 : ℝ) (5/4)) :
    HasDerivAt (boundedFlow p) (weightedField (boundedFlow p t)) t :=
  (boundedFlow_derivWithin p ⟨ht.1.le,ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Time one is inside the admitted derivative interval, not only its endpoint. -/
theorem boundedFlow_time_one (p : Initial) :
    HasDerivAt (boundedFlow p) (weightedField (boundedFlow p 1)) 1 ∧
    ‖boundedFlow p 1‖ ≤ 1/4 :=
  ⟨boundedFlow_deriv p (by norm_num), by simpa using boundedFlow_mem p 1⟩

theorem boundedFlow_unique (p : Initial) (β : ℝ → State)
    (hc : ContinuousOn β (Icc (-5/4 : ℝ) (5/4)))
    (hd : ∀ t ∈ Ioo (-5/4 : ℝ) (5/4), HasDerivAt β (weightedField (β t)) t)
    (hm : ∀ t ∈ Ioo (-5/4 : ℝ) (5/4), β t ∈ closedBall 0 (1/4 : ℝ))
    (h0 : β 0 = p.val) : EqOn β (boundedFlow p) (Icc (-5/4 : ℝ) (5/4)) := by
  apply ODE_solution_unique_of_mem_Icc (v := fun _ => weightedField)
    (s := fun _ => closedBall 0 (1/4 : ℝ)) (K := 1/2)
    (fun _ _ => weightedField_lipschitz) (t₀ := 0) (by norm_num)
    hc hd hm (boundedFlow_continuous p).continuousOn
    (fun _ ht => boundedFlow_deriv p ht) (fun t _ => boundedFlow_mem p t)
  rw [h0, boundedFlow_initial]

def unweight (p : State) : State := (p.1,p.2/2)

def geodesicFlow (p : Initial) (t : ℝ) : State := unweight (boundedFlow p t)

theorem geodesicFlow_initial (p : Initial) : geodesicFlow p 0 = unweight p.val := by
  rw [geodesicFlow, boundedFlow_initial]

theorem geodesicFlow_deriv (p : Initial) {t : ℝ} (ht : t ∈ Ioo (-5/4 : ℝ) (5/4)) :
    HasDerivAt (geodesicFlow p) (field (geodesicFlow p t)) t := by
  have h := boundedFlow_deriv p ht
  have hz := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t h
  have hw := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t h
  convert hz.prodMk (hw.div_const 2) using 1
  · rfl
  · ext <;> simp [geodesicFlow, unweight, field, weightedField, gamma] <;> ring

/-- The actual endpoint of the bounded selected solution, not a formal jet. -/
def endpoint (p : Initial) : ℂ := (geodesicFlow p 1).1

theorem initial_neighborhood : ball (0 : State) (1/16 : ℝ) ⊆ Initial :=
  ball_subset_closedBall

theorem initial_nonempty : (ball (0 : State) (1/16 : ℝ)).Nonempty :=
  ⟨0, by simp⟩

end RadialMetric
