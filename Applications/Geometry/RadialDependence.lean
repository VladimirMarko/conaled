import Applications.Geometry.RadialVariation

/-! Identification of the implicit integral-equation family with the bounded
selected Picard flow. All comparisons retain the actual coordinate-ball bound. -/
noncomputable section
namespace RadialMetric.Variation
open Set Metric
open scoped Topology

def extendPaths (α : Paths) (t : ℝ) : State := (extend α.1 t,extend α.2 t)

theorem extendPaths_bound (α : Paths) (t : ℝ) : ‖extendPaths α t‖ ≤ ‖α‖ := by
  rw [norm_prod_le_iff]
  exact ⟨(α.1.norm_coe_le_norm _).trans (norm_fst_le α),
    (α.2.norm_coe_le_norm _).trans (norm_snd_le α)⟩

def integralPath (p : State) (t : ℝ) : State :=
  (p.1 + (1/2 : ℝ) • (∫ s in (0 : ℝ)..t, extend (solutionPaths p).2 s),
   p.2 - ∫ s in (0 : ℝ)..t,
     extend (conjugate (solutionPaths p).1 * (solutionPaths p).2 ^ 2) s)

theorem integralPath_initial (p : State) : integralPath p 0 = p := by
  simp [integralPath]

theorem integralPath_eq {p : State} (hp : residual (p,solutionPaths p) = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    integralPath p t = extendPaths (solutionPaths p) t := by
  have hz := congrArg (fun q : Paths => q.1 ⟨t,ht⟩) hp
  have hw := congrArg (fun q : Paths => q.2 ⟨t,ht⟩) hp
  simp [residual, linearResidual, constant, integralCLM_apply, smul_eq_mul] at hz hw
  have hproj : projIcc 0 1 (by norm_num) t = ⟨t,ht⟩ := projIcc_of_mem _ ht
  apply Prod.ext
  · change p.1 + (1/2 : ℝ) • (∫ s in (0 : ℝ)..t, extend (solutionPaths p).2 s) =
      (solutionPaths p).1 (projIcc 0 1 (by norm_num) t)
    rw [hproj]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    linear_combination -hz
  · change p.2 - (∫ s in (0 : ℝ)..t,
        extend (conjugate (solutionPaths p).1 * (solutionPaths p).2 ^ 2) s) =
      (solutionPaths p).2 (projIcc 0 1 (by norm_num) t)
    rw [hproj]
    linear_combination -hw

theorem integralPath_deriv (p : State) (t : ℝ) :
    HasDerivAt (integralPath p) (weightedField (extendPaths (solutionPaths p) t)) t := by
  have primitive (f : Curve) :
      HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, extend f s) (extend f t) t :=
    intervalIntegral.integral_hasDerivAt_right ((continuous_extend f).intervalIntegrable 0 t)
      (continuous_extend f).aestronglyMeasurable.stronglyMeasurableAtFilter
      (continuous_extend f).continuousAt
  convert ((hasDerivAt_const t p.1).add ((primitive (solutionPaths p).2).const_smul (1/2 : ℝ))).prodMk
    ((hasDerivAt_const t p.2).sub (primitive
      (conjugate (solutionPaths p).1 * (solutionPaths p).2 ^ 2))) using 1
  · rfl
  · ext <;> simp [weightedField, extendPaths, extend, conjugate, smul_eq_mul,
      Complex.real_smul] <;> ring

theorem integralPath_continuous (p : State) : Continuous (integralPath p) :=
  continuous_iff_continuousAt.mpr (fun t => (integralPath_deriv p t).continuousAt)

theorem paths_admitted : ∀ᶠ p in 𝓝 (0 : State),
    p ∈ Initial ∧ ‖solutionPaths p‖ < (1/4 : ℝ) ∧ residual (p,solutionPaths p) = 0 := by
  have hi : ∀ᶠ p in 𝓝 (0 : State), p ∈ Initial := closedBall_mem_nhds 0 (by norm_num)
  have hn : ∀ᶠ p in 𝓝 (0 : State), ‖solutionPaths p‖ < (1/4 : ℝ) := by
    have h := solutionPaths_smooth.continuousAt.norm
    have h0 : ‖solutionPaths 0‖ < (1/4 : ℝ) := by rw [solutionPaths_zero]; norm_num
    exact h.eventually (gt_mem_nhds h0)
  filter_upwards [hi,hn,solutionPaths_equation] with p hi hn he
  exact ⟨hi,hn,he⟩

theorem integralPath_eq_bounded {p : State} (hi : p ∈ Initial)
    (hn : ‖solutionPaths p‖ < (1/4 : ℝ)) (he : residual (p,solutionPaths p) = 0) :
    EqOn (integralPath p) (boundedFlow ⟨p,hi⟩) (Icc (0 : ℝ) 1) := by
  apply ODE_solution_unique_of_mem_Icc_right (v := fun _ => weightedField)
    (s := fun _ => closedBall 0 (1/4 : ℝ)) (K := 1/2)
    (fun _ _ => weightedField_lipschitz) (integralPath_continuous p).continuousOn
  · intro t ht
    rw [integralPath_eq he ⟨ht.1,ht.2.le⟩]
    exact (integralPath_deriv p t).hasDerivWithinAt
  · intro t ht
    rw [integralPath_eq he ⟨ht.1,ht.2.le⟩, mem_closedBall, dist_zero_right]
    exact (extendPaths_bound _ _).trans hn.le
  · exact (boundedFlow_continuous ⟨p,hi⟩).continuousOn
  · intro t ht
    exact (boundedFlow_deriv ⟨p,hi⟩ (by constructor <;> linarith [ht.1,ht.2])).hasDerivWithinAt
  · intro t ht
    exact boundedFlow_mem ⟨p,hi⟩ t
  · rw [integralPath_initial, boundedFlow_initial]

end RadialMetric.Variation
