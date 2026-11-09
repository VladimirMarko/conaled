import Applications.Geometry.RadialSymmetry

/-! The imaginary radial momentum of the selected origin geodesic vanishes.
This identifies radial parallel transport along that geodesic, without choosing
an affine straight-line parameter. -/
noncomputable section
namespace RadialMetric
open Complex Set Metric
open scoped ComplexConjugate

def radialMomentum (p : Initial) (t : ℝ) : ℂ :=
  conj (boundedFlow p t).1 * (boundedFlow p t).2

theorem radialMomentum_derivative (p : Initial) {t : ℝ}
    (ht : t ∈ Ioo (-5/4 : ℝ) (5/4)) :
    HasDerivAt (radialMomentum p)
      ((normSq (boundedFlow p t).2 : ℂ)/2 - (radialMomentum p t)^2) t := by
  have hz := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t (boundedFlow_deriv p ht)
  have hw := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t (boundedFlow_deriv p ht)
  have hc := (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hz
  convert hc.mul hw using 1
  · rfl
  · change _ = conj ((boundedFlow p t).2 / 2) * (boundedFlow p t).2 +
      conj (boundedFlow p t).1 * (-conj (boundedFlow p t).1 * (boundedFlow p t).2^2)
    rw [normSq_eq_conj_mul_self]
    simp [radialMomentum,map_div₀,map_ofNat]
    ring

theorem angular_derivative (p : Initial) {t : ℝ}
    (ht : t ∈ Ioo (-5/4 : ℝ) (5/4)) :
    HasDerivAt (fun s => (radialMomentum p s).im)
      (-2*(radialMomentum p t).re*(radialMomentum p t).im) t := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (radialMomentum_derivative p ht)
  convert! h using 1
  change -2*(radialMomentum p t).re*(radialMomentum p t).im =
    ((normSq (boundedFlow p t).2 : ℂ)/2 - (radialMomentum p t)^2).im
  simp [pow_two,Complex.mul_im]
  ring

theorem radialMomentum_continuous (p : Initial) : Continuous (radialMomentum p) := by
  exact ((Complex.continuous_conj.comp (boundedFlow_continuous p).fst).mul
    (boundedFlow_continuous p).snd)

theorem radialMomentum_bound (p : Initial) (t : ℝ) : ‖radialMomentum p t‖ ≤ 1/16 := by
  obtain ⟨hz,hw⟩ := components_le (boundedFlow_mem p t)
  rw [radialMomentum,norm_mul,norm_conj]
  nlinarith [norm_nonneg (boundedFlow p t).1,norm_nonneg (boundedFlow p t).2]

theorem angular_zero (p : Initial) (hp : p.val.1 = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (radialMomentum p t).im = 0 := by
  have he : EqOn (fun t => (radialMomentum p t).im) (fun _ => (0 : ℝ)) (Icc (0 : ℝ) 1) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun t a => -2*(radialMomentum p t).re*a) (s := fun _ => univ) (K := 1/8)
    · intro t _
      apply LipschitzOnWith.of_dist_le_mul
      intro a _ b _
      rw [dist_eq_norm,dist_eq_norm,← mul_sub,norm_mul]
      have hb : ‖-2*(radialMomentum p t).re‖ ≤ (1/8 : ℝ) := by
        rw [norm_mul]
        norm_num
        have h := Complex.abs_re_le_norm (radialMomentum p t)
        have hn := radialMomentum_bound p t
        linarith
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg (a-b))
    · exact (Complex.continuous_im.comp (radialMomentum_continuous p)).continuousOn
    · intro t ht
      exact (angular_derivative p (by constructor <;> linarith [ht.1,ht.2])).hasDerivWithinAt
    · intros; trivial
    · exact continuousOn_const
    · intro t _
      simpa using (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt (s := Ici t)
    · intros; trivial
    · simp [radialMomentum,boundedFlow_initial,hp]
  exact he ht

def originParallel (p : Initial) (t : ℝ) (v : ℂ) : ℂ :=
  (Real.exp (-normSq (boundedFlow p t).1) : ℂ)*v

theorem originParallel_derivative (p : Initial) (hp : p.val.1 = 0) (v : ℂ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => originParallel p s v)
      (-gamma (boundedFlow p t).1 ((boundedFlow p t).2/2) (originParallel p t v)) t := by
  have hz := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t
    (boundedFlow_deriv p (by constructor <;> linarith [ht.1,ht.2]))
  have hn := Orbifold.DiskConnection.normSq_derivative hz
  have he := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hn.neg.exp).mul_const v
  have ha : ((radialMomentum p t).re : ℂ) = radialMomentum p t := by
    apply Complex.ext
    · simp
    · simp [angular_zero p hp ht]
  convert! he using 1
  change -gamma (boundedFlow p t).1 ((boundedFlow p t).2/2) (originParallel p t v) =
    ↑(Real.exp (-normSq (boundedFlow p t).1) * -(2*(conj (boundedFlow p t).1 * ((boundedFlow p t).2/2)).re)) * v
  have hr : 2*(conj (boundedFlow p t).1 * ((boundedFlow p t).2/2)).re = (radialMomentum p t).re := by
    simp [radialMomentum,mul_div_assoc]
    ring
  rw [hr]
  push_cast
  rw [ha]
  simp [gamma,originParallel,radialMomentum]
  ring

theorem originParallel_initial (p : Initial) (hp : p.val.1 = 0) (v : ℂ) :
    originParallel p 0 v = v := by
  simp [originParallel,boundedFlow_initial,hp]

theorem radialParallel_selected {y : ℂ} (hy : (0,y) ∈ branch.target) (v : ℂ) :
    let h := log_admitted hy
    let p : Initial := ⟨weight (0,originLog y),h.1⟩
    originParallel p 1 v = radialParallel y v := by
  dsimp only
  have he := expMap_actual (log_admitted hy)
  have hl := exp_log hy
  rw [he] at hl
  change (boundedFlow ⟨weight (0,originLog y),(log_admitted hy).1⟩ 1).1 = y at hl
  simp only [originParallel,hl,radialParallel]

/-- The selected radial solution is unique among parallel fields with that initial vector. -/
theorem originParallel_unique (p : Initial) (hp : p.val.1 = 0) (v : ℂ) (V : ℝ → ℂ)
    (hV : ContinuousOn V (Icc (0 : ℝ) 1))
    (hd : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt V
      (-gamma (boundedFlow p t).1 ((boundedFlow p t).2/2) (V t)) (Ici t) t)
    (h0 : V 0 = v) : EqOn V (fun t => originParallel p t v) (Icc (0 : ℝ) 1) := by
  have hc (t : ℝ) (w : ℂ) :
      -gamma (boundedFlow p t).1 ((boundedFlow p t).2/2) w = -radialMomentum p t*w := by
    simp only [gamma,radialMomentum]
    ring
  apply ODE_solution_unique_of_mem_Icc_right
    (v := fun t w => -gamma (boundedFlow p t).1 ((boundedFlow p t).2/2) w)
    (s := fun _ => univ) (K := 1/16)
  · intro t _
    apply LipschitzOnWith.of_dist_le_mul
    intro a _ b _
    rw [hc,hc,dist_eq_norm,dist_eq_norm,← mul_sub,norm_mul,norm_neg]
    exact mul_le_mul_of_nonneg_right (radialMomentum_bound p t) (norm_nonneg (a-b))
  · exact hV
  · exact hd
  · intros; trivial
  · have h : Continuous (fun t => originParallel p t v) := by
      unfold originParallel
      have hz := (boundedFlow_continuous p).fst
      fun_prop
    exact h.continuousOn
  · intro t ht
    exact (originParallel_derivative p hp v ⟨ht.1,ht.2.le⟩).hasDerivWithinAt
  · intros; trivial
  · rw [h0,originParallel_initial p hp]

end RadialMetric
