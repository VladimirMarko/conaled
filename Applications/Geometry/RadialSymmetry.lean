import Applications.Geometry.RadialDisplacement

/-! Flow symmetry follows from the actual field and uniqueness. Local branch
laws retain their source/target premises rather than assuming a global inverse. -/
noncomputable section
namespace RadialMetric
open Complex Set Metric
open scoped ComplexConjugate

theorem expMap_rest {x : ℂ} (hx : Admitted (x,0)) : expMap (x,0) = x := by
  let p : Initial := ⟨weight (x,0),hx.1⟩
  have hw : weightedField p.val = 0 := by simp [p,weight,weightedField]
  have he := boundedFlow_unique p (fun _ => p.val) continuousOn_const
    (fun t _ => by rw [hw]; exact hasDerivAt_const t p.val)
    (fun _ _ => (closedBall_subset_closedBall (by norm_num : (1/16 : ℝ) ≤ 1/4)) p.property) rfl
  rw [expMap_actual hx]
  change (boundedFlow p 1).1 = x
  have h := congrArg Prod.fst (he (show (1 : ℝ) ∈ Icc (-5/4) (5/4) by norm_num))
  simpa [p,weight] using h.symm

theorem displacement_right_unit {x : ℂ} (hx : DisplacementDomain (x,0)) :
    displacement (x,0) = x := by
  have hp := branch_source_actual hx.2
  simp only [originLog_zero,radialParallel,mul_zero] at hp
  change expMap (x,radialParallel x (originLog 0)) = x
  simp only [originLog_zero,radialParallel,mul_zero]
  exact expMap_rest hp

theorem weightedField_rotation (g : ℂ) (hg : normSq g = 1) (p : State) :
    weightedField (g • p) = g • weightedField p := by
  have hc : conj g * g = 1 := by rw [← normSq_eq_conj_mul_self,hg]; norm_num
  apply Prod.ext
  · simp [weightedField,smul_eq_mul]; ring
  · change -conj (g*p.1)*(g*p.2)^2 = g*(-conj p.1*p.2^2)
    calc
      _ = (conj g*g)*(g*(-conj p.1*p.2^2)) := by simp only [map_mul]; ring
      _ = _ := by rw [hc,one_mul]

theorem unit_norm (g : ℂ) (hg : normSq g = 1) : ‖g‖ = 1 := by
  rw [normSq_eq_norm_sq] at hg
  nlinarith [norm_nonneg g]

def rotateInitial (g : ℂ) (hg : normSq g = 1) (p : Initial) : Initial :=
  ⟨g • p.val, by
    rw [mem_closedBall,dist_zero_right,norm_smul,unit_norm g hg,one_mul]
    simpa only [Initial, mem_closedBall, dist_zero_right] using p.property⟩

theorem boundedFlow_rotation (g : ℂ) (hg : normSq g = 1) (p : Initial)
    {t : ℝ} (ht : t ∈ Icc (-5/4 : ℝ) (5/4)) :
    boundedFlow (rotateInitial g hg p) t = g • boundedFlow p t := by
  have he := boundedFlow_unique (rotateInitial g hg p) (fun t => g • boundedFlow p t)
    ((boundedFlow_continuous p).const_smul g).continuousOn
    (fun t ht => by
      rw [weightedField_rotation g hg]
      exact (boundedFlow_deriv p ht).const_smul g)
    (fun t _ => by
      rw [mem_closedBall,dist_zero_right,norm_smul,unit_norm g hg,one_mul]
      simpa using boundedFlow_mem p t)
    (by rw [boundedFlow_initial]; rfl)
  exact (he ht).symm

theorem weight_rotation (g : ℂ) (p : State) : weight (g • p) = g • weight p := by
  ext <;> simp [weight,smul_eq_mul] <;> ring

theorem expMap_rotation (g : ℂ) (hg : normSq g = 1) (p : State)
    (hp : Admitted p) (hq : Admitted (g • p)) : expMap (g • p) = g * expMap p := by
  have he : rotateInitial g hg ⟨weight p,hp.1⟩ = ⟨weight (g • p),hq.1⟩ := by
    apply Subtype.ext
    exact (weight_rotation g p).symm
  have h := boundedFlow_rotation g hg ⟨weight p,hp.1⟩ (t := 1) (by norm_num)
  rw [he] at h
  rw [expMap_actual hp,expMap_actual hq]
  exact congrArg Prod.fst h

/-- The rotated inverse input must remain on the same local branch. -/
def RotationDomain (g : ℂ) (p : State) : Prop :=
  DisplacementDomain p ∧ DisplacementDomain (g • p) ∧
    (0,g * originLog p.2) ∈ branch.source

theorem originLog_rotation (g : ℂ) (hg : normSq g = 1) {y : ℂ}
    (hy : (0,y) ∈ branch.target) (hr : (0,g * originLog y) ∈ branch.source) :
    originLog (g*y) = g * originLog y := by
  have he := expMap_rotation g hg (0,originLog y) (log_admitted hy)
    (by simpa only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_zero] using branch_source_actual hr)
  have hz : expMap (0,g*originLog y) = g*y := by
    simpa only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_zero, originLog, exp_log hy] using he
  have hl := log_exp hr
  rw [hz] at hl
  exact hl

theorem radialParallel_rotation (g : ℂ) (hg : normSq g = 1) (x v : ℂ) :
    radialParallel (g*x) (g*v) = g*radialParallel x v := by
  simp only [radialParallel, normSq_mul, hg, one_mul]
  ring

theorem displacement_rotation (g : ℂ) (hg : normSq g = 1) {p : State}
    (hp : RotationDomain g p) : displacement (g • p) = g*displacement p := by
  have hl := originLog_rotation g hg hp.1.1 hp.2.2
  have hv : (g • p).1 = g*p.1 := rfl
  have hw : (g • p).2 = g*p.2 := rfl
  have he : ((g • p).1, radialParallel (g • p).1 (originLog (g • p).2)) =
      g • (p.1,radialParallel p.1 (originLog p.2)) := by
    rw [hv,hw,hl,radialParallel_rotation g hg]
    rfl
  have h := expMap_rotation g hg (p.1,radialParallel p.1 (originLog p.2))
    (branch_source_actual hp.1.2) (by rw [← he]; exact branch_source_actual hp.2.1.2)
  change expMap ((g • p).1,radialParallel (g • p).1 (originLog (g • p).2)) = _
  rw [he]
  exact h

open scoped Topology in
theorem rotation_domain_near_zero (g : ℂ) : ∀ᶠ p in 𝓝 (0 : State), RotationDomain g p := by
  have hc : ContinuousAt (fun p : State => g • p) 0 := by fun_prop
  have hrot : ∀ᶠ p in 𝓝 (0 : State), DisplacementDomain (g • p) := by
    apply hc.tendsto.eventually
    simpa only [smul_zero] using displacement_domain_near_zero
  have hi : ContinuousAt (fun p : State => ((0 : ℂ),g*originLog p.2)) 0 :=
    continuousAt_const.prodMk (continuousAt_const.mul (originLog_smooth.continuousAt.comp (f := fun p : State => p.2) (x := (0 : State)) continuousAt_snd))
  have hin : ∀ᶠ p in 𝓝 (0 : State), (0,g*originLog p.2) ∈ branch.source := by
    apply hi.tendsto.eventually
    simp only [Prod.snd_zero,originLog_zero,mul_zero]
    exact branch_neighborhoods.1
  filter_upwards [displacement_domain_near_zero,hrot,hin] with p hp hq hr
  exact ⟨hp,hq,hr⟩

/-- A common local domain for every chosen C4 alignment. -/
def C4Domain (p : State) : Prop :=
  ∀ g : Orbifolds.QuarterTurn.C4, RotationDomain (g.val : ℂ) p

open scoped Topology in
theorem c4_domain_near_zero : ∀ᶠ p in 𝓝 (0 : State), C4Domain p := by
  exact Filter.eventually_all.mpr (fun g => rotation_domain_near_zero (g.val : ℂ))

theorem displacement_c4 (g : Orbifolds.QuarterTurn.C4) {p : State} (hp : C4Domain p) :
    displacement ((g.val : ℂ) • p) = (g.val : ℂ)*displacement p :=
  displacement_rotation _ (c4_normSq g) (hp g)

end RadialMetric
