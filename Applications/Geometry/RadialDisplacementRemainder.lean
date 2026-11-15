import Applications.Geometry.RadialLogRemainder

/-! Remainder estimates for the composed local displacement, including the
inverse exponential and radial parallel factor. -/
noncomputable section
namespace RadialMetric
open Set Metric Complex Asymptotics
open scoped Topology ComplexConjugate

def parallelFactor (p : State) : ℂ := Real.exp (-normSq p.1)

theorem first_bigO : (fun p : State => p.1) =O[𝓝 0] (fun p => ‖p‖) :=
  ((ContinuousLinearMap.fst ℝ ℂ ℂ).isBigO_id _).norm_right

theorem second_bigO : (fun p : State => p.2) =O[𝓝 0] (fun p => ‖p‖) :=
  ((ContinuousLinearMap.snd ℝ ℂ ℂ).isBigO_id _).norm_right

theorem normSq_first_bigO : (fun p : State => normSq p.1) =O[𝓝 0] (fun p => ‖p‖^2) := by
  simpa only [normSq_eq_norm_sq] using first_bigO.norm_left.pow 2

theorem parallelFactor_bigO : parallelFactor =O[𝓝 (0 : State)] (fun _ => (1 : ℝ)) := by
  have h : Continuous parallelFactor := by unfold parallelFactor; fun_prop
  exact (h.tendsto 0).isBigO_one ℝ

theorem parallelFactor_remainder : (fun p : State => parallelFactor p-1+(normSq p.1 : ℂ))
    =O[𝓝 0] (fun p => ‖p‖^4) := by
  have ht : Filter.Tendsto (fun p : State => -normSq p.1) (𝓝 0) (𝓝 0) := by
    have h : Continuous (fun p : State => -normSq p.1) := by fun_prop
    simpa using h.tendsto 0
  have he : (fun p : State => Real.exp (-normSq p.1)-1+normSq p.1)
      =O[𝓝 0] (fun p => ‖p‖^4) := by
    have h := (Real.exp_sub_sum_range_isBigO_pow 2).comp_tendsto ht
    have hn := (normSq_first_bigO.neg_left).pow 2
    have hh := h.trans hn
    convert hh using 1
    · funext p; simp [Finset.sum_range_succ]; ring
    · funext p; ring
  have hc := (Complex.ofRealCLM.isBigO_comp
    (fun p : State => Real.exp (-normSq p.1)-1+normSq p.1) _).trans he
  apply hc.congr_left
  intro p
  simp [parallelFactor]

theorem parallelFactor_deviation : (fun p => parallelFactor p-1)
    =O[𝓝 (0 : State)] (fun p => ‖p‖^2) := by
  have he := parallelFactor_remainder.trans
    (isLittleO_norm_pow_norm_pow (E' := State) (by norm_num : 2 < 4)).isBigO
  have hn := (Complex.ofRealCLM.isBigO_comp (fun p : State => normSq p.1) _).trans normSq_first_bigO
  apply (he.sub hn).congr_left
  intro p
  change (parallelFactor p-1+(normSq p.1 : ℂ))-(normSq p.1 : ℂ) = parallelFactor p-1
  ring

theorem log_second_remainder : (fun p : State => originLog p.2-p.2-conj p.2*p.2^2/3)
    =O[𝓝 0] (fun p => ‖p‖^5) := by
  exact (originLog_remainder.comp_tendsto continuous_snd.continuousAt.tendsto).trans
    (second_bigO.norm_left.pow 5)

theorem velocity_remainder :
    (fun p : State => displacementVelocity p-p.2-conj p.2*p.2^2/3+(normSq p.1 : ℂ)*p.2)
      =O[𝓝 0] (fun p => ‖p‖^5) := by
  have h1 : (fun p : State => parallelFactor p*(originLog p.2-p.2-conj p.2*p.2^2/3))
      =O[𝓝 0] (fun p => ‖p‖^5) := by
    simpa only [one_mul] using parallelFactor_bigO.mul log_second_remainder
  have h2 : (fun p : State => (parallelFactor p-1+(normSq p.1 : ℂ))*p.2)
      =O[𝓝 0] (fun p => ‖p‖^5) := by
    convert parallelFactor_remainder.mul second_bigO using 1
    funext p; ring
  have h3 : (fun p : State => (parallelFactor p-1)*(conj p.2*p.2^2))
      =O[𝓝 0] (fun p => ‖p‖^5) := by
    convert parallelFactor_deviation.mul (complexCube_bigO second_bigO) using 1
    funext p; ring
  apply ((h1.add h2).add (h3.const_mul_left (1/3 : ℂ))).congr_left
  intro p
  change _ = parallelFactor p*originLog p.2-p.2-conj p.2*p.2^2/3+(normSq p.1 : ℂ)*p.2
  ring

theorem velocity_bigO : displacementVelocity =O[𝓝 (0 : State)] (fun p => ‖p‖) := by
  have h := displacementVelocity_derivative.isBigO_sub.norm_right
  convert! h using 1 <;> (funext p; simp [displacementVelocity,radialParallel,originLog_zero])

theorem velocity_deviation : (fun p : State => displacementVelocity p-p.2)
    =O[𝓝 0] (fun p => ‖p‖^3) := by
  have he := velocity_remainder.trans
    (isLittleO_norm_pow_norm_pow (E' := State) (by norm_num : 3 < 5)).isBigO
  have hc := (complexCube_bigO second_bigO).const_mul_left (1/3 : ℂ)
  have hq : (fun p : State => (normSq p.1 : ℂ)*p.2) =O[𝓝 0] (fun p => ‖p‖^3) := by
    have hn := (Complex.ofRealCLM.isBigO_comp (fun p : State => normSq p.1) _).trans normSq_first_bigO
    convert hn.mul second_bigO using 1
    · rfl
    · funext p; ring
  apply ((he.add hc).sub hq).congr_left
  intro p
  ring

theorem displacement_remainder :
    (fun p : State => displacement p-p.1-p.2+conj p.1*p.2^2+(normSq p.1 : ℂ)*p.2)
      =O[𝓝 0] (fun p => ‖p‖^5) := by
  have ht : Filter.Tendsto (fun p : State => (p.1,displacementVelocity p)) (𝓝 0) (𝓝 0) := by
    have h := (contDiffAt_fst.prodMk displacementVelocity_smooth).continuousAt.tendsto
    have hz : ((0 : State).1,displacementVelocity 0) = (0 : State) := by
      simp [displacementVelocity,radialParallel,originLog_zero]
    rw [hz] at h
    convert! h using 1
  have he := (expMap_remainder.comp_tendsto ht).trans
    ((first_bigO.prod_left velocity_bigO).norm_left.pow 5)
  have hm : (fun p : State => conj p.1*((displacementVelocity p)^2-p.2^2))
      =O[𝓝 0] (fun p => ‖p‖^5) := by
    have h := ((complexConjugate_bigO first_bigO).mul velocity_deviation).mul
      (velocity_bigO.add second_bigO)
    convert h using 1 <;> (funext p; ring)
  have hc := complexCube_difference velocity_bigO second_bigO velocity_deviation
  apply (((he.add velocity_remainder).sub hm).sub (hc.const_mul_left (1/3 : ℂ))).congr_left
  intro p
  change (displacement p-(p.1+displacementVelocity p)+conj p.1*(displacementVelocity p)^2+
      conj (displacementVelocity p)*(displacementVelocity p)^2/3 +
      (displacementVelocity p-p.2-conj p.2*p.2^2/3+(normSq p.1 : ℂ)*p.2) -
      conj p.1*((displacementVelocity p)^2-p.2^2) -
      (1/3 : ℂ)*(conj (displacementVelocity p)*(displacementVelocity p)^2-conj p.2*p.2^2)) = _
  ring

end RadialMetric
