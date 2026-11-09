import Applications.Geometry.RadialTaylor
import Applications.Geometry.RadialDisplacement

/-! Inversion of the actual origin exponential, retaining its local target. -/
noncomputable section
namespace RadialMetric
open Set Metric Complex Asymptotics
open scoped Topology ComplexConjugate

theorem complexConjugate_bigO {E : Type*} [NormedAddCommGroup E] {f : E → ℂ}
    {g : E → ℝ} (h : f =O[𝓝 0] g) : (fun p => conj (f p)) =O[𝓝 0] g :=
  ((starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.isBigO_comp f _).trans h

theorem complexCube_bigO {E : Type*} [NormedAddCommGroup E] {f : E → ℂ}
    (h : f =O[𝓝 0] (fun p => ‖p‖)) :
    (fun p => conj (f p)*(f p)^2) =O[𝓝 0] (fun p => ‖p‖^3) := by
  convert (complexConjugate_bigO h).mul (h.pow 2) using 1
  funext p; ring

theorem complexCube_difference {E : Type*} [NormedAddCommGroup E] {f g : E → ℂ}
    (hf : f =O[𝓝 0] (fun p => ‖p‖)) (hg : g =O[𝓝 0] (fun p => ‖p‖))
    (hd : (fun p => f p-g p) =O[𝓝 0] (fun p => ‖p‖^3)) :
    (fun p => conj (f p)*(f p)^2-conj (g p)*(g p)^2) =O[𝓝 0] (fun p => ‖p‖^5) := by
  have h1 : (fun p => conj (f p-g p)*f p*f p) =O[𝓝 0] (fun p => ‖p‖^5) := by
    convert ((complexConjugate_bigO hd).mul hf).mul hf using 1
    funext p; ring
  have h2 : (fun p => conj (g p)*(f p-g p)*f p) =O[𝓝 0] (fun p => ‖p‖^5) := by
    convert ((complexConjugate_bigO hg).mul hd).mul hf using 1
    funext p; ring
  have h3 : (fun p => conj (g p)*g p*(f p-g p)) =O[𝓝 0] (fun p => ‖p‖^5) := by
    convert ((complexConjugate_bigO hg).mul hg).mul hd using 1
    funext p; ring
  apply ((h1.add h2).add h3).congr_left
  intro p
  simp only [map_sub]
  ring

theorem originLog_bigO : originLog =O[𝓝 (0 : ℂ)] (fun y => ‖y‖) := by
  simpa only [originLog_zero,sub_zero] using originLog_derivative.isBigO_sub.norm_right

theorem originLog_target : ∀ᶠ y in 𝓝 (0 : ℂ), (0,y) ∈ branch.target := by
  have h : ContinuousAt (fun y : ℂ => ((0 : ℂ),y)) 0 := by fun_prop
  exact h.tendsto.eventually branch_neighborhoods.2

theorem originLog_exp_error :
    (fun y => y-originLog y + conj (originLog y)*(originLog y)^2/3)
      =O[𝓝 (0 : ℂ)] (fun y => ‖y‖^5) := by
  have ht : Filter.Tendsto originLog (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [originLog_zero] using originLog_smooth.continuousAt.tendsto
  have he := (origin_exp_remainder.comp_tendsto ht).trans (originLog_bigO.norm_left.pow 5)
  apply he.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [originLog_target] with y hy
  change expMap (0,originLog y) - originLog y + _ = _
  rw [show expMap (0,originLog y) = y from exp_log hy]

theorem originLog_deviation : (fun y => originLog y-y)
    =O[𝓝 (0 : ℂ)] (fun y => ‖y‖^3) := by
  have hc := (complexCube_bigO originLog_bigO).const_mul_left (1/3 : ℂ)
  have he := originLog_exp_error.trans
    (isLittleO_norm_pow_norm_pow (E' := ℂ) (by norm_num : 3 < 5)).isBigO
  apply (hc.sub he).congr_left
  intro y
  ring

theorem originLog_remainder : (fun y => originLog y-y-conj y*y^2/3)
    =O[𝓝 (0 : ℂ)] (fun y => ‖y‖^5) := by
  have hd := complexCube_difference originLog_bigO
    ((isBigO_refl (fun y : ℂ => y) (𝓝 0)).norm_right) originLog_deviation
  apply ((hd.const_mul_left (1/3 : ℂ)).sub originLog_exp_error).congr_left
  intro y
  ring

end RadialMetric
