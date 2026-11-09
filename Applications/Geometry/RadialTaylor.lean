import Applications.Geometry.RadialRemainder
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Evaluation of the cubic path correction, with the actual fifth-order bound
inherited from the selected integral equation. -/
noncomputable section
namespace RadialMetric.Variation
open Set Metric Asymptotics Complex
open scoped Topology ComplexConjugate

def timePower (n : ℕ) : Curve := ⟨fun t => (t.val : ℂ)^n, by fun_prop⟩

theorem integral_monomial (c : ℂ) (n : ℕ) :
    integralCLM (constant c * timePower n) = constant (c/(n+1)) * timePower (n+1) := by
  ext t
  change (∫ s in (0 : ℝ)..t.val, extend (constant c*timePower n) s) =
    (c/(n+1))*(t.val : ℂ)^(n+1)
  have he : (∫ s in (0 : ℝ)..t.val, extend (constant c*timePower n) s) =
      ∫ s in (0 : ℝ)..t.val, c*(s : ℂ)^n := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    have hp : projIcc 0 1 (by norm_num) s = ⟨s,⟨hs.1,hs.2.trans t.property.2⟩⟩ :=
      projIcc_of_mem _ ⟨hs.1,hs.2.trans t.property.2⟩
    simp [extend,hp,constant,timePower]
  rw [he,intervalIntegral.integral_const_mul]
  simp_rw [← Complex.ofReal_pow]
  rw [intervalIntegral.integral_ofReal,integral_pow]
  push_cast
  simp
  ring

theorem timePower_zero : timePower 0 = 1 := by ext t; simp [timePower]

theorem integral_constant (c : ℂ) : integralCLM (constant c) = constant c*timePower 1 := by
  simpa [timePower_zero] using integral_monomial c 0

theorem initialPaths_position (p : State) :
    (initialPaths p).1 = constant p.1 + constant (p.2/2)*timePower 1 := by
  change constant p.1 + (1/2 : ℝ) • integralCLM (constant p.2) = _
  rw [integral_constant]
  ext t
  simp [constant,timePower,Complex.real_smul]
  ring

theorem initialPaths_cubic (p : State) : pathCubic (initialPaths p) =
    constant (conj p.1*p.2^2) + constant (conj p.2*p.2^2/2)*timePower 1 := by
  rw [pathCubic,initialPaths_position]
  ext t
  change conj (p.1+(p.2/2)*(t.val : ℂ)^1) * p.2 * p.2 =
    conj p.1*p.2^2 + (conj p.2*p.2^2/2)*(t.val : ℂ)^1
  simp only [map_add,map_mul,map_div₀,map_ofNat,Complex.conj_ofReal,pow_one]
  ring

theorem cubic_endpoint (p : State) : (cubicLift (pathCubic (initialPaths p))).1 oneTime =
    -conj p.1*p.2^2/4-conj p.2*p.2^2/24 := by
  change ((-(1/2 : ℝ)) • integralCLM (integralCLM (pathCubic (initialPaths p)))) oneTime = _
  rw [initialPaths_cubic,map_add,integral_constant,integral_monomial,map_add,
    integral_monomial,integral_monomial]
  simp [constant,timePower,oneTime,Complex.real_smul]
  ring

theorem endpoint_remainder :
    (fun p => endpointMap p - (p.1+p.2/2) + conj p.1*p.2^2/4 + conj p.2*p.2^2/24)
      =O[𝓝 (0 : State)] (fun p => ‖p‖^5) := by
  have h := ((ContinuousMap.evalCLM ℝ oneTime : Curve →L[ℝ] ℂ).isBigO_comp
    (fun p => (solutionPaths p - initialPaths p - cubicLift (pathCubic (initialPaths p))).1) _).trans
    solutionPaths_remainder.prod_left_fst
  apply h.congr_left
  intro p
  change (solutionPaths p).1 oneTime - (initialPaths p).1 oneTime -
    (cubicLift (pathCubic (initialPaths p))).1 oneTime = _
  rw [cubic_endpoint,initialPaths_position]
  simp [endpointMap,constant,timePower,oneTime]
  ring

end RadialMetric.Variation

namespace RadialMetric
open Asymptotics Complex
open scoped Topology ComplexConjugate

/-- Actual fifth-order error of the time-one exponential of the fixed metric. -/
theorem expMap_remainder :
    (fun p => expMap p - (p.1+p.2) + conj p.1*p.2^2 + conj p.2*p.2^2/3)
      =O[𝓝 (0 : State)] (fun p => ‖p‖^5) := by
  have hw : Filter.Tendsto weight (𝓝 (0 : State)) (𝓝 (0 : State)) := by
    have he : weight = (weightLinear : State → State) := funext (fun p => (weightLinear_apply p).symm)
    rw [he]
    simpa only [map_zero] using weightLinear.continuous.tendsto (0 : State)
  have h := Variation.endpoint_remainder.comp_tendsto hw
  have hb := ((weightLinear.isBigO_id (𝓝 (0 : State))).norm_left.norm_right).pow 5
  have hb' : (fun p => ‖weight p‖^5) =O[𝓝 (0 : State)] (fun p => ‖p‖^5) := by
    simpa only [weightLinear_apply] using hb
  have hc := h.trans hb'
  apply hc.congr_left
  intro p
  simp only [Function.comp_apply,weight,expMap,map_mul,map_ofNat]
  ring

end RadialMetric

namespace RadialMetric
open Asymptotics Complex
open scoped Topology ComplexConjugate

theorem origin_exp_remainder :
    (fun v : ℂ => expMap (0,v) - v + conj v*v^2/3)
      =O[𝓝 (0 : ℂ)] (fun v => ‖v‖^5) := by
  have ht : Filter.Tendsto (fun v : ℂ => ((0 : ℂ),v)) (𝓝 0) (𝓝 (0 : State)) := by
    have h : ContinuousAt (fun v : ℂ => ((0 : ℂ),v)) 0 := by fun_prop
    exact h.tendsto
  simpa [Function.comp_def,Prod.norm_def] using expMap_remainder.comp_tendsto ht

end RadialMetric
