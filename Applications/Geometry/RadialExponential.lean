import Applications.Geometry.RadialDependence

/-! The time-one exponential endpoint and its initial-data derivative, obtained
from the actual integral equation and identified with the bounded ODE solution. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace RadialMetric.Variation
open Set Metric
open scoped Topology

def initialPaths : State →L[ℝ] Paths :=
  ((constant.comp (ContinuousLinearMap.fst ℝ ℂ ℂ) +
    (1/2 : ℝ) • integralCLM.comp (constant.comp (ContinuousLinearMap.snd ℝ ℂ ℂ))).prod
    (constant.comp (ContinuousLinearMap.snd ℝ ℂ ℂ)))

theorem solutionPaths_derivative : HasFDerivAt solutionPaths initialPaths 0 := by
  have h := residual_smooth.contDiffAt.hasStrictFDerivAt_implicitFunction
    (by simp) residual_partial_invertible
  have hp : linearResidual ∘L ContinuousLinearMap.inr ℝ State Paths = pathDerivative := by
    ext p t <;> simp [linearResidual, pathDerivative]
  have hinv : pathDerivative.inverse = pathInverse := by
    apply ContinuousLinearMap.inverse_eq
    · ext p t <;> simp [pathDerivative, pathInverse]
    · ext p t <;> simp [pathDerivative, pathInverse]
  rw [residual_derivative_zero.fderiv, hp, hinv] at h
  convert! h.hasFDerivAt using 1
  apply ContinuousLinearMap.ext
  intro p
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro t <;>
    simp [initialPaths, pathInverse, linearResidual, add_comm]

def oneTime : Time := ⟨1,by norm_num⟩
def endpointMap (p : State) : ℂ := (solutionPaths p).1 oneTime

def endpointDerivative : State →L[ℝ] ℂ :=
  ContinuousLinearMap.fst ℝ ℂ ℂ + (1/2 : ℝ) • ContinuousLinearMap.snd ℝ ℂ ℂ

theorem endpointMap_smooth : ContDiffAt ℝ ⊤ endpointMap 0 := by
  convert! (ContinuousMap.evalCLM ℝ oneTime : Curve →L[ℝ] ℂ).contDiff.contDiffAt.comp 0
    (contDiffAt_fst.comp 0 solutionPaths_smooth) using 1

theorem endpointMap_derivative : HasFDerivAt endpointMap endpointDerivative 0 := by
  have h := (ContinuousMap.evalCLM ℝ oneTime).hasFDerivAt.comp (0 : State)
    ((ContinuousLinearMap.fst ℝ Curve Curve).hasFDerivAt.comp (0 : State)
      solutionPaths_derivative)
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro p
  simp [endpointDerivative, initialPaths, constant, integralCLM_apply, extend, oneTime,
    integralCurve, integralCLM, integralLinear]

theorem endpointMap_zero : endpointMap 0 = 0 := by simp [endpointMap,solutionPaths_zero]

theorem endpointMap_eq_bounded {p : State} (hi : p ∈ Initial)
    (hn : ‖solutionPaths p‖ < (1/4 : ℝ)) (he : residual (p,solutionPaths p) = 0) :
    endpointMap p = (boundedFlow ⟨p,hi⟩ 1).1 := by
  have h := integralPath_eq_bounded hi hn he (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  rw [integralPath_eq he (by norm_num)] at h
  have heval := congrArg Prod.fst h
  simpa [endpointMap, extendPaths, extend, oneTime, projIcc] using heval

end RadialMetric.Variation

namespace RadialMetric
open Set Metric
open scoped Topology

def weightLinear : State →L[ℝ] State :=
  (ContinuousLinearMap.fst ℝ ℂ ℂ).prod (2 • ContinuousLinearMap.snd ℝ ℂ ℂ)

def expMap (p : State) : ℂ := Variation.endpointMap (weight p)
def expDerivative : State →L[ℝ] ℂ :=
  ContinuousLinearMap.fst ℝ ℂ ℂ + ContinuousLinearMap.snd ℝ ℂ ℂ

theorem weightLinear_apply (p : State) : weightLinear p = weight p := by
  ext <;> simp [weightLinear, weight, two_smul, two_mul]

theorem expMap_smooth : ContDiffAt ℝ ⊤ expMap 0 := by
  have hf : ContDiffAt ℝ ⊤ Variation.endpointMap (weightLinear 0) := by
    rw [map_zero]; exact Variation.endpointMap_smooth
  have h := hf.comp (0 : State) weightLinear.contDiff.contDiffAt
  convert! h using 1
  funext p; exact congrArg Variation.endpointMap (weightLinear_apply p).symm

theorem expMap_derivative : HasFDerivAt expMap expDerivative 0 := by
  have hf : HasFDerivAt Variation.endpointMap Variation.endpointDerivative (weightLinear 0) := by
    rw [map_zero]; convert! Variation.endpointMap_derivative
  have h := hf.comp (0 : State) weightLinear.hasFDerivAt
  convert! h using 1
  · funext p; exact congrArg Variation.endpointMap (weightLinear_apply p).symm
  · ext p <;> simp [Variation.endpointDerivative, expDerivative, weightLinear, smul_smul]

theorem expMap_zero : expMap 0 = 0 := by
  change Variation.endpointMap (weight (0 : State)) = 0
  have hw : weight (0 : State) = 0 := by ext <;> simp [weight]
  rw [hw]
  exact Variation.endpointMap_zero

/-- The conditions retain the same Picard solution and its bounded comparison. -/
def Admitted (p : State) : Prop := weight p ∈ Initial ∧
  ‖Variation.solutionPaths (weight p)‖ < (1/4 : ℝ) ∧
  Variation.residual (weight p,Variation.solutionPaths (weight p)) = 0

theorem admitted_near_zero : ∀ᶠ p in 𝓝 (0 : State), Admitted p := by
  have ht : Filter.Tendsto weightLinear (𝓝 (0 : State)) (𝓝 (0 : State)) := by
    simpa only [map_zero] using (weightLinear.continuous.continuousAt (x := (0 : State))).tendsto
  have h := ht.eventually Variation.paths_admitted
  simpa only [Admitted, weightLinear_apply] using h

theorem expMap_actual {p : State} (hp : Admitted p) :
    expMap p = endpoint ⟨weight p,hp.1⟩ :=
  Variation.endpointMap_eq_bounded hp.1 hp.2.1 hp.2.2

end RadialMetric
