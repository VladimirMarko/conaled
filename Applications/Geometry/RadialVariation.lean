import Applications.Geometry.RadialFlow
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra

/-! Integral-equation infrastructure for initial-data dependence of the fixed
radial flow. Differentiability in time alone is not used as parameter regularity. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace RadialMetric.Variation
open Set Metric
open scoped Topology

abbrev Time := Icc (0 : ℝ) 1
abbrev Curve := C(Time, ℂ)
abbrev Paths := Curve × Curve

instance : Nonempty Time := ⟨⟨0, by norm_num⟩⟩

def extend (f : Curve) (t : ℝ) : ℂ := f (projIcc 0 1 (by norm_num) t)

theorem continuous_extend (f : Curve) : Continuous (extend f) :=
  f.continuous.comp continuous_projIcc

def integralCurve (f : Curve) : Curve :=
  ⟨fun t => ∫ s in (0 : ℝ)..t.val, extend f s,
    (intervalIntegral.continuous_primitive
      (fun a b => (continuous_extend f).intervalIntegrable a b) 0).comp continuous_subtype_val⟩

theorem integralCurve_bound (f : Curve) : ‖integralCurve f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro t
  change ‖∫ s in (0 : ℝ)..t.val, extend f s‖ ≤ ‖f‖
  calc
    _ ≤ ‖f‖ * |t.val - 0| := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun s _ => f.norm_coe_le_norm _)
    _ ≤ ‖f‖ := by rw [sub_zero, abs_of_nonneg t.property.1]; nlinarith [t.property.2, norm_nonneg f]

def integralLinear : Curve →ₗ[ℝ] Curve where
  toFun := integralCurve
  map_add' f g := by
    ext t
    exact intervalIntegral.integral_add
      ((continuous_extend f).intervalIntegrable 0 t.val)
      ((continuous_extend g).intervalIntegrable 0 t.val)
  map_smul' c f := by
    ext t
    exact intervalIntegral.integral_smul c (extend f)

def integralCLM : Curve →L[ℝ] Curve :=
  integralLinear.mkContinuous 1 (fun f => by
    change ‖integralCurve f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using integralCurve_bound f)

@[simp] theorem integralCLM_apply (f : Curve) (t : Time) :
    integralCLM f t = ∫ s in (0 : ℝ)..t.val, extend f s := rfl

def constant : ℂ →L[ℝ] Curve := ContinuousLinearMap.const ℝ Time

def conjugate : Curve →L[ℝ] Curve := (starL' ℝ : Curve ≃L[ℝ] Curve).toContinuousLinearMap

def linearResidual : State × Paths →L[ℝ] Paths :=
  (((ContinuousLinearMap.fst ℝ Curve Curve).comp (ContinuousLinearMap.snd ℝ State Paths) -
    constant.comp ((ContinuousLinearMap.fst ℝ ℂ ℂ).comp (ContinuousLinearMap.fst ℝ State Paths)) -
    (1/2 : ℝ) • integralCLM.comp
      ((ContinuousLinearMap.snd ℝ Curve Curve).comp (ContinuousLinearMap.snd ℝ State Paths))).prod
  ((ContinuousLinearMap.snd ℝ Curve Curve).comp (ContinuousLinearMap.snd ℝ State Paths) -
    constant.comp ((ContinuousLinearMap.snd ℝ ℂ ℂ).comp (ContinuousLinearMap.fst ℝ State Paths))))

def residual (p : State × Paths) : Paths :=
  linearResidual p + (0, integralCLM (conjugate p.2.1 * p.2.2 ^ 2))

theorem residual_smooth : ContDiff ℝ ⊤ residual := by
  unfold residual
  apply linearResidual.contDiff.add
  apply contDiff_const.prodMk
  exact integralCLM.contDiff.comp
    ((conjugate.contDiff.comp (contDiff_fst.comp contDiff_snd)).mul
      ((contDiff_snd.comp contDiff_snd).pow 2))

def pathZ : State × Paths →L[ℝ] Curve :=
  (ContinuousLinearMap.fst ℝ Curve Curve).comp (ContinuousLinearMap.snd ℝ State Paths)
def pathW : State × Paths →L[ℝ] Curve :=
  (ContinuousLinearMap.snd ℝ Curve Curve).comp (ContinuousLinearMap.snd ℝ State Paths)

theorem cubic_derivative_zero :
    HasFDerivAt (fun p : State × Paths => integralCLM (conjugate p.2.1 * p.2.2 ^ 2)) (0 : State × Paths →L[ℝ] Curve) 0 := by
  have hz : HasFDerivAt (fun p : State × Paths => conjugate p.2.1)
      (conjugate.comp pathZ) (0 : State × Paths) := (conjugate.comp pathZ).hasFDerivAt
  have hw : HasFDerivAt (fun p : State × Paths => p.2.2) pathW (0 : State × Paths) :=
    pathW.hasFDerivAt
  have hc : HasFDerivAt (fun p : State × Paths => conjugate p.2.1 * p.2.2 ^ 2)
      (0 : State × Paths →L[ℝ] Curve) 0 := by
    convert hz.mul (hw.mul hw) using 1
    · funext p; simp [pow_two]
    · apply ContinuousLinearMap.ext
      intro p
      apply ContinuousMap.ext
      intro t
      simp [pathZ, pathW, conjugate, ContinuousLinearMap.smul_apply, smul_eq_mul]
  convert! integralCLM.hasFDerivAt.comp (0 : State × Paths) hc using 1 <;> simp

theorem residual_derivative_zero : HasFDerivAt residual linearResidual 0 := by
  have hc := cubic_derivative_zero
  have hl : HasFDerivAt (fun p : State × Paths => linearResidual p) linearResidual 0 :=
    linearResidual.hasFDerivAt
  have hn : HasFDerivAt (fun p : State × Paths =>
      ((0 : Curve), integralCLM (conjugate p.2.1 * p.2.2 ^ 2)))
      (0 : State × Paths →L[ℝ] Paths) 0 := by
    convert! (ContinuousLinearMap.inr ℝ Curve Curve).hasFDerivAt.comp
      (0 : State × Paths) hc using 1 <;> simp
  convert! hl.add hn using 1 <;> simp [residual]

def pathDerivative : Paths →L[ℝ] Paths :=
  ((ContinuousLinearMap.fst ℝ Curve Curve -
    (1/2 : ℝ) • integralCLM.comp (ContinuousLinearMap.snd ℝ Curve Curve)).prod
    (ContinuousLinearMap.snd ℝ Curve Curve))

def pathInverse : Paths →L[ℝ] Paths :=
  ((ContinuousLinearMap.fst ℝ Curve Curve +
    (1/2 : ℝ) • integralCLM.comp (ContinuousLinearMap.snd ℝ Curve Curve)).prod
    (ContinuousLinearMap.snd ℝ Curve Curve))

theorem pathDerivative_invertible : pathDerivative.IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := pathInverse)
  · ext p t <;> simp [pathDerivative, pathInverse]
  · ext p t <;> simp [pathDerivative, pathInverse]

theorem residual_partial_invertible :
    (fderiv ℝ residual 0 ∘L ContinuousLinearMap.inr ℝ State Paths).IsInvertible := by
  rw [residual_derivative_zero.fderiv]
  have he : linearResidual ∘L ContinuousLinearMap.inr ℝ State Paths = pathDerivative := by
    ext p t <;> simp [linearResidual, pathDerivative]
  rw [he]
  exact pathDerivative_invertible

/-- Smooth path family obtained from the actual polynomial integral equation. -/
def solutionPaths : State → Paths :=
  residual_smooth.contDiffAt.implicitFunction (by simp) residual_partial_invertible

theorem solutionPaths_zero : solutionPaths 0 = 0 :=
  residual_smooth.contDiffAt.implicitFunction_apply_self (by simp) residual_partial_invertible

theorem solutionPaths_smooth : ContDiffAt ℝ ⊤ solutionPaths 0 :=
  residual_smooth.contDiffAt.contDiffAt_implicitFunction (by simp) residual_partial_invertible

theorem solutionPaths_equation : ∀ᶠ p in 𝓝 (0 : State), residual (p,solutionPaths p) = 0 := by
  have h := residual_smooth.contDiffAt.eventually_apply_implicitFunction
    (by simp) residual_partial_invertible
  have hz : residual (0 : State × Paths) = 0 := by
    ext t <;> simp [residual, linearResidual, smul_zero]
  rw [hz] at h
  exact h

end RadialMetric.Variation
