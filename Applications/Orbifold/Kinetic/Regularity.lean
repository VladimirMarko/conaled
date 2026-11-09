import Applications.Orbifold.Kinetic.Midpoint
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section
open scoped ContDiff
namespace Orbifold.Kinetic
open DiskConnection

@[simp] theorem midpoint_self (x : ℂ) : midpoint x x = x := by
  apply Complex.ext <;> simp [midpoint] <;> ring

theorem normSq_smooth : ContDiff ℝ ∞ Complex.normSq := by
  convert (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff) using 1
  funext z
  simp [Complex.normSq_apply]

theorem gap_smooth : ContDiff ℝ ∞ gap := contDiff_const.sub normSq_smooth

theorem midpoint_smooth : ContDiff ℝ ∞ (fun p : ℂ × ℂ => midpoint p.1 p.2) :=
  (contDiff_fst.add contDiff_snd).const_smul (1/2 : ℝ)

def diagonalScale (h : ℝ) (x : ℂ) : ℝ := 4/(h*gap x^2)

def deltaLinear : (ℂ × ℂ) →L[ℝ] ℂ :=
  ContinuousLinearMap.snd ℝ ℂ ℂ - ContinuousLinearMap.fst ℝ ℂ ℂ

theorem d1_joint_diagonal (h : ℝ) (x : ℂ) (hh : h ≠ 0) (hg : gap x ≠ 0) :
    HasFDerivAt (fun p : ℂ × ℂ => d1 h p.1 p.2)
      (-diagonalScale h x • deltaLinear) (x,x) := by
  have hm := midpoint_smooth.differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hgap := (gap_smooth.comp midpoint_smooth).differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hden : h*gap (midpoint x x)^2 ≠ 0 := by simpa using mul_ne_zero hh (pow_ne_zero 2 hg)
  have ha := quotient_fderiv (hasFDerivAt_const (4 : ℝ) (x,x))
    (((hgap (x,x)).hasFDerivAt.pow 2).const_mul h) hden
  have hb := quotient_fderiv (hasFDerivAt_const (4 : ℝ) (x,x))
    (((hgap (x,x)).hasFDerivAt.pow 3).const_mul h)
    (by simpa using mul_ne_zero hh (pow_ne_zero 3 hg))
  have hd : HasFDerivAt (fun p : ℂ × ℂ => p.2-p.1) deltaLinear (x,x) :=
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.sub
      (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt
  have hn := (normSq_fderiv (x-x)).comp (x,x) hd
  have hfirst := ha.neg.smul hd
  have hsecond := (hb.mul hn).smul (hm (x,x)).hasFDerivAt
  convert hfirst.add hsecond using 1
  · funext p
    dsimp [d1]
    congr 1
    congr 1
    ring
  · apply ContinuousLinearMap.ext
    intro p
    simp [diagonalScale,deltaLinear,covector,ContinuousLinearMap.comp_apply]

theorem d2_joint_diagonal (h : ℝ) (x : ℂ) (hh : h ≠ 0) (hg : gap x ≠ 0) :
    HasFDerivAt (fun p : ℂ × ℂ => d2 h p.1 p.2)
      (diagonalScale h x • deltaLinear) (x,x) := by
  have hm := midpoint_smooth.differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hgap := (gap_smooth.comp midpoint_smooth).differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hden : h*gap (midpoint x x)^2 ≠ 0 := by simpa using mul_ne_zero hh (pow_ne_zero 2 hg)
  have ha := quotient_fderiv (hasFDerivAt_const (4 : ℝ) (x,x))
    (((hgap (x,x)).hasFDerivAt.pow 2).const_mul h) hden
  have hb := quotient_fderiv (hasFDerivAt_const (4 : ℝ) (x,x))
    (((hgap (x,x)).hasFDerivAt.pow 3).const_mul h)
    (by simpa using mul_ne_zero hh (pow_ne_zero 3 hg))
  have hd : HasFDerivAt (fun p : ℂ × ℂ => p.2-p.1) deltaLinear (x,x) :=
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.sub
      (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt
  have hn := (normSq_fderiv (x-x)).comp (x,x) hd
  have hfirst := ha.smul hd
  have hsecond := (hb.mul hn).smul (hm (x,x)).hasFDerivAt
  convert hfirst.add hsecond using 1
  · funext p
    dsimp [d2]
    congr 1
    congr 1
    ring
  · apply ContinuousLinearMap.ext
    intro p
    simp [diagonalScale,deltaLinear,covector,ContinuousLinearMap.comp_apply]

/-- This is the derivative of the already proved first partial, not a stipulated Hessian. -/
theorem mixed_hessian (h : ℝ) (x : ℂ) (hh : h ≠ 0) (hg : gap x ≠ 0) :
    HasFDerivAt (fun y => d1 h x y)
      (-(4/(h*gap x^2)) • ContinuousLinearMap.id ℝ ℂ) x := by
  have H := (d1_joint_diagonal h x hh hg).comp x
    ((hasFDerivAt_const (𝕜 := ℝ) x x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  convert H using 1
  · rfl
  · ext v
    simp [diagonalScale,deltaLinear]

end Orbifold.Kinetic
