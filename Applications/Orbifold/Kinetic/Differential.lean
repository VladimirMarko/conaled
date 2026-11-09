import Applications.Orbifold.TimedMotion
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! Actual real differentials for the free particle, in the native complex chart. -/
noncomputable section
open scoped ComplexConjugate ContDiff
namespace Orbifold.Kinetic
open DiskConnection

/-- Euclidean real covector represented by a complex vector. -/
def covector (v : ℂ) : ℂ →L[ℝ] ℝ := v.re • Complex.reCLM + v.im • Complex.imCLM

@[simp] theorem covector_apply (v w : ℂ) : covector v w = v.re*w.re+v.im*w.im := rfl

theorem normSq_fderiv (z : ℂ) : HasFDerivAt Complex.normSq (2 • covector z) z := by
  have hr := Complex.reCLM.hasFDerivAt (x := z)
  have hi := Complex.imCLM.hasFDerivAt (x := z)
  convert (hr.mul hr).add (hi.mul hi) using 1
  · funext w; simp [Complex.normSq_apply]
  · ext w; simp [covector]; ring

theorem gap_fderiv (z : ℂ) : HasFDerivAt gap (-2 • covector z) z := by
  convert (hasFDerivAt_const (1 : ℝ) z).sub (normSq_fderiv z) using 1
  · rfl
  · ext w; simp

theorem quotient_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {x : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) (hne : g x ≠ 0) :
    HasFDerivAt (fun y => f y / g y)
      ((g x)⁻¹ • f' - (f x / (g x)^2) • g') x := by
  have hi := (hasDerivAt_inv hne).comp_hasFDerivAt x hg
  convert hf.mul hi using 1
  · funext y; exact div_eq_mul_inv _ _
  · ext v; simp; ring

def lagrangian (z v : ℂ) : ℝ := 2 * Complex.normSq v / gap z ^ 2

def momentum (z v : ℂ) : ℂ := (4 / gap z ^ 2 : ℝ) • v

def force (z v : ℂ) : ℂ := (8 * Complex.normSq v / gap z ^ 3 : ℝ) • z

theorem lagrangian_velocity (z v : ℂ) :
    HasFDerivAt (lagrangian z) (covector (momentum z v)) v := by
  convert ((normSq_fderiv v).const_mul 2).mul_const (gap z ^ 2)⁻¹ using 1
  · funext w; exact div_eq_mul_inv _ _
  · ext w
    simp only [covector,momentum,add_apply,smul_apply,
      Complex.reCLM_apply,Complex.imCLM_apply]
    simp only [Complex.real_smul,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,mul_zero,sub_zero,smul_eq_mul]
    ring

theorem lagrangian_position (z v : ℂ) (hg : gap z ≠ 0) :
    HasFDerivAt (fun x => lagrangian x v) (covector (force z v)) z := by
  have h := quotient_fderiv (hasFDerivAt_const (2 * Complex.normSq v) z)
    ((gap_fderiv z).pow 2) (pow_ne_zero 2 hg)
  convert h using 1
  · rfl
  · ext w
    simp only [covector,force,add_apply,smul_apply,
      sub_apply,zero_apply,Complex.reCLM_apply,Complex.imCLM_apply]
    simp only [Complex.real_smul,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,mul_zero,sub_zero,smul_eq_mul]
    field_simp
    ring

theorem lagrangian_metric (z v : ℂ) : lagrangian z v = metric z v v / 2 := by
  simp [lagrangian,metric,Complex.mul_re,Complex.normSq_apply]
  ring

theorem native_energy (p : Pose) (d : ℂ) (hd : Complex.normSq d = 1) (s t : ℝ) :
    lagrangian (DiskTransport.move p d hd s t).a
      ((DiskTransport.move p d hd s t).frame (d*(s : ℂ))) = s^2/2 := by
  rw [lagrangian_metric,DiskTransport.move_speed]

example (v : ℂ) : momentum 0 v = (4 : ℝ) • v := by simp [momentum,gap]
example : force 0 0 = 0 := by simp [force]

end Orbifold.Kinetic
