import Applications.Geometry.ConformalConnection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Experimental variable-curvature consumer of the scalar transport construction.
The metric is exp(2*x²)(dx²+dy²), and admitted segments are vertical affine lines. -/
noncomputable section
open Set
namespace VariableCurvature

def scale (z : ℂ) : ℝ := Real.exp (z.re ^ 2)
def coefficient (z : ℂ) : ℂ := 2 * (z.re : ℂ)
def curve (b : ℝ) (t : ℝ) : ℂ := (b : ℂ) + t * Complex.I
def factor (b t : ℝ) : ℂ := Complex.exp (-2 * b * t * Complex.I)

theorem factor_nonzero (b t : ℝ) : factor b t ≠ 0 := Complex.exp_ne_zero _

def transport (b a t : ℝ) : ℂ ≃ₗ[ℝ] ℂ :=
  ParallelTransport.scalar (factor b) a t (factor_nonzero b a) (factor_nonzero b t)

theorem curve_derivative (b t : ℝ) : HasDerivAt (curve b) Complex.I t := by
  convert (((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).const_add (b : ℂ) using 1 <;> first | rfl | simp

theorem factor_parallel (b t : ℝ) :
    HasDerivAt (factor b) (-coefficient (curve b t) * Complex.I * factor b t) t := by
  convert ((((hasDerivAt_id t).ofReal_comp).const_mul (-2 * (b : ℂ))).mul_const Complex.I).cexp using 1
  · rfl
  · simp [factor, coefficient, curve]; ring

theorem solves (b a t : ℝ) (v : ℂ) :
    HasDerivAt (fun s => factor b s / factor b a * v)
      (-coefficient (curve b t) * Complex.I * (factor b t / factor b a * v)) t := by
  simpa only [neg_mul, mul_assoc] using
    (ParallelTransport.scalar_solves (k := fun t => coefficient (curve b t) * Complex.I)
      (a := a) (by simpa only [neg_mul, mul_assoc] using factor_parallel b t) v)

theorem unique (b a t : ℝ) (w : ℝ → ℂ)
    (hw : ∀ s ∈ Icc a t,
      HasDerivAt w (-coefficient (curve b s) * Complex.I * w s) s)
    (hat : a ≤ t) : w t = transport b a t (w a) := by
  exact ParallelTransport.scalar_unique (k := fun s => coefficient (curve b s) * Complex.I) (fun s _ => factor_nonzero b s)
    (fun s _ => by simpa only [neg_mul, mul_assoc] using factor_parallel b s)
    (fun s hs => by simpa only [neg_mul, mul_assoc] using hw s hs) ⟨hat, le_rfl⟩

theorem metric_preserved (b a t : ℝ) (v : ℂ) :
    scale (curve b t) ^ 2 * Complex.normSq (transport b a t v) =
      scale (curve b a) ^ 2 * Complex.normSq v := by
  simp [transport, ParallelTransport.scalar, factor, map_mul,
    Complex.normSq_div, Complex.normSq_eq_norm_sq, Complex.norm_exp, scale, curve]

/-- This is computed from derivatives of Christoffel coefficients, not assigned
as a descriptive curvature label. -/
theorem curvature (z : ℂ) :
    ConformalConnection.gaussian scale coefficient z = -2 / Real.exp (z.re ^ 2) ^ 2 := by
  have hx : HasDerivAt (fun t : ℝ => coefficient (z + t)) 2 0 := by
    convert ((((hasDerivAt_id (0 : ℝ)).const_add z.re).ofReal_comp).const_mul 2) using 1 <;>
      simp [coefficient]
  have hy : HasDerivAt (fun t : ℝ => coefficient (z + t * Complex.I)) 0 0 := by
    simpa [coefficient] using hasDerivAt_const (0 : ℝ) (2 * (z.re : ℂ))
  rw [ConformalConnection.gaussian, ConformalConnection.curvature_of_derivatives _ _ _ _ hx hy]
  simp [scale]

theorem curvature_nonconstant :
    ConformalConnection.gaussian scale coefficient 0 ≠
      ConformalConnection.gaussian scale coefficient 1 := by
  rw [curvature, curvature]
  norm_num
  have h : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  have hp := Real.exp_pos (1 : ℝ)
  intro he
  have := (div_eq_iff (ne_of_gt (sq_pos_of_pos hp))).mp he.symm
  nlinarith

/-- The logarithmic scale gradient is (2x,0), yielding the displayed coefficient. -/
theorem log_scale_derivative (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
  convert (hasDerivAt_id x).pow 2 using 1 <;> first | rfl | simp

open scoped ComplexConjugate in
def metric (z v w : ℂ) : ℝ := scale z ^ 2 * (conj v * w).re

theorem torsion_free (z u v : ℂ) :
    ConformalConnection.gamma coefficient z u v = ConformalConnection.gamma coefficient z v u := by
  simp [ConformalConnection.gamma]; ring

open scoped ComplexConjugate in
/-- Compatibility is proved by differentiating exp(2*x²), for every path
velocity and every pair of constant coordinate fields. -/
theorem metric_compatible {c : ℝ → ℂ} {u : ℂ} {t : ℝ}
    (hc : HasDerivAt c u t) (v w : ℂ) :
    HasDerivAt (fun s => metric (c s) v w)
      (metric (c t) (ConformalConnection.gamma coefficient (c t) u v) w +
       metric (c t) v (ConformalConnection.gamma coefficient (c t) u w)) t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hc
  have hd := (((hr.pow 2).exp).pow 2).mul_const ((conj v * w).re)
  convert hd using 1
  · rfl
  · simp [metric, scale, coefficient, ConformalConnection.gamma,
      Complex.mul_re, Complex.mul_im]; ring

end VariableCurvature
