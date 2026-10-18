import Applications.Orbifold.ConnectionAssessment
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Experimental disk connection in the global real coordinate chart.
The coefficient is the conformal Levi-Civita coefficient; vectors are complex
numbers viewed as a real vector space, as in the existing disk tangent API. -/
noncomputable section
open scoped ComplexConjugate
namespace Orbifold.DiskConnection

def gap (z : ℂ) : ℝ := 1 - Complex.normSq z

def metric (z v w : ℂ) : ℝ := 4 / gap z ^ 2 * (conj v * w).re

/-- The connection contracted against the path velocity, acting by multiplication. -/
def coefficient (z u : ℂ) : ℂ := 2 * conj z * u / (gap z : ℂ)

def christoffel (z u v : ℂ) : ℂ := coefficient z u * v

theorem torsion_free (z u v : ℂ) : christoffel z u v = christoffel z v u := by
  simp [christoffel, coefficient]; ring

/-- Identification with the conformal coefficient from the assessment. -/
theorem conformal_coefficient (z u v : ℂ) (hg : gap z ≠ 0) :
    ((christoffel z u v).re, (christoffel z u v).im) =
      ConnectionAssessment.gamma
        (ConnectionAssessment.diskGradient z.re z.im) (u.re, u.im) (v.re, v.im) := by
  have hg' : 1 - z.re ^ 2 - z.im ^ 2 ≠ 0 := by simpa [gap, Complex.normSq_apply, sub_sub, pow_two] using hg
  ext <;> simp [christoffel, coefficient, gap, Complex.normSq_apply,
    Complex.div_re, Complex.div_im, ConnectionAssessment.gamma,
    ConnectionAssessment.dot, ConnectionAssessment.diskGradient] <;> field_simp <;> ring_nf <;> field_simp [hg'] <;> ring

/-- Derivative of squared coordinate norm along a real-parameter curve. -/
theorem normSq_derivative {c : ℝ → ℂ} {u : ℂ} {t : ℝ} (h : HasDerivAt c u t) :
    HasDerivAt (fun s => Complex.normSq (c s)) (2 * (conj (c t) * u).re) t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h
  convert (hr.mul hr).add (hi.mul hi) using 1
  · funext s; simp [Complex.normSq_apply]
  · simp [Complex.mul_re]; ring

/-- Metric compatibility along a curve, applied to a parallel field.
The proof differentiates the actual disk metric. -/
theorem parallel_metric_derivative {c v : ℝ → ℂ} {u : ℂ} {t : ℝ}
    (hc : HasDerivAt c u t) (hg : gap (c t) ≠ 0)
    (hv : HasDerivAt v (-coefficient (c t) u * v t) t) :
    HasDerivAt (fun s => metric (c s) (v s) (v s)) 0 t := by
  have hgap := (hasDerivAt_const t (1 : ℝ)).sub (normSq_derivative hc)
  have hn := normSq_derivative hv
  have hd := ((hasDerivAt_const t (4 : ℝ)).div (hgap.pow 2) (pow_ne_zero 2 hg)).mul hn
  convert hd using 1
  · funext s
    simp [metric, gap, Complex.mul_re, Complex.normSq_apply]
  · simp [coefficient, gap, Complex.div_re, Complex.div_im, Complex.mul_re,
      Complex.mul_im, Complex.normSq_apply] at *
    field_simp
    <;> ring

/-- The chosen metric is positive definite on the open disk. -/
theorem metric_positive (z v : ℂ) (hz : Complex.normSq z < 1) (hv : v ≠ 0) :
    0 < metric z v v := by
  have hg : 0 < gap z := sub_pos.mpr hz
  have hn := Complex.normSq_pos.mpr hv
  have he : metric z v v = 4 / gap z ^ 2 * Complex.normSq v := by
    simp [metric, Complex.normSq_apply, Complex.mul_re]
  rw [he]
  exact mul_pos (div_pos (by norm_num) (sq_pos_of_pos hg)) hn

end Orbifold.DiskConnection
