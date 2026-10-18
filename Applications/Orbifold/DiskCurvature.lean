import Applications.Orbifold.DiskConnection
import Applications.Geometry.ConformalConnection

/-! Experimental derivative and curvature checks for the disk Levi-Civita
coefficient, with curvature convention R(X,Y)Z = nabla_X nabla_Y Z - nabla_Y nabla_X Z. -/
noncomputable section
open scoped ComplexConjugate
namespace Orbifold.DiskConnection

def scale (z : ℂ) : ℝ := 2 / gap z
def b (z : ℂ) : ℂ := 2 * conj z / (gap z : ℂ)
def db (z u : ℂ) : ℂ :=
  2 * conj u / (gap z : ℂ) + 4 * conj z * ((conj z * u).re : ℂ) / (gap z : ℂ) ^ 2

theorem coefficient_derivative {c : ℝ → ℂ} {u : ℂ} {t : ℝ}
    (hc : HasDerivAt c u t) (hg : gap (c t) ≠ 0) :
    HasDerivAt (fun s => b (c s)) (db (c t) u) t := by
  have hgap := ((hasDerivAt_const t (1 : ℝ)).sub (normSq_derivative hc)).ofReal_comp
  have hgc : (gap (c t) : ℂ) ≠ 0 := by exact_mod_cast hg
  convert (hc.star.const_mul 2).div hgap hgc using 1
  · rfl
  · change db (c t) u = (2 * conj u * (gap (c t) : ℂ) -
        (2 * conj (c t)) * ((0 - 2 * (conj (c t) * u).re : ℝ) : ℂ)) / (gap (c t) : ℂ) ^ 2
    unfold db
    push_cast
    field_simp
    <;> ring

theorem curvature_vector (z : ℂ) (hz : gap z ≠ 0) :
    ConformalConnection.curvatureVector b z = (-4 / (gap z : ℂ) ^ 2) := by
  have hx := coefficient_derivative
    ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_add z)) (by simpa using hz)
  have hy := coefficient_derivative
    (((((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).const_add z)) (by simpa using hz)
  rw [ConformalConnection.curvature_of_derivatives b z (db z 1) (db z Complex.I)
    (by simpa only [id_eq, zero_add, add_zero, Complex.ofReal_zero, Complex.ofReal_one] using hx)
    (by simpa only [id_eq, zero_add, add_zero, Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul] using hy)]
  have hg : (gap z : ℂ) ≠ 0 := by exact_mod_cast hz
  simp [db, Complex.mul_re]
  field_simp
  apply Complex.ext <;> simp [gap, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

theorem curvature_minus_one (z : ℂ) (hz : gap z ≠ 0) :
    ConformalConnection.gaussian scale b z = -1 := by
  rw [ConformalConnection.gaussian, curvature_vector z hz]
  have hh : (-4 / (gap z : ℂ) ^ 2) = ((-4 / gap z ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [hh]
  simp only [Complex.ofReal_re, scale]
  field_simp
  norm_num

/-- Actual derivative of the conformal scale along a path. -/
theorem scale_derivative {c : ℝ → ℂ} {u : ℂ} {t : ℝ}
    (hc : HasDerivAt c u t) (hg : gap (c t) ≠ 0) :
    HasDerivAt (fun s => scale (c s))
      (scale (c t) * (coefficient (c t) u).re) t := by
  convert (hasDerivAt_const t (2 : ℝ)).div
    ((hasDerivAt_const t (1 : ℝ)).sub (normSq_derivative hc)) hg using 1
  · rfl
  · simp [scale, coefficient, gap, Complex.div_re, Complex.mul_re, Complex.normSq_apply] at *
    field_simp
    <;> ring

/-- Compatibility on arbitrary constant coordinate fields, with the metric
variation supplied by the actual base-curve derivative. -/
theorem metric_compatible {c : ℝ → ℂ} {u : ℂ} {t : ℝ}
    (hc : HasDerivAt c u t) (hg : gap (c t) ≠ 0) (v w : ℂ) :
    HasDerivAt (fun s => metric (c s) v w)
      (metric (c t) (christoffel (c t) u v) w +
       metric (c t) v (christoffel (c t) u w)) t := by
  have hd := ((hasDerivAt_const t (4 : ℝ)).div
    (((hasDerivAt_const t (1 : ℝ)).sub (normSq_derivative hc)).pow 2)
    (pow_ne_zero 2 hg)).mul_const ((conj v * w).re)
  convert hd using 1
  · rfl
  · simp [metric, christoffel, coefficient, gap, Complex.div_re, Complex.div_im,
      Complex.mul_re, Complex.mul_im, Complex.normSq_apply] at *
    field_simp
    <;> ring

/-- The torsion-free, metric-compatible coefficient is unique in the disk chart.
Compatibility is stated with the actual derivative of the metric, so this
characterizes the selected Levi-Civita connection without assuming its formula. -/
theorem leviCivita_unique (z : ℂ) (hz : gap z ≠ 0) (B : ℂ → ℂ → ℂ)
    (hs : ∀ u v, B u v = B v u)
    (hm : ∀ u v w, HasDerivAt (fun t : ℝ => metric (z + t * u) v w)
      (metric z (B u v) w + metric z v (B u w)) 0) :
    B = christoffel z := by
  refine ConformalConnection.metric_coefficient_unique
    (fun u v : ℂ => (conj u * v).re) ?_ ?_ ?_ B (christoffel z) hs (torsion_free z) ?_
  · intro u v w; simp [Complex.mul_re]; ring
  · intro u v; simp [Complex.mul_re]; ring
  · intro u hu
    apply Complex.normSq_eq_zero.mp
    simpa [Complex.normSq_apply, Complex.mul_re] using hu u
  · intro u v w
    have hd := metric_compatible
      (((((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const u).const_add z))
      (by simpa using hz) v w
    have he := (hm u v w).unique (by simpa using hd)
    have hk : (4 / gap z ^ 2 : ℝ) ≠ 0 := div_ne_zero (by norm_num) (pow_ne_zero 2 hz)
    simp only [metric, ← mul_add] at he
    exact mul_left_cancel₀ hk he

end Orbifold.DiskConnection
