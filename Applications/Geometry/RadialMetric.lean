import Applications.Orbifold.ConnectionAssessment
import Applications.Geometry.ConformalConnection
import Applications.Orbifold.DiskConnection

/-! The fixed radial conformal metric exp(2|z|²) times the Euclidean metric.
Complex coordinates carry their real Euclidean norm; state products below use
only the ordinary product norm. This is not the earlier x² conformal example. -/
noncomputable section
open scoped ComplexConjugate
namespace RadialMetric
open Complex

/-- Explicit coordinates for comparison with the existing real-pair connection. -/
def coords (z : ℂ) : ℝ × ℝ := (z.re,z.im)
def scale (z : ℂ) : ℝ := Real.exp (normSq z)
def gradient (z : ℂ) : ℝ × ℝ := (2*z.re,2*z.im)
def gamma (z u v : ℂ) : ℂ := 2 * conj z * u * v

theorem scale_positive (z : ℂ) : 0 < scale z := Real.exp_pos _

theorem metric_factor (z : ℂ) : scale z^2 = Real.exp (2*normSq z) := by
  rw [scale,pow_two,← Real.exp_add]
  congr 1
  ring

theorem gamma_coords (z u v : ℂ) : coords (gamma z u v) =
    Orbifold.ConnectionAssessment.gamma (gradient z) (coords u) (coords v) := by
  ext <;> simp [coords, gamma, gradient, Orbifold.ConnectionAssessment.gamma,
    Orbifold.ConnectionAssessment.dot, Complex.mul_re, Complex.mul_im] <;> ring

theorem gamma_symmetric (z u v : ℂ) : gamma z u v = gamma z v u := by
  apply Complex.ext
  · exact congrArg Prod.fst ((gamma_coords z u v).trans
      ((Orbifold.ConnectionAssessment.gamma_symmetric _ _ _).trans (gamma_coords z v u).symm))
  · exact congrArg Prod.snd ((gamma_coords z u v).trans
      ((Orbifold.ConnectionAssessment.gamma_symmetric _ _ _).trans (gamma_coords z v u).symm))

theorem metric_compatibility (z u v w : ℂ) :
    scale z ^ 2 * (Orbifold.ConnectionAssessment.dot (coords (gamma z u v)) (coords w) +
      Orbifold.ConnectionAssessment.dot (coords v) (coords (gamma z u w))) =
    2 * scale z * (scale z * Orbifold.ConnectionAssessment.dot (gradient z) (coords u)) *
      Orbifold.ConnectionAssessment.dot (coords v) (coords w) := by
  rw [gamma_coords, gamma_coords]
  exact Orbifold.ConnectionAssessment.gamma_metric _ _ _ _ _

theorem scale_directional (z u : ℂ) :
    HasDerivAt (fun t : ℝ => scale (z + t * u))
      (scale z * Orbifold.ConnectionAssessment.dot (gradient z) (coords u)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => z + t * u) u 0 := by
    convert (hasDerivAt_const 0 z).add
      ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_id 0)).mul_const u) using 1
    · rfl
    · simp
  have h := (Orbifold.DiskConnection.normSq_derivative hc).exp
  convert h using 1
  · rfl
  · simp [scale, gradient, coords, Orbifold.ConnectionAssessment.dot, Complex.mul_re]
    ring

/-- Quarter-turn covariance is a coefficient law for this actual connection. -/
theorem gamma_quarterTurn (z u v : ℂ) :
    gamma (I*z) (I*u) (I*v) = I * gamma z u v := by
  simp [gamma, map_mul, mul_assoc]
  ring_nf
  simp [Complex.I_sq]

def field (p : ℂ × ℂ) : ℂ × ℂ := (p.2, -gamma p.1 p.2 p.2)
def weightedField (p : ℂ × ℂ) : ℂ × ℂ := (p.2 / 2, -conj p.1 * p.2 ^ 2)
def weight (p : ℂ × ℂ) : ℂ × ℂ := (p.1,2*p.2)

theorem weightedField_weight (p : ℂ × ℂ) : weightedField (weight p) = weight (field p) := by
  ext <;> simp [weightedField, weight, field, gamma] <;> ring

theorem acceleration_coords (z v : ℂ) : coords (-gamma z v v) =
    (-4 * Orbifold.ConnectionAssessment.dot (coords z) (coords v)) • coords v +
      (2 * Orbifold.ConnectionAssessment.dot (coords v) (coords v)) • coords z := by
  ext <;> simp [coords, gamma, Orbifold.ConnectionAssessment.dot,
    Complex.mul_re, Complex.mul_im] <;> ring

end RadialMetric
