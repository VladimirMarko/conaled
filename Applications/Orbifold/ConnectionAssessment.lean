import Applications.Orbifold.Pose
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Experimental coordinate feasibility checks for issue #44's prerequisite assessment.
These establish coefficient identities and a nonconstant radial parallel field;
they do not provide a path transport API or a manifold connection instance. -/
noncomputable section
namespace Orbifold.ConnectionAssessment

/-- Euclidean coordinate pairing on the existing product vector space. -/
def dot (v w : ℝ × ℝ) : ℝ := v.1 * w.1 + v.2 * w.2

/-- Christoffel term for a conformal metric with logarithmic scale gradient `a`.
The covariant derivative is `D V[u] + gamma a u V`. -/
def gamma (a u v : ℝ × ℝ) : ℝ × ℝ :=
  (dot a u * v.1 + dot a v * u.1 - dot u v * a.1,
   dot a u * v.2 + dot a v * u.2 - dot u v * a.2)

/-- Symmetry of the Christoffel term is the coordinate torsion-free condition. -/
theorem gamma_symmetric (a u v : ℝ × ℝ) : gamma a u v = gamma a v u := by
  ext <;> simp [gamma, dot] <;> ring

/-- If `D lambda[u] = lambda * dot a u`, this is precisely metric compatibility
for `g(v,w) = lambda^2 * dot v w` on constant coordinate fields. -/
theorem gamma_metric (a u v w : ℝ × ℝ) (scale : ℝ) :
    scale ^ 2 * (dot (gamma a u v) w + dot v (gamma a u w)) =
      2 * scale * (scale * dot a u) * dot v w := by
  simp [gamma, dot]
  ring

/-- Disk logarithmic scale gradient for `lambda = 2 / (1-x²-y²)`. -/
def diskGradient (x y : ℝ) : ℝ × ℝ :=
  (2 * x / (1 - x ^ 2 - y ^ 2), 2 * y / (1 - x ^ 2 - y ^ 2))

/-- A radial field from the origin: coordinate length scales by `1-t²`.
This checks the parallel equation along `c(t)=(t,0)` on any disk subinterval. -/
theorem radial_parallel (t : ℝ) (ht : 1 - t ^ 2 ≠ 0) (v : ℝ × ℝ) :
    (-2 * t * v.1, -2 * t * v.2) +
      gamma (diskGradient t 0) (1, 0) ((1 - t ^ 2) • v) = 0 := by
  ext <;> simp [gamma, diskGradient, dot] <;> field_simp <;> ring

theorem radial_field_derivative (t : ℝ) (v : ℝ × ℝ) :
    HasDerivAt (fun s : ℝ => (1 - s ^ 2) • v) ((-2 * t) • v) t := by
  convert ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow 2)).smul_const v using 1 <;>
    congr 1; simp only [id_eq]; ring

/-- At radius one half the circular connection term is `(2/3) J v` per radian.
Together with `V' = -(2/3) J V` this supplies an explicit solvable loop. -/
theorem circle_coefficient (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1 / 4)
    (v : ℝ × ℝ) :
    gamma (diskGradient x y) (-y, x) v = (-(2 / 3) * v.2, (2 / 3) * v.1) := by
  have hd : 1 - x ^ 2 - y ^ 2 = 3 / 4 := by linarith
  ext <;> simp [gamma, diskGradient, dot, hd] <;>
    nlinarith [congrArg (fun z : ℝ => z * v.1) h,
      congrArg (fun z : ℝ => z * v.2) h]

/-- The frame normalization used by `Pose.frame` has metric-unit length. -/
theorem pose_frame_norm (p : Pose) (w : ℂ) :
    (4 / (1 - Complex.normSq p.a) ^ 2) * Complex.normSq (p.frame w) =
      Complex.normSq w := by
  have h : 1 - Complex.normSq p.a ≠ 0 := ne_of_gt (sub_pos.mpr p.inside)
  have hc : (1 - (Complex.normSq p.a : ℂ)) = ((1 - Complex.normSq p.a : ℝ) : ℂ) := by simp
  rw [Pose.frame, Complex.normSq_div, map_mul, map_mul, p.unit, hc]
  simp only [Complex.normSq_ofReal, mul_one]
  norm_num
  field_simp

/-- The variable-curvature candidate `f=x²` has the expected coefficient term
along vertical lines. This is the same conformal connection, not a second API. -/
theorem variable_vertical (x : ℝ) (v : ℝ × ℝ) :
    gamma (2 * x, 0) (0, 1) v = (-2 * x * v.2, 2 * x * v.1) := by
  ext <;> simp [gamma, dot] <;> ring

end Orbifold.ConnectionAssessment
