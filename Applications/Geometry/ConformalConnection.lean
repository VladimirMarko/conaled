import Applications.Geometry.ParallelTransport
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Experimental conformal coordinate connections on the real complex plane.
The Riemann curvature expression differentiates the connection coefficient;
Gaussian curvature is its metric-normalized sectional component. -/
noncomputable section
namespace ConformalConnection

/-- `b=conj(grad(log lambda))` for a conformal Levi-Civita connection. -/
def gamma (b : ℂ → ℂ) (z u v : ℂ) : ℂ := b z * u * v

/-- `R(1,I)I` in constant coordinate fields, with convention
`R(X,Y)Z = nabla_X nabla_Y Z - nabla_Y nabla_X Z`. -/
def curvatureVector (b : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (fun t : ℝ => gamma b (z + t) Complex.I Complex.I) 0 -
  deriv (fun t : ℝ => gamma b (z + t * Complex.I) 1 Complex.I) 0 +
  gamma b z 1 (gamma b z Complex.I Complex.I) -
  gamma b z Complex.I (gamma b z 1 Complex.I)

/-- The sectional curvature of the coordinate plane for `lambda²(dx²+dy²)`. -/
def gaussian (scale : ℂ → ℝ) (b : ℂ → ℂ) (z : ℂ) : ℝ :=
  (curvatureVector b z).re / scale z ^ 2

/-- Derivatives of the coefficient suffice to compute the actual curvature
expression, including its quadratic Christoffel terms. -/
theorem curvature_of_derivatives (b : ℂ → ℂ) (z bx byy : ℂ)
    (hx : HasDerivAt (fun t : ℝ => b (z + t)) bx 0)
    (hy : HasDerivAt (fun t : ℝ => b (z + t * Complex.I)) byy 0) :
    curvatureVector b z = -bx - byy * Complex.I := by
  unfold curvatureVector gamma
  rw [((hx.mul_const Complex.I).mul_const Complex.I).deriv,
    ((hy.mul_const 1).mul_const Complex.I).deriv]
  have hi := Complex.I_sq
  linear_combination bx * hi

/-- Uniqueness of a symmetric metric-compatible coefficient. This algebraic
argument needs no choice of basis or curvature assumption. -/
theorem metric_coefficient_unique {V : Type*} [AddCommGroup V]
    (g : V → V → ℝ)
    (gsub : ∀ u v w, g (u - v) w = g u w - g v w)
    (gsym : ∀ u v, g u v = g v u)
    (gnondeg : ∀ u, (∀ v, g u v = 0) → u = 0)
    (B C : V → V → V)
    (hB : ∀ u v, B u v = B v u) (hC : ∀ u v, C u v = C v u)
    (hm : ∀ u v w, g (B u v) w + g v (B u w) = g (C u v) w + g v (C u w)) :
    B = C := by
  let D := fun u v => B u v - C u v
  have hs (u v : V) : D u v = D v u := by dsimp [D]; rw [hB, hC]
  have hk (u v w : V) : g (D u v) w = -g (D u w) v := by
    dsimp [D]
    rw [gsub, gsub]
    have h := hm u v w
    rw [gsym v (B u w), gsym v (C u w)] at h
    linarith
  have hz (u v w : V) : g (D u v) w = 0 := by
    have h1 := hk u v w
    have h2 := hk v w u
    have h3 := hk w u v
    rw [hs u w] at h1
    rw [hs v u] at h2
    rw [hs w v] at h3
    linarith
  funext u v
  exact sub_eq_zero.mp (gnondeg (D u v) (hz u v))

end ConformalConnection
