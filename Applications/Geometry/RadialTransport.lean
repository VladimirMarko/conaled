import Applications.Geometry.RadialMetric
import Applications.Orbifolds.QuarterTurn
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Symmetry and solved radial/circular transport for the fixed conformal
metric. Straight radial parameters are not asserted to be affine geodesic time. -/
noncomputable section
namespace RadialMetric
open Complex
open scoped ComplexConjugate

theorem scale_rotation (g z : ℂ) (hg : normSq g = 1) : scale (g*z) = scale z := by
  simp [scale,map_mul,hg]

theorem gamma_rotation (g z u v : ℂ) (hg : normSq g = 1) :
    gamma (g*z) (g*u) (g*v) = g * gamma z u v := by
  have hc : conj g * g = 1 := by rw [← Complex.normSq_eq_conj_mul_self, hg]; norm_num
  calc
    _ = (conj g*g) * (g*gamma z u v) := by simp only [gamma,map_mul]; ring
    _ = _ := by rw [hc,one_mul]

theorem c4_normSq (g : Orbifolds.QuarterTurn.C4) : normSq (g.val : ℂ) = 1 := by
  rw [normSq_eq_norm_sq, Complex.norm_eq_one_of_mem_rootsOfUnity g.property]
  norm_num

theorem gamma_c4 (g : Orbifolds.QuarterTurn.C4) (z u v : ℂ) :
    gamma ((g.val : ℂ)*z) ((g.val : ℂ)*u) ((g.val : ℂ)*v) =
      (g.val : ℂ) * gamma z u v := gamma_rotation _ _ _ _ (c4_normSq g)

theorem scale_c4 (g : Orbifolds.QuarterTurn.C4) (z : ℂ) :
    scale ((g.val : ℂ)*z) = scale z := scale_rotation _ _ (c4_normSq g)

/-- The radial connection equation for a straight radial parameter. -/
theorem gamma_radial (x v : ℂ) (t : ℝ) :
    gamma (t*x) x v = (2*t*normSq x : ℝ) * v := by
  have hx := (Complex.normSq_eq_conj_mul_self (z := x)).symm
  simp only [gamma,map_mul,Complex.conj_ofReal]
  push_cast
  linear_combination 2 * (t : ℂ) * v * hx

def radialTransport (x : ℂ) (t : ℝ) (v : ℂ) : ℂ :=
  (Real.exp (-(t^2)*normSq x) : ℂ) * v

theorem radialTransport_derivative (x v : ℂ) (t : ℝ) :
    HasDerivAt (fun s => radialTransport x s v)
      (-gamma (t*x) x (radialTransport x t v)) t := by
  have h := (((hasDerivAt_id t).pow 2).neg.mul_const (normSq x)).exp
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t h).mul_const v
  convert hc using 1
  · rfl
  · rw [gamma_radial]
    simp [radialTransport]
    push_cast
    ring

theorem radialTransport_initial (x v : ℂ) : radialTransport x 0 v = v := by
  simp [radialTransport]

theorem radialTransport_endpoint (x v : ℂ) :
    radialTransport x 1 v = (Real.exp (-normSq x) : ℂ)*v := by simp [radialTransport]

/-- Along a circle the coefficient depends on its radius, not the chosen endpoint. -/
theorem gamma_circle (z v : ℂ) : gamma z (I*z) v = (2*normSq z : ℝ)*I*v := by
  have hz := (Complex.normSq_eq_conj_mul_self (z := z)).symm
  simp only [gamma]
  push_cast
  linear_combination 2 * I * v * hz

def circle (r t : ℝ) : ℂ := r * Complex.exp (t * I)
def circleTransport (r t : ℝ) (v : ℂ) : ℂ := Complex.exp ((-2*r^2*t : ℝ)*I) * v

theorem circle_derivative (r t : ℝ) : HasDerivAt (circle r) (I*circle r t) t := by
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)).mul_const I
  convert hc.cexp.const_mul (r : ℂ) using 1
  · rfl
  · simp [circle]; ring

theorem circle_normSq (r t : ℝ) : normSq (circle r t) = r^2 := by
  simp [circle, map_mul, normSq_eq_norm_sq, Complex.norm_exp]

theorem circleTransport_derivative (r t : ℝ) (v : ℂ) :
    HasDerivAt (fun s => circleTransport r s v)
      (-gamma (circle r t) (I*circle r t) (circleTransport r t v)) t := by
  have hr : HasDerivAt (fun s : ℝ => -2*r^2*s) (-2*r^2) t := by
    convert (hasDerivAt_id t).const_mul (-2*r^2) using 1 <;> simp
  have hc := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hr).mul_const I).cexp.mul_const v
  convert hc using 1
  · rfl
  · rw [gamma_circle,circle_normSq]
    simp [circleTransport]
    push_cast
    ring

@[simp] theorem circle_initial (r : ℝ) : circle r 0 = r := by simp [circle]

theorem circle_closed (r : ℝ) : circle r (2*Real.pi) = r := by
  simp [circle,Complex.ofReal_mul,Complex.exp_two_pi_mul_I]

@[simp] theorem circleTransport_initial (r : ℝ) (v : ℂ) : circleTransport r 0 v = v := by
  simp [circleTransport]

/-- A small nonzero circle has nonidentity transport, although its endpoint closes. -/
theorem circleTransport_nontrivial {r : ℝ} (hr : 0 < r) (hs : r^2 < 1/2) :
    circleTransport r (2*Real.pi) 1 ≠ 1 := by
  intro he
  simp only [circleTransport,mul_one] at he
  obtain ⟨n,hn⟩ := Complex.exp_eq_one_iff.mp he
  have hi := congrArg Complex.im hn
  push_cast at hi
  simp at hi
  rw [← Complex.ofReal_pow, Complex.ofReal_re] at hi
  have hp := Real.pi_pos
  have heq : (n : ℝ) = -2*r^2 := by nlinarith
  have hlo : (-1 : ℝ) < n := by rw [heq]; linarith
  have hhi : (n : ℝ) < 0 := by rw [heq]; nlinarith [sq_pos_of_pos hr]
  have hnlo : (-1 : ℤ) < n := by exact_mod_cast hlo
  have hnhi : n < 0 := by exact_mod_cast hhi
  omega

/-- Holding at the same endpoint solves the zero-speed connection equation. -/
theorem holdTransport_derivative (x v : ℂ) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => v) (-gamma x 0 v) t := by
  simpa [gamma] using hasDerivAt_const t v

end RadialMetric
