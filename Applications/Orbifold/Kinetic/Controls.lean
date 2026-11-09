import Applications.Orbifold.Kinetic.Midpoint

noncomputable section
namespace Orbifold.Kinetic
open DiskConnection

/-- The sign convention comes from the two actual partial derivatives. -/
def discreteEL (h : ℝ) (x y z : ℂ) : Prop := d2 h x y + d1 h y z = 0

theorem midpoint_rational_residual :
    (d2 1 0 (1/2) + d1 1 (1/2) (4/5)).re = 301663232/1540798875 := by
  norm_num [d1,d2,midpoint,gap,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,scalar_re,scalar_im]

theorem midpoint_rational_not_DEL : ¬ discreteEL 1 0 (1/2) (4/5) := by
  intro h
  have H := congrArg Complex.re h
  rw [midpoint_rational_residual] at H
  norm_num at H

def quartic (x y : ℝ) : ℝ := (y-x)^4

theorem quartic_d1 (x y : ℝ) :
    HasDerivAt (fun z => quartic z y) (-4*(y-x)^3) x := by
  convert ((hasDerivAt_const x y).sub (hasDerivAt_id x)).pow 4 using 1 <;>
    first | rfl | (simp only [Pi.sub_apply,id_eq]; ring)

theorem quartic_d2 (x y : ℝ) :
    HasDerivAt (quartic x) (4*(y-x)^3) y := by
  convert ((hasDerivAt_id y).sub (hasDerivAt_const y x)).pow 4 using 1 <;>
    first | rfl | (simp only [Pi.sub_apply,id_eq]; ring)

theorem quartic_mixed (x y : ℝ) :
    HasDerivAt (fun z => -4*(z-x)^3) (-12*(y-x)^2) y := by
  convert (((hasDerivAt_id y).sub (hasDerivAt_const y x)).pow 3).const_mul (-4) using 1 <;>
    simp <;> ring

theorem quartic_unique_recurrence (x y z : ℝ) :
    4*(y-x)^3 - 4*(z-y)^3 = 0 ↔ z = 2*y-x := by
  constructor
  · intro h
    have he : (y-x)^3 = (z-y)^3 := by linarith
    have he' : y-x = z-y := (by decide : Odd 3).pow_injective he
    linarith
  · intro h; rw [h]; ring

example (x : ℝ) : HasDerivAt (fun z => -4*(z-x)^3) 0 x := by
  simpa using quartic_mixed x x

theorem quartic_mixed_not_invertible (x : ℝ) :
    ¬ ∃ e : ℝ ≃L[ℝ] ℝ, HasFDerivAt (fun y => -4*(y-x)^3) (e : ℝ →L[ℝ] ℝ) x := by
  rintro ⟨e,he⟩
  have hz : HasDerivAt (fun y => -4*(y-x)^3) 0 x := by simpa using quartic_mixed x x
  have heq := he.unique hz.hasFDerivAt
  have h1 := congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) heq
  have hzero : e 1 = e 0 := by simpa using h1
  have := e.injective hzero
  norm_num at this

end Orbifold.Kinetic
