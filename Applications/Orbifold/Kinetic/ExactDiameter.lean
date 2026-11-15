import Applications.Orbifold.Kinetic.Legendre
import Applications.Orbifold.Kinetic.Controls
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
open Set Filter
open scoped Topology
namespace Orbifold.Kinetic

theorem artanh_derivative {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    HasDerivAt Real.artanh (1/(1-x^2)) x := by
  have hm : 1-x ≠ 0 := ne_of_gt (by linarith [hx.2])
  have hp : 1+x ≠ 0 := ne_of_gt (by linarith [hx.1])
  have hq := ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).div
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) hm
  have hl := (hq.log (div_ne_zero hp hm)).const_mul (1/2 : ℝ)
  have he : Real.artanh =ᶠ[𝓝 x] (fun z => 1/2 * Real.log ((1+z)/(1-z))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact Real.artanh_eq_half_log ⟨le_of_lt hy.1,le_of_lt hy.2⟩
  convert hl.congr_of_eventuallyEq he using 1
  simp only [Pi.sub_apply,Pi.add_apply,Pi.div_apply,id_eq]
  have hs : 1-x^2 ≠ 0 := ne_of_gt (by nlinarith [hx.1,hx.2])
  field_simp
  ring

def exactAction (h x y : ℝ) : ℝ := 2*(Real.artanh y-Real.artanh x)^2/h

def exactD1 (h x y : ℝ) : ℝ := -4*(Real.artanh y-Real.artanh x)/(h*(1-x^2))
def exactD2 (h x y : ℝ) : ℝ := 4*(Real.artanh y-Real.artanh x)/(h*(1-y^2))

theorem exact_d1 (h x y : ℝ) (hx : x ∈ Ioo (-1) 1) :
    HasDerivAt (fun z => exactAction h z y) (exactD1 h x y) x := by
  have H := (((hasDerivAt_const x (Real.artanh y)).sub (artanh_derivative hx)).pow 2).const_mul 2 |>.div_const h
  convert H using 1
  · rfl
  · dsimp [exactD1]; simp only [div_mul_eq_div_div]; ring

theorem exact_d2 (h x y : ℝ) (hy : y ∈ Ioo (-1) 1) :
    HasDerivAt (exactAction h x) (exactD2 h x y) y := by
  have H := (((artanh_derivative hy).sub (hasDerivAt_const y (Real.artanh x))).pow 2).const_mul 2 |>.div_const h
  convert H using 1
  · rfl
  · dsimp [exactD2]; simp only [div_mul_eq_div_div]; ring

theorem exact_DEL_iff (h x y z : ℝ) (hh : 0 < h) (hy : y ∈ Ioo (-1) 1) :
    exactD2 h x y + exactD1 h y z = 0 ↔
      Real.artanh y-Real.artanh x = Real.artanh z-Real.artanh y := by
  have hd : h*(1-y^2) ≠ 0 := mul_ne_zero (ne_of_gt hh) (ne_of_gt (by nlinarith [hy.1,hy.2]))
  simp only [exactD1,exactD2]
  rw [← add_div,div_eq_zero_iff]
  simp only [hd,or_false]
  constructor <;> intro H <;> linarith

theorem native_exact_action (h s t : ℝ) (hh : h ≠ 0) :
    exactAction h (DiskTransport.timedRadius s t) (DiskTransport.timedRadius s (t+h)) = h*s^2/2 := by
  simp only [exactAction,DiskTransport.timedRadius,Real.artanh_tanh]
  field_simp
  ring

theorem native_action_integral (p : Pose) (d : ℂ) (hd : Complex.normSq d = 1) (s t h : ℝ) :
    (∫ r in t..(t+h), lagrangian (DiskTransport.move p d hd s r).a
      ((DiskTransport.move p d hd s r).frame (d*(s : ℂ)))) = h*s^2/2 := by
  simp_rw [native_energy p d hd s]
  simp [intervalIntegral.integral_const]

end Orbifold.Kinetic
