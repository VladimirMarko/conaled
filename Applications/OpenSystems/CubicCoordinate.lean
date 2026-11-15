import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-! Cubic coordinates for the bounded interconnection experiment #416.
The inverse is mathematical and noncomputable, not a numerical root solver. -/
noncomputable section
namespace Applications.OpenSystems.Cubic

def encode (x : ℝ) : ℝ := x + x^3

theorem factor (x y : ℝ) : encode y - encode x = (y-x)*(1+x^2+x*y+y^2) := by
  unfold encode; ring

theorem factor_ge_one (x y : ℝ) : 1 ≤ 1+x^2+x*y+y^2 := by
  nlinarith [sq_nonneg (x+y), sq_nonneg x, sq_nonneg y]

theorem strictMono : StrictMono encode := by
  intro x y h
  have := mul_pos (sub_pos.mpr h) (lt_of_lt_of_le zero_lt_one (factor_ge_one x y))
  rw [← factor] at this
  linarith

theorem surjective : Function.Surjective encode := by
  intro q
  have hp : 0 ≤ |q| + 1 := by positivity
  have hcube : 0 ≤ (|q|+1)^3 := pow_nonneg hp _
  have lo : encode (-(|q|+1)) ≤ q := by
    simp only [encode, neg_add_rev]
    nlinarith [neg_abs_le q]
  have hi : q ≤ encode (|q|+1) := by
    unfold encode
    linarith [le_abs_self q]
  have hc : Continuous encode := by unfold encode; fun_prop
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (by linarith : -(|q|+1) ≤ |q|+1)
    hc.continuousOn ⟨lo, hi⟩
  exact ⟨x, hx⟩

def equiv : ℝ ≃ ℝ := Equiv.ofBijective encode ⟨strictMono.injective, surjective⟩
def decode : ℝ → ℝ := equiv.symm

@[simp] theorem decode_encode (x : ℝ) : decode (encode x) = x := equiv.symm_apply_apply x
@[simp] theorem encode_decode (q : ℝ) : encode (decode q) = q := equiv.apply_symm_apply q
@[simp] theorem encode_zero : encode 0 = 0 := by norm_num [encode]
@[simp] theorem decode_zero : decode 0 = 0 := by simpa using decode_encode 0
@[simp] theorem encode_neg (x : ℝ) : encode (-x) = -encode x := by unfold encode; ring

theorem inverse_bound (x y : ℝ) : |decode x-decode y| ≤ |x-y| := by
  have h := factor (decode y) (decode x)
  simp only [encode_decode] at h
  rw [h, abs_mul, abs_of_nonneg (le_trans zero_le_one (factor_ge_one _ _))]
  nlinarith [abs_nonneg (decode x-decode y), factor_ge_one (decode y) (decode x)]

theorem decode_box {R q : ℝ} (h : |q| ≤ encode R) : |decode q| ≤ R := by
  rw [abs_le] at h ⊢
  constructor
  · apply strictMono.le_iff_le.mp
    simpa using h.1
  · apply strictMono.le_iff_le.mp
    simpa using h.2

theorem encode_box {R x : ℝ} (h : |x| ≤ R) : |encode x| ≤ encode R := by
  rw [abs_le] at h ⊢
  constructor
  · simpa using strictMono.monotone h.1
  · exact strictMono.monotone h.2

theorem derivative (x : ℝ) : HasDerivAt encode (1+3*x^2) x := by
  simpa [encode] using! HasDerivAt.add (hasDerivAt_id x) ((hasDerivAt_id x).pow 3)

theorem defect (x v h : ℝ) :
    encode (x+h*v) - (encode x+h*(1+3*x^2)*v) = 3*x*h^2*v^2+h^3*v^3 := by
  unfold encode; ring

theorem defect_fixture : encode (1+(1/4)*(-1)) -
    (encode 1+(1/4)*(1+3*(1:ℝ)^2)*(-1)) = 11/64 := by
  rw [defect]; norm_num

/-- Cubic-coordinate Euler remains in the encoded interval under the same step bound. -/
theorem euler_box {R x z h : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R) (hz : |z| ≤ R)
    (hh : 0 ≤ h) (hh' : h ≤ 1/3) :
    |encode x+h*(1+3*x^2)*(-x+z)| ≤ encode R := by
  have upper : ∀ x z : ℝ, |x| ≤ R → |z| ≤ R →
      encode x+h*(1+3*x^2)*(-x+z) ≤ encode R := by
    intro x z hx hz
    obtain ⟨hxl, hxu⟩ := abs_le.mp hx
    obtain ⟨hzl, hzu⟩ := abs_le.mp hz
    have ha : 0 ≤ 1+3*x^2 := by positivity
    have hb : 0 ≤ R^2+R*x+2/3 := by nlinarith [mul_nonneg hR (by linarith : 0 ≤ R+x)]
    have gap := mul_nonneg (sub_nonneg.mpr hxu) hb
    have step := mul_le_mul_of_nonneg_right hh' (mul_nonneg ha (sub_nonneg.mpr hxu))
    have input := mul_le_mul_of_nonneg_left hzu (mul_nonneg hh ha)
    unfold encode at *
    nlinarith
  apply abs_le.mpr
  constructor
  · have ht := upper (-x) (-z) (by simpa using hx) (by simpa using hz)
    rw [encode_neg] at ht
    nlinarith
  · exact upper x z hx hz

/-- Taylor defect here is an exact polynomial estimate, with no flow premise. -/
theorem defect_bound {R x v h : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R)
    (hv : |v| ≤ 2*R) (hh : 0 ≤ h) :
    |encode (x+h*v) - (encode x+h*(1+3*x^2)*v)| ≤ 12*R^3*h^2+8*R^3*h^3 := by
  rw [defect]
  calc
    _ ≤ |3*x*h^2*v^2|+|h^3*v^3| := abs_add_le _ _
    _ = 3*|x| *h^2*|v|^2+h^3*|v|^3 := by
      simp [abs_mul, abs_pow, abs_of_nonneg hh]
    _ ≤ 3*R*h^2*(2*R)^2+h^3*(2*R)^3 := by
      gcongr
    _ = _ := by ring

/-- Sensitivities of the transformed component before selecting suppliers. -/
theorem field_gain {R x x' z z' : ℝ} (hR : 0 ≤ R)
    (hx : |x| ≤ R) (hx' : |x'| ≤ R) (hz : |z| ≤ R) :
    |(1+3*x^2)*(-x+z)-(1+3*x'^2)*(-x'+z')| ≤
      (1+15*R^2)*|x-x'|+(1+3*R^2)*|z-z'| := by
  have ha : |1+3*x'^2| ≤ 1+3*R^2 := by
    rw [abs_of_nonneg (by positivity)]
    have hh := pow_le_pow_left₀ (abs_nonneg x') hx' 2
    rw [sq_abs] at hh
    nlinarith
  have hb : |(1+3*x^2)-(1+3*x'^2)| ≤ 6*R*|x-x'| := by
    have he : (1+3*x^2)-(1+3*x'^2) = 3*(x+x')*(x-x') := by ring
    rw [he, abs_mul, abs_mul]
    have hh : |x+x'| ≤ 2*R := (abs_add_le _ _).trans (by linarith)
    norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 3)]
    calc
      3 * |x+x'| * |x-x'| ≤ 3 * (2*R) * |x-x'| := by gcongr
      _ = _ := by ring
  have hc : |-x+z| ≤ 2*R := (abs_add_le _ _).trans (by rw [abs_neg]; linarith)
  have hd : |(-x+z)-(-x'+z')| ≤ |x-x'|+|z-z'| := by
    calc
      _ = |-(x-x')+(z-z')| := by congr 1; ring
      _ ≤ _ := by simpa only [abs_neg] using abs_add_le (-(x-x')) (z-z')
  have he : (1+3*x^2)*(-x+z)-(1+3*x'^2)*(-x'+z') =
      ((1+3*x^2)-(1+3*x'^2))*(-x+z)+(1+3*x'^2)*((-x+z)-(-x'+z')) := by ring
  rw [he]
  calc
    _ ≤ |((1+3*x^2)-(1+3*x'^2))*(-x+z)|+
        |(1+3*x'^2)*((-x+z)-(-x'+z'))| := abs_add_le _ _
    _ ≤ (6*R*|x-x'|)*(2*R)+(1+3*R^2)*(|x-x'|+|z-z'|) := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul hb hc (abs_nonneg _) (by positivity))
        (mul_le_mul ha hd (abs_nonneg _) (by positivity))
    _ = _ := by ring
end Applications.OpenSystems.Cubic
