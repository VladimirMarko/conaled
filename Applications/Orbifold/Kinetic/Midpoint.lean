import Applications.Orbifold.Kinetic.EulerLagrange

noncomputable section
namespace Orbifold.Kinetic
open DiskConnection

def midpoint (x y : ℂ) : ℂ := (1/2 : ℝ) • (x+y)

def discrete (h : ℝ) (x y : ℂ) : ℝ :=
  2 * Complex.normSq (y-x) / (h * gap (midpoint x y)^2)

def d1 (h : ℝ) (x y : ℂ) : ℂ :=
  -(4/(h*gap (midpoint x y)^2) : ℝ) • (y-x) +
    (4*Complex.normSq (y-x)/(h*gap (midpoint x y)^3) : ℝ) • midpoint x y

def d2 (h : ℝ) (x y : ℂ) : ℂ :=
  (4/(h*gap (midpoint x y)^2) : ℝ) • (y-x) +
    (4*Complex.normSq (y-x)/(h*gap (midpoint x y)^3) : ℝ) • midpoint x y

theorem midpoint_inside {x y : ℂ} (hx : Complex.normSq x < 1)
    (hy : Complex.normSq y < 1) : Complex.normSq (midpoint x y) < 1 := by
  have hn := Complex.normSq_nonneg (y-x)
  simp only [midpoint,Complex.normSq_apply,scalar_re,scalar_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im] at *
  nlinarith

theorem discrete_d1 (h : ℝ) (x y : ℂ) (hh : h ≠ 0)
    (hg : gap (midpoint x y) ≠ 0) :
    HasFDerivAt (fun z => discrete h z y) (covector (d1 h x y)) x := by
  have hd := (hasFDerivAt_const (𝕜 := ℝ) y x).sub (hasFDerivAt_id (𝕜 := ℝ) x)
  have hm := ((hasFDerivAt_id (𝕜 := ℝ) x).add (hasFDerivAt_const (𝕜 := ℝ) y x)).const_smul (1/2 : ℝ)
  have hn := ((normSq_fderiv (y-x)).comp x hd).const_mul 2
  have hg' := (((gap_fderiv (midpoint x y)).comp x hm).pow 2).const_mul h
  have H := quotient_fderiv hn hg' (mul_ne_zero hh (pow_ne_zero 2 hg))
  convert H using 1
  · rfl
  · ext w
    simp only [d1,covector,add_apply,smul_apply,sub_apply,zero_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
      Complex.reCLM_apply,Complex.imCLM_apply,Complex.add_re,Complex.add_im,
      Complex.sub_re,Complex.sub_im,scalar_re,scalar_im,smul_eq_mul,
      Function.comp_apply,Pi.smul_apply,Pi.sub_apply,Pi.add_apply,id_eq,Complex.zero_re,Complex.zero_im]
    simp only [midpoint] at hg ⊢
    field_simp
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    ring

theorem discrete_d2 (h : ℝ) (x y : ℂ) (hh : h ≠ 0)
    (hg : gap (midpoint x y) ≠ 0) :
    HasFDerivAt (discrete h x) (covector (d2 h x y)) y := by
  have hd := (hasFDerivAt_id (𝕜 := ℝ) y).sub (hasFDerivAt_const (𝕜 := ℝ) x y)
  have hm := ((hasFDerivAt_const (𝕜 := ℝ) x y).add (hasFDerivAt_id (𝕜 := ℝ) y)).const_smul (1/2 : ℝ)
  have hn := ((normSq_fderiv (y-x)).comp y hd).const_mul 2
  have hg' := (((gap_fderiv (midpoint x y)).comp y hm).pow 2).const_mul h
  have H := quotient_fderiv hn hg' (mul_ne_zero hh (pow_ne_zero 2 hg))
  convert H using 1
  · rfl
  · ext w
    simp only [d2,covector,add_apply,smul_apply,sub_apply,zero_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
      Complex.reCLM_apply,Complex.imCLM_apply,Complex.add_re,Complex.add_im,
      Complex.sub_re,Complex.sub_im,scalar_re,scalar_im,smul_eq_mul,
      Function.comp_apply,Pi.smul_apply,Pi.sub_apply,Pi.add_apply,id_eq,Complex.zero_re,Complex.zero_im]
    simp only [midpoint] at hg ⊢
    field_simp
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    ring

end Orbifold.Kinetic
