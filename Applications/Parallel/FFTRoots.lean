import Applications.Parallel.ComplexFFT
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Exact phase identities for scalar lowering. No approximate literals occur. -/
namespace Applications.Parallel.FFTScalar

noncomputable def phase (n k : Nat) : ℂ :=
  Complex.exp (((-(2 * Real.pi * k / n) : ℝ) : ℂ) * Complex.I)

theorem phase_coefficients (n k : Nat) :
    phase n k = (⟨Real.cos (-(2 * Real.pi * k / n)),
      Real.sin (-(2 * Real.pi * k / n))⟩ : ℂ) := by
  rw [phase, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    <;> ring

theorem phase_zero (n : Nat) : phase n 0 = 1 := by simp [phase]

theorem phase_pow (n k l : Nat) : phase n k ^ l = phase n (k * l) := by
  rw [phase, phase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem phase_ratio {n k d j : Nat} (hn : 0 < n) (hd : 0 < d)
    (h : d * k = j * n) : phase n k = phase d j := by
  apply congrArg Complex.exp
  congr 1
  apply congrArg (fun x : ℝ => (x : ℂ))
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have h' : (d : ℝ) * k = j * n := by exact_mod_cast h
  field_simp
  nlinarith

theorem phase_fourierRoot (s : Factor) : phase s.size 1 = s.fourierRoot := by
  rw [Factor.fourierRoot_eq_exp]
  unfold phase
  congr 1
  push_cast
  ring

theorem phase_two : phase 2 1 = -1 := by
  unfold phase
  have h : (((-(2 * Real.pi * (1 : Nat) / (2 : Nat)) : ℝ) : ℂ) * Complex.I) =
      -((Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [h, Complex.exp_neg_pi_mul_I]

theorem phase_quarter : phase 4 1 = -Complex.I := by
  unfold phase
  have h : (((-(2 * Real.pi * (1 : Nat) / (4 : Nat)) : ℝ) : ℂ) * Complex.I) =
      -(Real.pi : ℂ) / 2 * Complex.I := by push_cast; ring
  rw [h, Complex.exp_neg_pi_div_two_mul_I]

theorem phase_diagonal : phase 8 1 =
    (⟨Real.sqrt 2 / 2, -(Real.sqrt 2 / 2)⟩ : ℂ) := by
  rw [phase_coefficients]
  have h : -(2 * Real.pi * (1 : Nat) / (8 : Nat)) = -(Real.pi / 4) := by norm_num; ring
  rw [h]
  simp [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]

theorem phase_add (n k l : Nat) : phase n (k + l) = phase n k * phase n l := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_eight_odd (j : Nat) :
    phase 8 (1 + 2 * j) = phase 8 1 * (-Complex.I) ^ j := by
  rw [phase_add, ← phase_pow]
  have h : phase 8 2 = phase 4 1 := phase_ratio (by decide) (by decide) (by decide)
  rw [h, phase_quarter]

/-- Root powers at a composition node are exactly its children's roots. -/
theorem phase_child (s t : Factor) :
    phase (s.size * t.size) 1 ^ t.size = phase s.size 1 := by
  rw [phase_pow, one_mul]
  exact phase_ratio (Nat.mul_pos s.size_pos t.size_pos) s.size_pos (by omega)

end Applications.Parallel.FFTScalar
