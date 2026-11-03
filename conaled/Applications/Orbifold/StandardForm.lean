import Applications.Orbifold.ProjectiveMotion

/-! The signature (1,1) witness used by the experimental disk model. -/
noncomputable section
open scoped ComplexConjugate
namespace Orbifold

abbrev DiskVector := Fin 2 → ℂ

/-- The standard indefinite Hermitian form, conjugate-linear in its first slot. -/
def diskForm : Form DiskVector :=
  Matrix.toLinearMapₛₗ₂' ℂ (starRingEnd ℂ) (RingHom.id ℂ) !![1, 0; 0, -1]

@[simp] theorem diskForm_apply (v w : DiskVector) :
    diskForm v w = conj (v 0) * w 0 - conj (v 1) * w 1 := by
  simp [diskForm, Matrix.toLinearMapₛₗ₂'_apply, Fin.sum_univ_two, sub_eq_add_neg]

theorem diskForm_hermitian : diskForm.IsSymm := by
  constructor
  intro v w
  simp [diskForm_apply, mul_comm]

theorem diskForm_nondegenerate (v : DiskVector) (h : ∀ w, diskForm v w = 0) : v = 0 := by
  have h0 := h ![1, 0]
  have h1 := h ![0, 1]
  simp at h0 h1
  ext i; fin_cases i <;> simp_all

/-- A negative vector exists; the construction is not vacuous. -/
def originLine : NegativeLine diskForm :=
  ⟨Projectivization.mk ℂ ![0, 1] (by intro h; have := congrFun h 1; simp at this),
    (negative_mk_iff _ _ _).mpr (by simp)⟩

/-- The positive coordinate direction witnesses indefiniteness. -/
theorem diskForm_positive : (diskForm ![1, 0] ![1, 0]).re = 1 := by simp

/-- A non-unit scalar changes the vector but fixes its projective motion. -/
def doubleScalar : Similitude diskForm :=
  Similitude.scalar diskForm (Units.mk0 2 (by norm_num))

example : doubleScalar.motion = 1 := Similitude.motion_scalar _

example : doubleScalar.val ![0, 1] ≠ ![0, 1] := by
  intro h
  have := congrFun h 1
  norm_num [doubleScalar, Similitude.scalar, LinearEquiv.smulOfUnit] at this

example : doubleScalar.motion • originLine = originLine := by simp [doubleScalar]

example (g : Motion diskForm) : ratio diskForm (g • originLine) (g • originLine) = 1 := by
  rw [ratio_preserved]
  rw [ratio_eq diskForm originLine originLine ![0, 1] ![0, 1]
    (by intro h; have := congrFun h 1; simp at this)
    (by intro h; have := congrFun h 1; simp at this) rfl rfl]
  norm_num [vectorRatio]

/-- A quarter-turn of the first coordinate preserves the form. -/
def turnLinear : DiskVector ≃ₗ[ℂ] DiskVector where
  toFun v := ![Complex.I * v 0, v 1]
  invFun v := ![-Complex.I * v 0, v 1]
  left_inv v := by ext i; fin_cases i <;> simp [← mul_assoc]
  right_inv v := by ext i; fin_cases i <;> simp [← mul_assoc]
  map_add' v w := by ext i; fin_cases i <;> simp [mul_add]
  map_smul' a v := by ext i; fin_cases i <;> simp [mul_left_comm]

def turn : Similitude diskForm := ⟨turnLinear, 1, zero_lt_one, by
  intro v w
  simp [turnLinear, mul_assoc]
  ring_nf
  simp [Complex.I_sq]⟩

/-- The line through (1/2,1) moves under the turn. -/
def halfLine : NegativeLine diskForm :=
  ⟨Projectivization.mk ℂ ![1/2, 1] (by intro h; have := congrFun h 1; simp at this),
    (negative_mk_iff _ _ _).mpr (by norm_num)⟩

theorem turn_moves_half : turn.motion • halfLine ≠ halfLine := by
  intro h
  have heq := congrArg Subtype.val h
  change Projectivization.mk ℂ (turnLinear ![1/2, 1]) _ =
    Projectivization.mk ℂ ![1/2, 1] _ at heq
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).mp heq
  have h1 := congrFun ha 1
  have h0 := congrFun ha 0
  have ha1 : (a : ℂ) = 1 := by simpa [turnLinear, Units.smul_def] using h1
  simp [turnLinear, Units.smul_def, ha1] at h0
  have := congrArg Complex.im h0
  norm_num at this

/-- Distinct points test the two-point invariant beyond its diagonal value. -/
example (g : Motion diskForm) : ratio diskForm (g • originLine) (g • halfLine) = 4/3 := by
  rw [ratio_preserved]
  rw [ratio_eq diskForm originLine halfLine ![0, 1] ![1/2, 1]
    (by intro h; have := congrFun h 1; simp at this)
    (by intro h; have := congrFun h 1; simp at this) rfl rfl]
  norm_num [vectorRatio]

end Orbifold
