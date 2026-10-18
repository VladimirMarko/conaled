import Applications.Orbifold.Disk
import Applications.Linear.Similitude
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Experimental disk poses. Gyro composition is defined by scalar formulas;
the matrix realization below has its own multiplication operation. -/
noncomputable section
open scoped ComplexConjugate
open Matrix
namespace Orbifold

/-- A disk displacement and a unit complex turn. -/
structure Pose where
  a : ℂ
  u : ℂ
  inside : Complex.normSq a < 1
  unit : Complex.normSq u = 1

/-- Möbius addition on scalar coordinates. Its disk domain is proved below. -/
def gyroAdd (a b : ℂ) := (a + b) / (1 + conj a * b)
def gyration (a b : ℂ) := (1 + a * conj b) / (1 + conj a * b)

theorem disk_gap (a b : ℂ) :
    Complex.normSq (1 + conj a * b) - Complex.normSq (a + b) =
      (1 - Complex.normSq a) * (1 - Complex.normSq b) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem disk_denominator (a b : ℂ) (ha : Complex.normSq a < 1)
    (hb : Complex.normSq b < 1) : 1 + conj a * b ≠ 0 := by
  intro h
  have hg := disk_gap a b
  rw [h, map_zero] at hg
  have hp := mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)
  have hn := Complex.normSq_nonneg (a + b)
  linarith

theorem gyroAdd_inside (a b : ℂ) (ha : Complex.normSq a < 1)
    (hb : Complex.normSq b < 1) : Complex.normSq (gyroAdd a b) < 1 := by
  rw [gyroAdd, Complex.normSq_div,
    div_lt_one (Complex.normSq_pos.mpr (disk_denominator a b ha hb))]
  have := disk_gap a b
  have := mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)
  linarith

theorem gyration_unit (a b : ℂ) (h : 1 + conj a * b ≠ 0) :
    Complex.normSq (gyration a b) = 1 := by
  have heq : 1 + a * conj b = conj (1 + conj a * b) := by simp
  rw [gyration, heq, Complex.normSq_div, Complex.normSq_conj]
  exact div_self (ne_of_gt (Complex.normSq_pos.mpr h))

namespace Pose

def comp (p q : Pose) : Pose where
  a := gyroAdd p.a (p.u * q.a)
  u := gyration p.a (p.u * q.a) * p.u * q.u
  inside := gyroAdd_inside _ _ p.inside (by simpa [map_mul, p.unit] using q.inside)
  unit := by
    rw [map_mul, map_mul, gyration_unit, p.unit, q.unit]
    · norm_num
    · exact disk_denominator _ _ p.inside (by simpa [map_mul, p.unit] using q.inside)

def identity : Pose := ⟨0, 1, by norm_num, by norm_num⟩

def matrix (p : Pose) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![p.u, p.a; conj p.a * p.u, 1]

theorem matrix_det (p : Pose) : p.matrix.det = p.u * (1 - (Complex.normSq p.a : ℂ)) := by
  simp [matrix, Matrix.det_fin_two]
  rw [← Complex.mul_conj]
  ring

theorem matrix_invertible (p : Pose) : p.matrix.det ≠ 0 := by
  rw [matrix_det]
  apply mul_ne_zero
  · intro h; have := p.unit; simp [h] at this
  · have := p.inside
    exact_mod_cast ne_of_gt (sub_pos.mpr this)

def matrixUnit (p : Pose) : (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero p.matrix p.matrix_invertible

def standardBasis := Pi.basisFun ℂ (Fin 2)

theorem matrix_preserves (p : Pose) :
    p.matrixᴴ * MatrixBackend.Hermitian.formMatrix standardBasis diskForm * p.matrix =
      ((1 - Complex.normSq p.a : ℝ) : ℂ) •
        MatrixBackend.Hermitian.formMatrix standardBasis diskForm := by
  have hu : conj p.u * p.u = 1 := by
    rw [mul_comm, Complex.mul_conj, p.unit]; norm_num
  have ha : conj p.a * p.a = (Complex.normSq p.a : ℂ) := by rw [mul_comm, Complex.mul_conj]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_two, MatrixBackend.Hermitian.formMatrix,
      LinearMap.toMatrix₂_apply, standardBasis, Pi.basisFun_apply, Matrix.conjTranspose_apply,
      sub_eq_add_neg] <;>
    ring_nf <;> simp_all [mul_comm]

def certified (p : Pose) : MatrixBackend.Hermitian.Certified standardBasis diskForm :=
  ⟨p.matrixUnit, (MatrixBackend.Hermitian.certified_iff _ _ _).mpr
    ⟨1 - Complex.normSq p.a, sub_pos.mpr p.inside, p.matrix_preserves⟩⟩

def motion (p : Pose) : Motion diskForm :=
  MatrixBackend.Hermitian.decode standardBasis diskForm p.certified

/-- Normalization after composition has a nonzero complex scalar factor. -/
def factor (p q : Pose) : ℂ := 1 + conj p.a * p.u * q.a

theorem factor_ne_zero (p q : Pose) : factor p q ≠ 0 := by
  simpa [factor, mul_assoc] using disk_denominator p.a (p.u * q.a) p.inside
    (by simpa [map_mul, p.unit] using q.inside)

theorem matrix_comp (p q : Pose) : p.matrix * q.matrix = factor p q • (p.comp q).matrix := by
  have hd := factor_ne_zero p q
  have hu : p.u * conj p.u = 1 := by rw [Complex.mul_conj, p.unit]; norm_num
  have hdc : conj (factor p q) ≠ 0 := by simpa using hd
  dsimp [factor] at hd hdc
  have hd2 : 1 + conj p.a * (p.u * q.a) ≠ 0 := by simpa [mul_assoc] using hd
  have hc2 : 1 + p.a * (conj p.u * conj q.a) ≠ 0 := by simpa [mul_assoc] using hdc
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matrix, comp, gyroAdd, gyration, factor, Matrix.mul_apply, Fin.sum_univ_two,
      map_mul, map_add, smul_eq_mul] <;>
    field_simp (disch := first | assumption | simpa only [mul_comm, mul_left_comm, mul_assoc] using hd | simpa only [mul_comm, mul_left_comm, mul_assoc] using hc2) <;>
    ring_nf <;> simp_all [mul_comm, mul_left_comm, mul_assoc]

  all_goals
    try apply Or.inl
    linear_combination -(q.u * conj q.a) * hu

theorem motion_comp (p q : Pose) : (p.comp q).motion = p.motion * q.motion := by
  let a : ℂˣ := Units.mk0 (factor p q) (factor_ne_zero p q)
  have h : p.certified * q.certified =
      MatrixBackend.Hermitian.rescale standardBasis diskForm a (p.comp q).certified := by
    apply Subtype.ext
    apply Units.ext
    rw [MatrixBackend.Hermitian.rescale_matrix]
    exact matrix_comp p q
  change _ = MatrixBackend.Hermitian.decode standardBasis diskForm p.certified *
    MatrixBackend.Hermitian.decode standardBasis diskForm q.certified
  rw [← map_mul, h, MatrixBackend.Hermitian.rescale_decode]
  rfl

@[simp] theorem motion_identity : identity.motion = 1 := by
  have h : identity.certified = 1 := by
    apply Subtype.ext; apply Units.ext
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [certified, matrixUnit, matrix, identity]
  change MatrixBackend.Hermitian.decode standardBasis diskForm identity.certified = 1
  rw [h, map_one]

/-- Finite sequences use independent scalar composition and matrix multiplication. -/
def composeList : List Pose → Pose
  | [] => identity
  | p :: ps => p.comp (composeList ps)

theorem motion_composeList (ps : List Pose) :
    (composeList ps).motion = (ps.map motion).prod := by
  induction ps with
  | nil => exact motion_identity
  | cons p ps ih => simp [composeList, motion_comp, ih]

def act (p : Pose) (z : Disk) : Disk := diskEquiv (p.motion • lineOfDisk z)

theorem act_formula (p : Pose) (z : Disk) :
    (p.act z : ℂ) = (p.a + p.u * z.val) / (1 + conj p.a * p.u * z.val) := by
  let L := MatrixBackend.Hermitian.decodeEquiv standardBasis diskForm p.certified
  have hn : (![z.val, 1] : DiskVector) ≠ 0 := by intro h; have := congrFun h 1; simp at this
  have hl : L.val ![z.val, 1] ≠ 0 := by simpa using L.val.injective.ne hn
  change (diskOfLine (p.motion • lineOfDisk z) : ℂ) = _
  rw [diskOfLine_eq _ (L.val ![z.val, 1]) hl rfl]
  change (Matrix.toLin standardBasis standardBasis p.matrix ![z.val, 1]) 0 /
    (Matrix.toLin standardBasis standardBasis p.matrix ![z.val, 1]) 1 = _
  simp [standardBasis, Matrix.toLin_eq_toLin', Matrix.toLin'_apply, matrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm]

theorem act_comp (p q : Pose) (z : Disk) : (p.comp q).act z = p.act (q.act z) := by
  unfold act
  rw [motion_comp, mul_smul]
  congr 2
  exact (diskEquiv.left_inv _).symm

def mobius (p : Pose) (z : ℂ) : ℂ := (p.a + p.u * z) / (1 + conj p.a * p.u * z)

theorem act_denominator (p : Pose) (z : Disk) : 1 + conj p.a * p.u * z.val ≠ 0 := by
  simpa [mul_assoc] using disk_denominator p.a (p.u * z.val) p.inside
    (by simpa [map_mul, p.unit] using (disk_mem _).mp z.property)

/-- Complex derivative of the disk action; this is not trajectory parallel transport. -/
def derivative (p : Pose) (z : ℂ) : ℂ :=
  (1 - (Complex.normSq p.a : ℂ)) * p.u / (1 + conj p.a * p.u * z)^2

theorem hasDerivAt_mobius (p : Pose) (z : Disk) :
    HasDerivAt p.mobius (p.derivative z.val) z.val := by
  have h := ((hasDerivAt_const z.val p.a).add ((hasDerivAt_id z.val).const_mul p.u)).div
    ((hasDerivAt_const z.val (1 : ℂ)).add
      ((hasDerivAt_id z.val).const_mul (conj p.a * p.u))) (act_denominator p z)
  convert h using 1
  · rfl
  · simp only [derivative, zero_add, Pi.add_apply, id_eq, mul_one]
    rw [← Complex.mul_conj]
    ring

/-- Curvature -1 orthonormal frame, expressed in disk tangent coordinates. -/
def frame (p : Pose) (w : ℂ) : ℂ := (1 - (Complex.normSq p.a : ℂ)) * p.u * w / 2

theorem gyro_gap (a b : ℂ) (ha : Complex.normSq a < 1) (hb : Complex.normSq b < 1) :
    1 - Complex.normSq (gyroAdd a b) =
      (1 - Complex.normSq a) * (1 - Complex.normSq b) / Complex.normSq (1 + conj a * b) := by
  rw [gyroAdd, Complex.normSq_div, ← disk_gap]
  have hn := ne_of_gt (Complex.normSq_pos.mpr (disk_denominator a b ha hb))
  field_simp (disch := simpa only [mul_comm] using hn)

/-- The derivative transports the entire frame under pose composition. -/
theorem frame_comp (p q : Pose) (w : ℂ) :
    (p.comp q).frame w = p.derivative q.a * q.frame w := by
  have hb : Complex.normSq (p.u * q.a) < 1 := by simpa [map_mul, p.unit] using q.inside
  have hd := disk_denominator p.a (p.u * q.a) p.inside hb
  have hc : conj (1 + conj p.a * (p.u * q.a)) ≠ 0 := by
    intro h; apply hd; simpa using congrArg conj h
  have hn : 1 + p.a * conj (p.u * q.a) = conj (1 + conj p.a * (p.u * q.a)) := by simp
  have hg : 1 - (Complex.normSq (gyroAdd p.a (p.u * q.a)) : ℂ) =
      (1 - (Complex.normSq p.a : ℂ)) * (1 - (Complex.normSq (p.u * q.a) : ℂ)) /
        (Complex.normSq (1 + conj p.a * (p.u * q.a)) : ℂ) := by
    exact_mod_cast gyro_gap p.a (p.u * q.a) p.inside hb
  simp only [frame, comp, hg, map_mul, p.unit, one_mul]
  rw [← Complex.mul_conj (1 + conj p.a * (p.u * q.a))]
  simp only [gyration, hn, derivative]
  have hd' : 1 + conj p.a * p.u * q.a ≠ 0 := by simpa [mul_assoc] using hd
  field_simp (disch := first | assumption | simpa only [mul_comm, mul_left_comm, mul_assoc] using hd | simpa only [mul_comm, mul_left_comm, mul_assoc] using hc)

theorem motion_injective : Function.Injective motion := by
  intro p q h
  obtain ⟨a, ha⟩ := (Similitude.motion_eq_iff
    (MatrixBackend.Hermitian.decodeEquiv standardBasis diskForm p.certified)
    (MatrixBackend.Hermitian.decodeEquiv standardBasis diskForm q.certified)).mp h
  have hm : p.certified = MatrixBackend.Hermitian.rescale standardBasis diskForm a q.certified := by
    apply (MatrixBackend.Hermitian.decodeEquiv standardBasis diskForm).injective
    simpa [MatrixBackend.Hermitian.rescale] using ha
  have he := congrArg (fun A : MatrixBackend.Hermitian.Certified standardBasis diskForm => A.val.val) hm
  rw [MatrixBackend.Hermitian.rescale_matrix] at he
  change p.matrix = (a : ℂ) • q.matrix at he
  have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) he
  have ha1 : (a : ℂ) = 1 := by simpa [matrix] using h11.symm
  have haa := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) he
  have huu := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) he
  simp only [ha1, one_smul] at haa huu
  cases p; cases q
  simp_all [matrix]

theorem comp_assoc (p q r : Pose) : (p.comp q).comp r = p.comp (q.comp r) := by
  apply motion_injective
  simp only [motion_comp, mul_assoc]

end Pose
end Orbifold
