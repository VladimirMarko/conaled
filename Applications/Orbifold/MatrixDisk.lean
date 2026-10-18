import Applications.Orbifold.Pose

/-! Disk-coordinate observations of the certified matrix realization.
The tangent action is the derivative of the matrix's fractional-linear map. -/
noncomputable section
open Matrix
namespace Orbifold.MatrixDisk
abbrev Certified := MatrixBackend.Hermitian.Certified Pose.standardBasis diskForm

def mobius (A : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) : ℂ :=
  (A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1)

def derivative (A : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) : ℂ :=
  A.det / (A 1 0 * z + A 1 1)^2

def frameAction (A : Matrix (Fin 2) (Fin 2) ℂ) (z w : ℂ) : ℂ := derivative A z * w

def coordinates (z : Disk) : MatrixBackend.Hermitian.PointCoordinates Pose.standardBasis diskForm :=
  ⟨![z.val, 1], by
    change (diskForm ![z.val, 1] ![z.val, 1]).re < 0
    rw [diskForm_self]
    simpa using sub_neg.mpr ((disk_mem _).mp z.property)⟩

theorem denominator (A : Certified) (z : Disk) : A.val.val 1 0 * z.val + A.val.val 1 1 ≠ 0 := by
  have h := (MatrixBackend.Hermitian.applyCoordinates Pose.standardBasis diskForm A (coordinates z)).property
  change (diskForm (A.val.val *ᵥ ![z.val, 1]) (A.val.val *ᵥ ![z.val, 1])).re < 0 at h
  have hn := negative_last_ne_zero _ h
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hn

theorem hasDerivAt_mobius (A : Certified) (z : Disk) :
    HasDerivAt (mobius A.val.val) (derivative A.val.val z.val) z.val := by
  have h := (((hasDerivAt_id z.val).const_mul (A.val.val 0 0)).add_const (A.val.val 0 1)).div
    (((hasDerivAt_id z.val).const_mul (A.val.val 1 0)).add_const (A.val.val 1 1)) (denominator A z)
  convert h using 1
  · rfl
  · simp only [derivative, Matrix.det_fin_two, id_eq, mul_one]
    ring

/-- Matrix point application observes the same projective action. -/
theorem action_formula (A : Certified) (z : Disk) :
    (diskEquiv (MatrixBackend.Hermitian.decode Pose.standardBasis diskForm A • lineOfDisk z) : ℂ) =
      mobius A.val.val z.val := by
  have h := (MatrixBackend.Hermitian.applicationSquare Pose.standardBasis diskForm).commutes
    (A, coordinates z)
  change MatrixBackend.Hermitian.pointDecode Pose.standardBasis diskForm
    (MatrixBackend.Hermitian.applyCoordinates Pose.standardBasis diskForm A (coordinates z)) =
      MatrixBackend.Hermitian.decode Pose.standardBasis diskForm A • lineOfDisk z at h
  rw [← h]
  change (diskOfLine _ : ℂ) = _
  rw [diskOfLine_eq _ (A.val.val *ᵥ ![z.val, 1]) _ rfl]
  simp [mobius, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] theorem pose_derivative (p : Pose) (z : ℂ) : derivative p.matrix z = p.derivative z := by
  rw [derivative, p.matrix_det]
  simp [Pose.matrix, Pose.derivative, mul_comm, add_comm]

theorem derivative_rescale (a : ℂ) (ha : a ≠ 0) (A : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    derivative (a • A) z = derivative A z := by
  unfold derivative
  simp only [Matrix.det_fin_two, Matrix.smul_apply, smul_eq_mul]
  rw [show a * A 1 0 * z + a * A 1 1 = a * (A 1 0 * z + A 1 1) by ring]
  rw [show a * A 0 0 * (a * A 1 1) - a * A 0 1 * (a * A 1 0) =
    a^2 * (A 0 0 * A 1 1 - A 0 1 * A 1 0) by ring, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero _ ha)

/-- Any certified representative of a pose has the same tangent action. -/
theorem derivative_of_decode_eq (A : Certified) (p : Pose)
    (h : MatrixBackend.Hermitian.decode Pose.standardBasis diskForm A = p.motion) (z : ℂ) :
    derivative A.val.val z = p.derivative z := by
  obtain ⟨a, ha⟩ := (Similitude.motion_eq_iff
    (MatrixBackend.Hermitian.decodeEquiv Pose.standardBasis diskForm A)
    (MatrixBackend.Hermitian.decodeEquiv Pose.standardBasis diskForm p.certified)).mp h
  have hm : A = MatrixBackend.Hermitian.rescale Pose.standardBasis diskForm a p.certified := by
    apply (MatrixBackend.Hermitian.decodeEquiv Pose.standardBasis diskForm).injective
    simpa [MatrixBackend.Hermitian.rescale] using ha
  rw [hm, MatrixBackend.Hermitian.rescale_matrix, derivative_rescale _ a.ne_zero]
  exact pose_derivative p z

/-- Matrix multiplication and gyro composition transport the same complete frame. -/
theorem frame_agreement (p q : Pose) (w : ℂ) :
    frameAction p.matrix q.a (q.frame w) = (p.comp q).frame w := by
  rw [frameAction, pose_derivative, Pose.frame_comp]

/-- Normalizing a product leaves its derivative at every coordinate unchanged. -/
theorem product_derivative (p q : Pose) (z : ℂ) :
    derivative (p.matrix * q.matrix) z = (p.comp q).derivative z := by
  rw [Pose.matrix_comp, derivative_rescale _ (Pose.factor_ne_zero _ _), pose_derivative]

end Orbifold.MatrixDisk
