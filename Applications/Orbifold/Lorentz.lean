import Applications.Orbifold.MatrixDisk

/-! Exact future oriented Lorentz coordinates for framed disk motions.
The real matrices and their actions are calculated independently of pose
composition. This module does not implement a numerical validator. -/
noncomputable section
open Matrix
namespace Orbifold.Lorentz

abbrev Vector := Fin 3 → ℝ
abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℝ

/-- Signature (-,+,+), in time-first coordinates. -/
def metric : Matrix3 := !![-1,0,0; 0,1,0; 0,0,1]

/-- Boost taking the base future vector to the disk point's hyperboloid lift. -/
def boost (a : ℂ) : Matrix3 :=
  let g := 1 - Complex.normSq a
  !![(1 + Complex.normSq a)/g, 2*a.re/g, 2*a.im/g;
     2*a.re/g, 1+2*a.re*a.re/g, 2*a.re*a.im/g;
     2*a.im/g, 2*a.re*a.im/g, 1+2*a.im*a.im/g]

/-- Spatial rotation; the time coordinate is fixed. -/
def rotation (u : ℂ) : Matrix3 :=
  !![1,0,0; 0,u.re,-u.im; 0,u.im,u.re]

/-- Independent real-matrix encoding B(a)R(u). -/
def encode (p : Pose) : Matrix3 := boost p.a * rotation p.u

private theorem gap_ne (a : ℂ) (h : Complex.normSq a < 1) :
    1 - Complex.normSq a ≠ 0 := ne_of_gt (sub_pos.mpr h)

@[simp] theorem boost_zero : boost 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [boost]

@[simp] theorem rotation_one : rotation 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [rotation]

@[simp] theorem encode_identity : encode Pose.identity = 1 := by
  simp [encode, Pose.identity]

theorem boost_preserves (a : ℂ) (ha : Complex.normSq a < 1) :
    (boost a).transpose * metric * boost a = metric := by
  have hg := gap_ne a ha
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [boost, metric, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> simp_all [Complex.normSq_apply] <;> ring_nf <;> simp

theorem rotation_preserves (u : ℂ) (hu : Complex.normSq u = 1) :
    (rotation u).transpose * metric * rotation u = metric := by
  have hu' : u.re * u.re + u.im * u.im = 1 := hu
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rotation, metric, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith

theorem encode_preserves (p : Pose) :
    (encode p).transpose * metric * encode p = metric := by
  rw [encode, Matrix.transpose_mul]
  calc
    (rotation p.u).transpose * (boost p.a).transpose * metric *
        (boost p.a * rotation p.u) =
      (rotation p.u).transpose * ((boost p.a).transpose * metric * boost p.a) *
        rotation p.u := by simp only [Matrix.mul_assoc]
    _ = metric := by rw [boost_preserves p.a p.inside, rotation_preserves p.u p.unit]

/-- Hermitian coordinates, used to prove the independent real multiplication law. -/
def hermitian (v : Vector) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v 0 : ℂ), (v 1 : ℂ) + (v 2 : ℂ) * Complex.I;
     (v 1 : ℂ) - (v 2 : ℂ) * Complex.I, (v 0 : ℂ)]

theorem hermitian_injective : Function.Injective hermitian := by
  intro v w h
  have h0 := congrArg (fun A => (A 0 0).re) h
  have h1 := congrArg (fun A => (A 0 1).re) h
  have h2 := congrArg (fun A => (A 0 1).im) h
  simp only [hermitian] at h0 h1 h2
  simp at h0 h1 h2
  ext i; fin_cases i <;> assumption

private def boostComplex (a : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1,a; star a,1]

private def rotationComplex (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![u,0; 0,1]

private theorem rotation_hermitian (u : ℂ) (hu : Complex.normSq u = 1) (v : Vector) :
    hermitian (rotation u *ᵥ v) = rotationComplex u * hermitian v * (rotationComplex u)ᴴ := by
  have hu' : u.re * u.re + u.im * u.im = 1 := hu
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [hermitian, rotation, rotationComplex, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;>
    try ring_nf
  all_goals linear_combination -(v 0) * hu'

private theorem boost_hermitian (a : ℂ) (ha : Complex.normSq a < 1) (v : Vector) :
    hermitian (boost a *ᵥ v) = ((1 / (1 - Complex.normSq a) : ℝ) : ℂ) •
      (boostComplex a * hermitian v * (boostComplex a)ᴴ) := by
  have hg := gap_ne a ha
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [hermitian, boost, boostComplex, Matrix.mulVec,
      dotProduct, Matrix.vecMul, Matrix.conjTranspose_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im, Complex.normSq_apply,
      -Complex.ofReal_div, -Complex.ofReal_sub, -Complex.ofReal_mul, -Complex.ofReal_add] <;>
    field_simp <;> ring_nf <;> simp_all [Complex.normSq_apply]
  all_goals
    have hg₁ : 1 - a.re ^ 2 - a.im ^ 2 ≠ 0 := by
      simpa [Complex.normSq_apply, pow_two, sub_sub] using hg
    have hg₂ : 1 - a.im ^ 2 - a.re ^ 2 ≠ 0 := by
      simpa [sub_sub, add_comm] using hg₁
    field_simp
    ring

theorem encode_hermitian (p : Pose) (v : Vector) :
    hermitian (encode p *ᵥ v) = ((1 / (1 - Complex.normSq p.a) : ℝ) : ℂ) •
      (p.matrix * hermitian v * p.matrixᴴ) := by
  have hm : boostComplex p.a * rotationComplex p.u = p.matrix := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [boostComplex, rotationComplex, Pose.matrix, Matrix.mul_apply, Fin.sum_univ_two]
  rw [encode, ← Matrix.mulVec_mulVec, boost_hermitian p.a p.inside,
    rotation_hermitian p.u p.unit, ← hm, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

private theorem gap_comp (p q : Pose) :
    1 - Complex.normSq (p.comp q).a =
      (1 - Complex.normSq p.a) * (1 - Complex.normSq q.a) /
        Complex.normSq (Pose.factor p q) := by
  have hb : Complex.normSq (p.u * q.a) < 1 := by simpa [map_mul, p.unit] using q.inside
  simpa [Pose.comp, Pose.factor, mul_assoc, map_mul, p.unit] using
    Pose.gyro_gap p.a (p.u * q.a) p.inside hb

theorem boost_det (a : ℂ) (ha : Complex.normSq a < 1) : (boost a).det = 1 := by
  have hg := gap_ne a ha
  simp [boost, Matrix.det_fin_three]
  field_simp
  simp only [Complex.normSq_apply]
  ring

theorem rotation_det (u : ℂ) (hu : Complex.normSq u = 1) : (rotation u).det = 1 := by
  simpa [rotation, Matrix.det_fin_three, Complex.normSq_apply, pow_two] using hu

theorem encode_det (p : Pose) : (encode p).det = 1 := by
  rw [encode, Matrix.det_mul, boost_det p.a p.inside, rotation_det p.u p.unit, one_mul]

theorem encode_future (p : Pose) : 0 < encode p 0 0 := by
  have h := Complex.normSq_nonneg p.a
  simpa [encode, boost, rotation, Matrix.mul_apply, Fin.sum_univ_three] using
    div_pos (show 0 < 1 + Complex.normSq p.a by linarith) (sub_pos.mpr p.inside)

private def sandwich (M X : Matrix (Fin 2) (Fin 2) ℂ) := M * X * Mᴴ

private theorem sandwich_mul (M N X : Matrix (Fin 2) (Fin 2) ℂ) :
    sandwich (M * N) X = sandwich M (sandwich N X) := by
  simp [sandwich, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private theorem sandwich_smul (M X : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) :
    sandwich M (c • X) = c • sandwich M X := by
  simp [sandwich]

private theorem sandwich_rescale (M X : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) :
    sandwich (c • M) X = (Complex.normSq c : ℂ) • sandwich M X := by
  simp only [sandwich, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  rw [mul_comm (star c) c]
  change (c * star c) • _ = _
  have hc : c * star c = (Complex.normSq c : ℂ) := Complex.mul_conj c
  rw [hc]

/-- Real matrix multiplication agrees with independent native gyro composition. -/
theorem encode_comp (p q : Pose) : encode (p.comp q) = encode p * encode q := by
  have hg₁ := gap_ne p.a p.inside
  have hg₂ := gap_ne q.a q.inside
  have hn : Complex.normSq (Pose.factor p q) ≠ 0 :=
    ne_of_gt (Complex.normSq_pos.mpr (Pose.factor_ne_zero p q))
  have hs : ((1 / (1 - Complex.normSq p.a) : ℝ) : ℂ) *
      ((1 / (1 - Complex.normSq q.a) : ℝ) : ℂ) * (Complex.normSq (Pose.factor p q) : ℂ) =
      ((1 / (1 - Complex.normSq (p.comp q).a) : ℝ) : ℂ) := by
    norm_cast
    rw [gap_comp]
    field_simp
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  apply hermitian_injective
  rw [← Matrix.mulVec_mulVec, encode_hermitian, encode_hermitian, encode_hermitian]
  change _ = _ • sandwich p.matrix (_ • sandwich q.matrix (hermitian v))
  rw [sandwich_smul, smul_smul, ← sandwich_mul, Pose.matrix_comp,
    sandwich_rescale, smul_smul, hs]
  rfl

/-- Stereographic decoding of the first column, not Klein projection. -/
def point (A : Matrix3) : ℂ :=
  ⟨A 1 0 / (A 0 0 + 1), A 2 0 / (A 0 0 + 1)⟩

/-- Differential of stereographic decoding on the two spatial frame columns. -/
def frame (A : Matrix3) (w : ℂ) : ℂ :=
  let d := A 0 0 + 1
  let e0 := A 0 1 * w.re + A 0 2 * w.im
  let e1 := A 1 1 * w.re + A 1 2 * w.im
  let e2 := A 2 1 * w.re + A 2 2 * w.im
  ⟨(e1 * d - A 1 0 * e0) / d^2, (e2 * d - A 2 0 * e0) / d^2⟩

@[simp] theorem point_encode (p : Pose) : point (encode p) = p.a := by
  have hg := gap_ne p.a p.inside
  apply Complex.ext <;>
    simp [point, encode, boost, rotation, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

@[simp] theorem frame_encode (p : Pose) (w : ℂ) : frame (encode p) w = p.frame w := by
  have hg := gap_ne p.a p.inside
  apply Complex.ext <;>
    simp [frame, encode, boost, rotation, Pose.frame, Matrix.mul_apply, Fin.sum_univ_three,
      Complex.mul_re, Complex.mul_im, -Complex.ofReal_sub, -Complex.ofReal_mul,
      -Complex.ofReal_add, -Complex.ofReal_div] <;>
    field_simp <;> simp only [Complex.normSq_apply] <;> ring

/-- Rotation recovered from decoded frame scale. -/
def turn (A : Matrix3) : ℂ :=
  (2 / (1 - Complex.normSq (point A)) : ℝ) • frame A 1

@[simp] theorem turn_encode (p : Pose) : turn (encode p) = p.u := by
  have hg := gap_ne p.a p.inside
  have hg' : (1 - (Complex.normSq p.a : ℂ)) ≠ 0 := by exact_mod_cast hg
  simp only [turn, point_encode, frame_encode, Pose.frame, mul_one, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_sub, Complex.ofReal_one]
  field_simp

private theorem pose_ext {p q : Pose} (ha : p.a = q.a) (hu : p.u = q.u) : p = q := by
  cases p; cases q; simp_all

/-- The explicitly restricted carrier of matrices of the form B(a)R(u).
No classification of all future Lorentz matrices is assumed. -/
abbrev Realized := {A : Matrix3 // A ∈ Set.range encode}

namespace Realized

def ofPose (p : Pose) : Realized := ⟨encode p, p, rfl⟩

/-- Coordinate decoding, not a choice of the image witness. -/
def decode (A : Realized) : Pose where
  a := point A.val
  u := turn A.val
  inside := by obtain ⟨p, hp⟩ := A.property; rw [← hp, point_encode]; exact p.inside
  unit := by obtain ⟨p, hp⟩ := A.property; rw [← hp, turn_encode]; exact p.unit

@[simp] theorem decode_ofPose (p : Pose) : decode (ofPose p) = p :=
  pose_ext (point_encode p) (turn_encode p)

@[simp] theorem encode_decode (A : Realized) : encode A.decode = A.val := by
  obtain ⟨p, hp⟩ := A.property
  have hA : A = ofPose p := Subtype.ext hp.symm
  rw [hA, decode_ofPose]; rfl

@[simp] theorem ofPose_decode (A : Realized) : ofPose A.decode = A :=
  Subtype.ext (encode_decode A)

theorem preserves (A : Realized) : A.val.transpose * metric * A.val = metric := by
  rw [← encode_decode A]; exact encode_preserves _

theorem orientation (A : Realized) : A.val.det = 1 := by
  rw [← encode_decode A]; exact encode_det _

theorem future (A : Realized) : 0 < A.val 0 0 := by
  rw [← encode_decode A]; exact encode_future _

/-- Actual real matrix multiplication. -/
def comp (A B : Realized) : Realized :=
  ⟨A.val * B.val, A.decode.comp B.decode, by simp [encode_comp]⟩

def identity : Realized := ⟨1, Pose.identity, encode_identity⟩

@[simp] theorem decode_comp (A B : Realized) :
    (A.comp B).decode = A.decode.comp B.decode := by
  have h : A.comp B = ofPose (A.decode.comp B.decode) := by
    apply Subtype.ext
    simp [comp, ofPose, encode_comp]
  rw [h, decode_ofPose]

@[simp] theorem decode_identity : identity.decode = Pose.identity := by
  have h : identity = ofPose Pose.identity := Subtype.ext encode_identity.symm
  rw [h, decode_ofPose]

end Realized

/-- Scalar inverse pose, used to establish closure of the independent Lorentz inverse. -/
def inversePose (p : Pose) : Pose where
  a := -(star p.u) * p.a
  u := star p.u
  inside := by simpa [map_mul, map_neg, Complex.normSq_conj, p.unit] using p.inside
  unit := by simpa using p.unit

private theorem comp_inversePose (p : Pose) : p.comp (inversePose p) = Pose.identity := by
  have hu : p.u * star p.u = 1 := by
    have h : p.u * star p.u = (Complex.normSq p.u : ℂ) := Complex.mul_conj p.u
    simpa [p.unit] using h
  have ha : p.a * star p.a = (Complex.normSq p.a : ℂ) := Complex.mul_conj p.a
  have hi : p.u * (inversePose p).a = -p.a := by
    simp only [inversePose]
    calc
      p.u * (-star p.u * p.a) = -(p.u * star p.u) * p.a := by ring
      _ = -p.a := by rw [hu]; ring
  have hg : 1 - (Complex.normSq p.a : ℂ) ≠ 0 := by
    exact_mod_cast gap_ne p.a p.inside
  apply pose_ext
  · change gyroAdd p.a (p.u * (inversePose p).a) = 0
    rw [hi]; simp [gyroAdd]
  · change gyration p.a (p.u * (inversePose p).a) * p.u * star p.u = 1
    rw [hi, mul_assoc, hu, mul_one]
    simp only [gyration, map_neg, mul_neg, ← sub_eq_add_neg]
    change (1 - p.a * star p.a) / (1 - star p.a * p.a) = 1
    rw [mul_comm (star p.a) p.a, ha, div_self hg]

/-- Algebraic Lorentz inverse J Aᵀ J. -/
def inverse (A : Matrix3) : Matrix3 := metric * A.transpose * metric

@[simp] theorem metric_mul_self : metric * metric = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [metric, Matrix.mul_apply, Fin.sum_univ_three]

theorem inverse_encode (p : Pose) : inverse (encode p) = encode (inversePose p) := by
  have hl : inverse (encode p) * encode p = 1 := by
    calc
      _ = metric * ((encode p).transpose * metric * encode p) := by
        simp only [inverse, Matrix.mul_assoc]
      _ = 1 := by rw [encode_preserves, metric_mul_self]
  have hr : encode p * encode (inversePose p) = 1 := by
    rw [← encode_comp, comp_inversePose, encode_identity]
  calc
    inverse (encode p) = inverse (encode p) * (encode p * encode (inversePose p)) := by rw [hr, mul_one]
    _ = encode (inversePose p) := by rw [← Matrix.mul_assoc, hl, one_mul]

namespace Realized

/-- The usual Lorentz inverse, with closure proved using the independently calculated encoding. -/
def inv (A : Realized) : Realized :=
  ⟨inverse A.val, inversePose A.decode, by rw [← inverse_encode, encode_decode]⟩

@[simp] theorem decode_inv (A : Realized) : A.inv.decode = inversePose A.decode := by
  have h : A.inv = ofPose (inversePose A.decode) := by
    apply Subtype.ext
    simp [inv, ofPose, ← inverse_encode]
  rw [h, decode_ofPose]

/-- Fold of independent real matrices; empty input uses the real identity matrix. -/
def composeList : List Realized → Realized
  | [] => identity
  | A :: As => A.comp (composeList As)

theorem decode_composeList (As : List Realized) :
    (composeList As).decode = Pose.composeList (As.map decode) := by
  induction As with
  | nil => exact decode_identity
  | cons A As ih => simp [composeList, Pose.composeList, ih]

theorem composeList_matrix (As : List Realized) :
    (composeList As).val = (As.map Subtype.val).prod := by
  induction As with
  | nil => rfl
  | cons A As ih =>
    change A.val * (composeList As).val = A.val * (As.map Subtype.val).prod
    rw [ih]

@[simp] theorem point_decode (A : Realized) : point A.val = A.decode.a := rfl

theorem frame_decode (A : Realized) (w : ℂ) : frame A.val w = A.decode.frame w := by
  rw [← encode_decode A, frame_encode]

end Realized

/-- The rotation-free frame at any valid disk point. -/
def atPoint (z : Disk) : Pose :=
  ⟨z.val, 1, (disk_mem _).mp z.property, by norm_num⟩

@[simp] theorem encode_atPoint (z : Disk) : encode (atPoint z) = boost z.val := by
  simp [encode, atPoint]

/-- Linear Lorentz point action followed by stereographic observation. -/
def pointAction (A : Matrix3) (z : Disk) : ℂ := point (A * boost z.val)

/-- Transport an arbitrary tangent vector through a rotation-free input frame,
then decode the output tangent by the stereographic differential. -/
def frameAction (A : Matrix3) (z : Disk) (v : ℂ) : ℂ :=
  frame (A * boost z.val) ((2 / (1 - Complex.normSq z.val) : ℝ) • v)

@[simp] theorem pointAction_encode (p : Pose) (z : Disk) :
    pointAction (encode p) z = (p.act z : ℂ) := by
  rw [pointAction, ← encode_atPoint, ← encode_comp, point_encode, Pose.act_formula]
  simp [Pose.comp, atPoint, gyroAdd, mul_assoc]

@[simp] theorem frameAction_encode (p : Pose) (z : Disk) (v : ℂ) :
    frameAction (encode p) z v = p.derivative z.val * v := by
  rw [frameAction, ← encode_atPoint, ← encode_comp, frame_encode, Pose.frame_comp]
  have hg : (1 - (Complex.normSq z.val : ℂ)) ≠ 0 := by
    exact_mod_cast gap_ne z.val ((disk_mem _).mp z.property)
  congr 1
  simp only [atPoint, Pose.frame, mul_one, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_sub, Complex.ofReal_one]
  field_simp

theorem pointAction_inside (A : Realized) (z : Disk) :
    Complex.normSq (pointAction A.val z) < 1 := by
  rw [← A.encode_decode, pointAction_encode]
  exact (disk_mem _).mp (A.decode.act z).property

/-- Every independent valid matrix gets the native point action. -/
theorem pointAction_decode (A : Realized) (z : Disk) :
    pointAction A.val z = (A.decode.act z : ℂ) := by
  rw [← A.encode_decode, pointAction_encode]

/-- Every independent valid matrix gets the native action on arbitrary tangents. -/
theorem frameAction_decode (A : Realized) (z : Disk) (v : ℂ) :
    frameAction A.val z v = A.decode.derivative z.val * v := by
  rw [← A.encode_decode, frameAction_encode]

/-- The complete frame consumer; no fixed tangent direction is selected. -/
theorem composed_frame (A B : Realized) (w : ℂ) :
    frame (A.val * B.val) w = A.decode.derivative B.decode.a * B.decode.frame w := by
  rw [← A.encode_decode, ← B.encode_decode, ← encode_comp, frame_encode, Pose.frame_comp]

theorem finite_point (As : List Realized) :
    point (As.map Subtype.val).prod = (Pose.composeList (As.map Realized.decode)).a := by
  rw [← Realized.composeList_matrix, Realized.point_decode, Realized.decode_composeList]

theorem finite_frame (As : List Realized) (w : ℂ) :
    frame (As.map Subtype.val).prod w = (Pose.composeList (As.map Realized.decode)).frame w := by
  rw [← Realized.composeList_matrix, Realized.frame_decode, Realized.decode_composeList]

/-- The actual future unit hyperboloid, time coordinate first. -/
def Future (X : Vector) : Prop :=
  -(X 0)^2 + (X 1)^2 + (X 2)^2 = -1 ∧ 0 < X 0

theorem Realized.future_column (A : Realized) : Future (fun i => A.val i 0) := by
  refine ⟨?_, A.future⟩
  have h := congrArg (fun M : Matrix3 => M 0 0) A.preserves
  simp [metric, Matrix.mul_apply, Fin.sum_univ_three] at h
  nlinarith

/-- Point action really applies the real linear matrix to a future-sheet lift. -/
theorem pointAction_future (A : Realized) (z : Disk) :
    Future (fun i => (A.val * boost z.val) i 0) := by
  have h := (A.comp (Realized.ofPose (atPoint z))).future_column
  simpa [Realized.comp, Realized.ofPose, encode_atPoint] using h

theorem inverse_mul (A : Realized) : inverse A.val * A.val = 1 := by
  calc
    _ = metric * (A.val.transpose * metric * A.val) := by simp [inverse, Matrix.mul_assoc]
    _ = 1 := by rw [A.preserves, metric_mul_self]

theorem mul_inverse (A : Realized) : A.val * inverse A.val = 1 := by
  rw [← A.encode_decode, inverse_encode, ← encode_comp, comp_inversePose, encode_identity]

namespace Realized

/-- Validity is discharged once; ordinary callers receive a disk point. -/
def act (A : Realized) (z : Disk) : Disk :=
  ⟨pointAction A.val z, (disk_mem _).mpr (pointAction_inside A z)⟩

@[simp] theorem act_decode (A : Realized) (z : Disk) : A.act z = A.decode.act z :=
  Subtype.ext (pointAction_decode A z)

theorem act_comp (A B : Realized) (z : Disk) :
    (A.comp B).act z = A.act (B.act z) := by
  simp only [act_decode, decode_comp, Pose.act_comp]

theorem act_identity (z : Disk) : identity.act z = z := by
  rw [act_decode, decode_identity]
  apply Subtype.ext
  rw [Pose.act_formula]
  simp [Pose.identity]

theorem inv_comp (A : Realized) : A.inv.comp A = identity :=
  Subtype.ext (inverse_mul A)

theorem comp_inv (A : Realized) : A.comp A.inv = identity :=
  Subtype.ext (mul_inverse A)

theorem act_inv (A : Realized) (z : Disk) : A.inv.act (A.act z) = z := by
  rw [← act_comp, inv_comp, act_identity]

end Realized

/-- Chain law for arbitrary tangent inputs, calculated through actual matrix products. -/
theorem frameAction_comp (A B : Realized) (z : Disk) (v : ℂ) :
    frameAction (A.val * B.val) z v =
      frameAction A.val (B.act z) (frameAction B.val z v) := by
  let C := B.comp (Realized.ofPose (atPoint z))
  have hC : C.val = B.val * boost z.val := by simp [C, Realized.comp, Realized.ofPose]
  have hz : C.decode.a = (B.act z).val := by
    change point C.val = pointAction B.val z
    rw [hC]; rfl
  rw [frameAction_decode A]
  change frame ((A.val * B.val) * boost z.val) _ =
    A.decode.derivative (B.act z).val * frame (B.val * boost z.val) _
  rw [Matrix.mul_assoc, ← hC, composed_frame, hz, ← Realized.frame_decode]

theorem frameAction_identity (z : Disk) (v : ℂ) : frameAction 1 z v = v := by
  rw [← encode_identity, frameAction_encode]
  simp [Pose.derivative, Pose.identity]

theorem frameAction_inverse (A : Realized) (z : Disk) (v : ℂ) :
    frameAction A.inv.val (A.act z) (frameAction A.val z v) = v := by
  rw [← frameAction_comp]
  change frameAction (inverse A.val * A.val) z v = v
  rw [inverse_mul, frameAction_identity]

theorem finite_pointAction (As : List Realized) (z : Disk) :
    pointAction (As.map Subtype.val).prod z =
      ((Pose.composeList (As.map Realized.decode)).act z : ℂ) := by
  rw [← Realized.composeList_matrix, pointAction_decode, Realized.decode_composeList]

theorem finite_frameAction (As : List Realized) (z : Disk) (v : ℂ) :
    frameAction (As.map Subtype.val).prod z v =
      (Pose.composeList (As.map Realized.decode)).derivative z.val * v := by
  rw [← Realized.composeList_matrix, frameAction_decode, Realized.decode_composeList]

theorem Realized.comp_assoc (A B C : Realized) : (A.comp B).comp C = A.comp (B.comp C) :=
  Subtype.ext (Matrix.mul_assoc A.val B.val C.val)

@[simp] theorem Realized.identity_comp (A : Realized) : Realized.identity.comp A = A :=
  Subtype.ext (one_mul A.val)

@[simp] theorem Realized.comp_identity (A : Realized) : A.comp Realized.identity = A :=
  Subtype.ext (mul_one A.val)

end Orbifold.Lorentz
