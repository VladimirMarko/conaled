import Applications.Orbifold.Lorentz
import Examples.AtlasIsotropy
import Examples.DiskRealizations

/-! Independently represented Lorentz increments, full frame observations,
and controls distinguishing sheet, orientation, coordinates and labels. -/
noncomputable section
open Orbifold Orbifold.Lorentz Matrix CategoryTheory
namespace Examples.LorentzMotion

/-- The existing motion semantics synchronizes independently calculated implementations. -/
@[reducible] def representation : Squares.Rep :=
  ⟨Realized, Motion diskForm, fun A => A.decode.motion⟩

def compositionSquare : Squares.Square (Squares.product representation representation) representation where
  impl AB := AB.1.comp AB.2
  spec pq := pq.1 * pq.2
  commutes AB := by
    change (AB.1.comp AB.2).decode.motion = AB.1.decode.motion * AB.2.decode.motion
    rw [Realized.decode_comp, Pose.motion_comp]

def agreement := Squares.synchronize compositionSquare
  DiskRealizations.poseCompositionSquare (fun _ => rfl)

theorem finite_motion (As : List Realized) :
    (Realized.composeList As).decode.motion = (As.map (fun A => A.decode.motion)).prod := by
  rw [Realized.decode_composeList, Pose.motion_composeList, List.map_map]
  rfl

def firstPose : Pose := ⟨1/3, Complex.I, by norm_num, by norm_num⟩
def secondPose : Pose :=
  ⟨Complex.I/4, ⟨3/5,4/5⟩, by norm_num,
    by norm_num [Complex.normSq_apply]⟩

/-- These are literal real matrices supplied independently of the pose encoder. -/
def firstMatrix : Matrix3 := !![5/4,0,-3/4; 3/4,0,-5/4; 0,1,0]
def secondMatrix : Matrix3 := !![17/15,32/75,8/25; 0,3/5,-4/5; 8/15,68/75,17/25]

theorem first_encoding : encode firstPose = firstMatrix := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [firstPose, firstMatrix, encode, boost, rotation, Matrix.mul_apply, Fin.sum_univ_three]

theorem second_encoding : encode secondPose = secondMatrix := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [secondPose, secondMatrix, encode, boost, rotation, Matrix.mul_apply,
      Fin.sum_univ_three, Complex.normSq_apply]

def first : Realized := ⟨firstMatrix, firstPose, first_encoding⟩
def second : Realized := ⟨secondMatrix, secondPose, second_encoding⟩

@[simp] theorem decode_first : first.decode = firstPose := by
  have h : first = Realized.ofPose firstPose := Subtype.ext first_encoding.symm
  rw [h, Realized.decode_ofPose]

@[simp] theorem decode_second : second.decode = secondPose := by
  have h : second = Realized.ofPose secondPose := Subtype.ext second_encoding.symm
  rw [h, Realized.decode_ofPose]

/-- The expected point 1/11 follows through the general independent matrix consumer. -/
theorem composed_point : point (first.val * second.val) = (1/11 : ℂ) := by
  change point (first.comp second).val = _
  rw [Realized.point_decode, Realized.decode_comp, decode_first, decode_second]
  norm_num [Pose.comp, firstPose, secondPose, gyroAdd, Complex.ext_iff,
    Complex.div_re, Complex.div_im, Complex.normSq_apply]

/-- All directions, not just the first column's tangent vector. -/
theorem composed_full_frame (w : ℂ) :
    frame (first.val * second.val) w = ((-48 + 36*Complex.I)/121) * w := by
  rw [composed_frame, decode_first, decode_second]
  apply Complex.ext <;>
    norm_num [Pose.derivative, Pose.frame, firstPose, secondPose, Complex.mul_re,
      Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq_apply, map_ofNat] <;>
    ring_nf <;> norm_num [Complex.I_sq, show Complex.I ^ 4 = 1 by norm_num, map_ofNat] <;> ring

example : first.val * second.val ≠ second.val * first.val := by
  intro h
  have h01 := congrArg (fun A : Matrix3 => A 0 1) h
  norm_num [first, second, firstMatrix, secondMatrix, Matrix.mul_apply, Fin.sum_univ_three] at h01

example (w : ℂ) : frame first.val w = (4*Complex.I/9)*w := by
  rw [Realized.frame_decode, decode_first]
  norm_num [Pose.frame, firstPose]
  ring

example : first.val * first.inv.val = 1 := mul_inverse first
example : first.inv.val * first.val = 1 := inverse_mul first

/-- Independent real-matrix increments can be supplied in any finite sequence. -/
example (As : List Realized) (w : ℂ) :
    frame (As.map Subtype.val).prod w = (Pose.composeList (As.map Realized.decode)).frame w :=
  finite_frame As w

example (w : ℂ) : frame (([] : List Realized).map Subtype.val).prod w = w/2 := by
  rw [finite_frame]
  simp [Pose.composeList, Pose.identity, Pose.frame]

example (z : Disk) (v : ℂ) :
    frameAction first.val z v = firstPose.derivative z.val * v := by
  rw [frameAction_decode, decode_first]

/-- Apex position does not force the frame to have zero orientation. -/
example (w : ℂ) :
    frame (encode (QuarterTurn.rotation Orbifolds.QuarterTurn.quarterTurn)) w = Complex.I*w/2 := by
  rw [frame_encode]
  simp [Pose.frame, QuarterTurn.rotation, Orbifolds.QuarterTurn.quarterTurn]

example : point (encode (Orbifolds.QuarterTurn.quarterTurn • firstPose)) = Complex.I/3 := by
  rw [point_encode]
  simp [QuarterTurn.rotate, firstPose, Orbifolds.QuarterTurn.quarterTurn, HSMul.hSMul, SMul.smul,
    div_eq_mul_inv]

/-- Left representative changes and right body increments commute as required. -/
example (g : QuarterTurn.C4) (p h : Pose) :
    encode (g • p) * encode h = encode (g • p.comp h) := by
  rw [← encode_comp, QuarterTurn.right_increment_equivariant]

example (w : ℂ) :
    frame (encode (Orbifolds.QuarterTurn.quarterTurn • firstPose)) w =
      -(4/9 : ℂ) * w := by
  rw [frame_encode]
  norm_num [Pose.frame, QuarterTurn.rotate, firstPose, Orbifolds.QuarterTurn.quarterTurn,
    HSMul.hSMul, SMul.smul]
  ring

example (h : Pose) {p q : ActionCategory QuarterTurn.C4 Pose} (f : p ⟶ q) :
    ((QuarterTurn.incrementFunctor h).map f).hom = f.hom := QuarterTurn.increment_label h f

/-- Retain the existing selected closing label alongside its matrix realization.
The ineffective factor cannot be recovered from this geometric matrix. -/
def selected (k : AtlasIsotropy.C2) :=
  (AtlasIsotropy.selectedLabel k,
    Realized.ofPose (QuarterTurn.rotation (AtlasIsotropy.selectedLabel k).1))

example : (selected 1).2.val = (selected AtlasIsotropy.kernel).2.val := rfl
example : selected 1 ≠ selected AtlasIsotropy.kernel := by
  intro h
  have hk := congrArg (fun x => x.1.2 (0 : Fin 2)) h
  norm_num [selected, AtlasIsotropy.selectedLabel, AtlasIsotropy.close,
    AtlasIsotropy.kernel, Equiv.swap_apply_def] at hk

example : (-(1 : Matrix3)).transpose * metric * (-(1 : Matrix3)) = metric := by
  simp

example : (!![1,0,0; 0,1,0; 0,0,-1] : Matrix3).transpose * metric *
    !![1,0,0; 0,1,0; 0,0,-1] = metric := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [metric, Matrix.mul_apply, Fin.sum_univ_three]

/-- Wrong sheet is rejected even though -I preserves the quadratic form. -/
example : ¬ ∃ A : Realized, A.val = -(1 : Matrix3) := by
  rintro ⟨A, h⟩
  have hf := A.future
  rw [h] at hf
  norm_num at hf

/-- Future reflection has the wrong orientation. -/
example : ¬ ∃ A : Realized, A.val = !![1,0,0; 0,1,0; 0,0,-1] := by
  rintro ⟨A,h⟩
  have hd := A.orientation
  rw [h] at hd
  norm_num [Matrix.det_fin_three] at hd

/-- Klein and Poincaré observation differ on the same nonzero future vector. -/
example : first.val 1 0 / first.val 0 0 = (3/5 : ℝ) ∧ point first.val = (1/3 : ℂ) := by
  constructor
  · norm_num [first, firstMatrix]
  · rw [Realized.point_decode, decode_first]; rfl

end Examples.LorentzMotion
