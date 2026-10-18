import Applications.Orbifold.QuarterTurn
import Applications.Orbifold.MatrixDisk

/-! Independent matrix and gyro computations, synchronized by projective motion
semantics. These exact noncomputable cases retain basis, scale and frame data. -/
noncomputable section
open Orbifold MatrixBackend.Hermitian
namespace Examples.DiskRealizations

@[reducible] def poseRepresentation : Squares.Rep := ⟨Pose, Motion diskForm, Pose.motion⟩

def poseCompositionSquare : Squares.Square
    (Squares.product poseRepresentation poseRepresentation) poseRepresentation where
  impl p := p.1.comp p.2
  spec p := p.1 * p.2
  commutes p := Pose.motion_comp p.1 p.2

/-- The pullback square accepts any two independently represented equal motions. -/
def agreement := Squares.synchronize (compositionSquare Pose.standardBasis diskForm)
  poseCompositionSquare (fun _ => rfl)

theorem independent_products (A B : Certified Pose.standardBasis diskForm) (p q : Pose)
    (hp : decode Pose.standardBasis diskForm A = p.motion)
    (hq : decode Pose.standardBasis diskForm B = q.motion) :
    decode Pose.standardBasis diskForm (A * B) = (p.comp q).motion := by
  rw [map_mul, hp, hq, Pose.motion_comp]

theorem finite_products (ps : List Pose) :
    decode Pose.standardBasis diskForm (ps.map Pose.certified).prod =
      (Pose.composeList ps).motion := by
  rw [Pose.motion_composeList, map_list_prod, List.map_map]
  rfl

theorem independent_frames (A : Certified Pose.standardBasis diskForm) (p q : Pose)
    (h : decode Pose.standardBasis diskForm A = p.motion) (w : ℂ) :
    MatrixDisk.frameAction A.val.val q.a (q.frame w) = (p.comp q).frame w := by
  rw [MatrixDisk.frameAction, MatrixDisk.derivative_of_decode_eq A p h, Pose.frame_comp]

theorem finite_frames (ps : List Pose) (q : Pose) (w : ℂ) :
    MatrixDisk.frameAction ((ps.map Pose.certified).prod).val.val q.a (q.frame w) =
      ((Pose.composeList ps).comp q).frame w :=
  independent_frames _ _ _ (finite_products ps) w

/-- Displacement 1/5 followed by a positive quarter-turn of the frame. -/
def step : Pose := ⟨1/5, Complex.I, by norm_num, by norm_num⟩

example : step.frame 1 = (12/25 : ℂ) * Complex.I := by
  norm_num [step, Pose.frame]
  ring

example (q : Pose) (w : ℂ) :
    MatrixDisk.frameAction step.matrix q.a (q.frame w) = (step.comp q).frame w :=
  MatrixDisk.frame_agreement step q w

example : (Pose.composeList [step, step, step]).motion = step.motion * step.motion * step.motion := by
  rw [Pose.motion_composeList]
  simp [mul_assoc]

/-- Swap the positive and negative basis vectors. The form matrix changes too. -/
def swappedBasis := Pose.standardBasis.reindex (Equiv.swap (0 : Fin 2) 1)

example : formMatrix swappedBasis diskForm = !![-1, 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [formMatrix, LinearMap.toMatrix₂_apply, swappedBasis, Pose.standardBasis,
      Module.Basis.reindex_apply, Pi.basisFun_apply, Equiv.swap_apply_def]

example : decode swappedBasis diskForm
    (changeBasis Pose.standardBasis diskForm swappedBasis step.certified) = step.motion :=
  changeBasis_decode _ _ _ _

example : (changeBasis Pose.standardBasis diskForm swappedBasis step.certified).val.val =
    (basisMatrix Pose.standardBasis swappedBasis).inv * step.matrix *
      (basisMatrix Pose.standardBasis swappedBasis).val := changeBasis_matrix _ _ _ _

example : decode Pose.standardBasis diskForm
    (rescale Pose.standardBasis diskForm (Units.mk0 2 (by norm_num)) step.certified) = step.motion :=
  rescale_decode _ _ _ _

example : (rescale Pose.standardBasis diskForm (Units.mk0 2 (by norm_num)) step.certified).val.val ≠
    step.matrix := by
  rw [rescale_matrix]
  intro h
  have := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) h
  norm_num [Pose.certified, Pose.matrixUnit, Pose.matrix] at this

example : MulAction.stabilizer QuarterTurn.C4 Orbifolds.QuarterTurn.origin = ⊤ :=
  QuarterTurn.origin_stabilizer

example : MulAction.stabilizer QuarterTurn.C4 QuarterTurn.fifth = ⊥ :=
  QuarterTurn.nonzero_stabilizer _ (by norm_num [QuarterTurn.fifth])

example : MulAction.stabilizer QuarterTurn.C4 step = ⊥ := QuarterTurn.pose_stabilizer _

example : gyroAdd (1/5 : ℂ) (1/5) = 5/13 ∧ gyroAdd (1/5 : ℂ) (-1/5) = 0 :=
  QuarterTurn.quotient_addition_values

end Examples.DiskRealizations
