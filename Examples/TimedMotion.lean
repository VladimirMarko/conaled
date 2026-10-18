import Applications.Orbifold.CommandComparison
import Applications.Orbifold.MotionUniqueness
import Mathlib.Analysis.SpecialFunctions.Artanh

/-! Checked uses of timed command execution: interior apex crossing, labeled
representative changes, vertical turns, elapsed time, and frame observations. -/
noncomputable section
open Set CategoryTheory MulAction
namespace Examples.TimedMotion
open Orbifold Orbifold.DiskTransport

/-- Start one unit of metric distance before the apex on the real diameter. -/
def beforeApex : Pose where
  a := -(Real.tanh (1 / 2) : ℂ)
  u := 1
  inside := by simpa only [Complex.normSq_neg, Complex.normSq_ofReal, pow_two] using Real.tanh_sq_lt_one (1 / 2)
  unit := by norm_num

def forward : Command := ⟨.move 1, 2, by norm_num⟩

/-- The actual two-unit command reaches the apex at its interior local time `1`. -/
example : (forward.control.trajectory beforeApex 1).a = 0 := by
  simp [forward, Control.trajectory, direction, move_position, diameterPose,
    timedRadius, beforeApex, Pose.mobius]

example : (forward.control.trajectory beforeApex 1).frame 1 ≠ 0 := frame_one_nonzero _

/-- The source differs from that interior point, so this is not an apex hold. -/
example : beforeApex.a ≠ (forward.control.trajectory beforeApex 1).a := by
  have hzero : (forward.control.trajectory beforeApex 1).a = 0 := by
    simp [forward, Control.trajectory, direction, move_position, diameterPose,
      timedRadius, beforeApex, Pose.mobius]
  rw [hzero]
  intro h
  change -(Real.tanh (1 / 2) : ℂ) = 0 at h
  have ht : Real.tanh (1 / 2) = Real.tanh 0 := by
    rw [Real.tanh_zero]
    exact_mod_cast neg_eq_zero.mp h
  have := Real.tanh_injective ht
  norm_num at this

example (t : ℝ) :
    DiskConnection.metric (forward.control.trajectory beforeApex t).a
      ((forward.control.trajectory beforeApex t).frame 1)
      ((forward.control.trajectory beforeApex t).frame 1) = 1 := by
  simpa [forward] using control_move_speed beforeApex 1 t

example (t : ℝ) :
    DiskConnection.metric (forward.control.trajectory beforeApex t).a
      ((forward.control.trajectory beforeApex t).frame 1)
      ((forward.control.trajectory beforeApex t).frame Complex.I) = 0 := by
  simpa using frame_pair (forward.control.trajectory beforeApex t) 1 Complex.I

example (w : ℂ) : (forward.path beforeApex).transport (beforeApex.frame w) =
    (forward.finish beforeApex).frame w := command_move_transport beforeApex 1 2 (by norm_num) w

def regularPose : Pose := ⟨1 / 5, 1, by norm_num, by norm_num⟩

example : regularPose.a ≠ 0 := by norm_num [regularPose]

/-- A regular-point representative change pushes the whole local motion. -/
example (t : ℝ) :
    forward.control.trajectory (Orbifolds.QuarterTurn.quarterTurn • regularPose) t =
      Orbifolds.QuarterTurn.quarterTurn • forward.control.trajectory regularPose t :=
  forward.control.equivariant _ regularPose t

def step : Command := ⟨.move 1, 1, by norm_num⟩
def turnLeft : Command := ⟨.turn (Real.pi / 2), 1, by norm_num⟩
def corner : List Command := [step, turnLeft, step]

/-- Composition order and time are tested on a move–turn–move word. -/
example : execute regularPose corner =
    step.finish (turnLeft.finish (step.finish regularPose)) ∧
    (develop regularPose corner).duration = 3 := by
  constructor
  · rfl
  · rw [develop_duration]; norm_num [elapsed, corner, step, turnLeft]

example : (trace regularPose corner).length = 3 := rfl

example : trace regularPose corner = trace regularPose [step, turnLeft] ++
    trace (execute regularPose [step, turnLeft]) [step] :=
  trace_append regularPose [step, turnLeft] [step]

/-- The symmetry label survives the same finite execution. -/
example {p q : ActionCategory QuarterTurn.C4 Pose} (f : p ⟶ q) :
    ((executionFunctor corner).map f).hom = f.hom := execution_label corner f

example : execute regularPose [⟨.hold, 3, by norm_num⟩] = regularPose ∧
    elapsed [⟨.hold, 3, by norm_num⟩] = 3 := hold_execution regularPose 3 (by norm_num)

example : (spin regularPose 1 Real.pi).frame 1 ≠
    (Segment.hold (QuarterTurn.position regularPose) Real.pi (le_of_lt Real.pi_pos)).transport
      (regularPose.frame 1) := spin_half_turn regularPose

example (w : ℂ) : MatrixDisk.frameAction (execute regularPose corner).matrix 0 (w / 2) =
    (execute regularPose corner).frame w := execution_matrix_frame regularPose corner w

example (A : MatrixDisk.Certified)
    (hA : MatrixBackend.Hermitian.decode Pose.standardBasis diskForm A =
      (execute regularPose corner).motion) (w : ℂ) :
    MatrixDisk.frameAction A.val.val 0 (w / 2) = (execute regularPose corner).frame w :=
  certified_execution_frame regularPose corner A hA w

/-- This erroneous change rotates only the point and keeps its old attached phase. -/
def positionOnly : Pose where
  a := Complex.I / 5
  u := 1
  inside := by norm_num [Complex.normSq_div]
  unit := by norm_num

example : positionOnly.a = (Orbifolds.QuarterTurn.quarterTurn • regularPose).a := by
  change Complex.I / 5 = Complex.I * (1 / 5)
  ring

/-- Keeping the old frame gives a different initial velocity under the same control. -/
example : (step.control.trajectory positionOnly 0).frame step.control.velocity ≠
    (step.control.trajectory (Orbifolds.QuarterTurn.quarterTurn • regularPose) 0).frame
      step.control.velocity := by
  rw [Control.initial, Control.initial, representative_frame]
  norm_num [step, Control.velocity, positionOnly, regularPose, Pose.frame,
    Complex.normSq_div, Orbifolds.QuarterTurn.quarterTurn_scalar]
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

/-- The constructed move is the unique solution, with no supplied solution certificate. -/
example (f : ℝ → Pose) (h0 : f 0 = beforeApex)
    (hp : ∀ t ∈ Icc 0 2, HasDerivAt (fun r => (f r).a) ((f t).frame 1) t)
    (hf : ∀ t ∈ Icc 0 2, ∀ w : ℂ, HasDerivAt (fun r => (f r).frame w)
      (-DiskConnection.christoffel (f t).a ((f t).frame 1) ((f t).frame w)) t) :
    EqOn f (forward.control.trajectory beforeApex) (Icc 0 2) := by
  apply Control.unique forward.control beforeApex 2 (by norm_num) f h0 hp
  simpa [forward, Control.angularVelocity, Control.velocity, Pose.frame] using hf
end Examples.TimedMotion
