import Applications.Orbifold.TimedCommands

/-! C4 changes of representative for timed execution and its frame observations.
The existing action groupoid retains symmetry labels and endpoint evidence. -/
noncomputable section
open MulAction CategoryTheory
namespace Orbifold.DiskTransport
open DiskConnection

theorem representative_frame (g : QuarterTurn.C4) (p : Pose) (w : ℂ) :
    (g • p).frame w = (g.val : ℂ) * p.frame w := by
  change (QuarterTurn.rotate g p).frame w = _
  simp [QuarterTurn.rotate, Pose.frame, map_mul, QuarterTurn.phase_unit]; ring

open scoped Manifold in
/-- The pose action pushes the frame by the existing manifold symmetry derivative. -/
theorem representative_manifold_frame (g : QuarterTurn.C4) (p : Pose) (w : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : Disk => g • z)
      (QuarterTurn.position p) (p.frame w) = (g • p).frame w := by
  rw [Orbifolds.QuarterTurn.disk_tangent, representative_frame]

theorem Control.equivariant (c : Control) (g : QuarterTurn.C4) (p : Pose) (t : ℝ) :
    c.trajectory (g • p) t = g • c.trajectory p t := by
  cases c with
  | move v => exact QuarterTurn.right_increment_equivariant _ g p
  | turn omega =>
    change spin (QuarterTurn.rotate g p) omega t = QuarterTurn.rotate g (spin p omega t)
    apply QuarterTurn.pose_ext <;> simp [spin, QuarterTurn.rotate, mul_assoc]
  | hold => rfl

theorem execute_equivariant (g : QuarterTurn.C4) (p : Pose) (cs : List Command) :
    execute (g • p) cs = g • execute p cs := by
  induction cs generalizing p with
  | nil => rfl
  | cons c cs ih =>
    change execute (c.control.trajectory (g • p) c.duration) cs = _
    rw [c.control.equivariant, ih]
    rfl

/-- A representative change is a labeled arrow, not a timed physical command. -/
def executionFunctor (cs : List Command) :
    ActionCategory QuarterTurn.C4 Pose ⥤ ActionCategory QuarterTurn.C4 Pose :=
  Orbifolds.actionFunctor (MonoidHom.id _) (fun p => execute p cs)
    (fun g p => execute_equivariant g p cs)

@[simp] theorem execution_label (cs : List Command)
    {p q : ActionCategory QuarterTurn.C4 Pose} (f : p ⟶ q) :
    ((executionFunctor cs).map f).hom = f.hom := rfl

theorem execution_arrow_evidence (cs : List Command)
    {p q : ActionCategory QuarterTurn.C4 Pose} (f : p ⟶ q) :
    @SMul.smul QuarterTurn.C4 Pose inferInstance f.hom (execute p.back cs) = execute q.back cs :=
  ((executionFunctor cs).map f).map_val

/-- The same body controls give the pushed velocity at every local clock time. -/
theorem representative_velocity (c : Control) (g : QuarterTurn.C4) (p : Pose) (t : ℝ) :
    (c.trajectory (g • p) t).frame c.velocity =
      (g.val : ℂ) * (c.trajectory p t).frame c.velocity := by
  rw [c.equivariant, representative_frame]

/-- Matrix and pose observations agree at every point of every command. -/
theorem command_matrix_frame (c : Control) (p : Pose) (t : ℝ) (w : ℂ) :
    MatrixDisk.frameAction (c.trajectory p t).matrix 0 (w / 2) =
      (c.trajectory p t).frame w := by
  simp [MatrixDisk.frameAction, MatrixDisk.pose_derivative, Pose.derivative, Pose.frame]
  ring

theorem execution_matrix_frame (p : Pose) (cs : List Command) (w : ℂ) :
    MatrixDisk.frameAction (execute p cs).matrix 0 (w / 2) = (execute p cs).frame w := by
  simpa [Control.trajectory] using command_matrix_frame .hold (execute p cs) 0 w

theorem move_representative_frame (g : QuarterTurn.C4) (p : Pose) (d : ℂ)
    (hd : Complex.normSq d = 1) (s t : ℝ) (w : ℂ) :
    (move (g • p) d hd s t).frame w = (g.val : ℂ) * (move p d hd s t).frame w := by
  rw [move, QuarterTurn.right_increment_equivariant, representative_frame]
  rfl

/-- The constructed path transport also commutes, despite its scalar certificate
being allowed to differ by a nonzero constant factor. -/
theorem Command.transport_equivariant (c : Command) (g : QuarterTurn.C4) (p : Pose) (w : ℂ) :
    (c.path (g • p)).transport ((g.val : ℂ) * w) =
      (g.val : ℂ) * (c.path p).transport w := by
  rcases c with ⟨c, T, hT⟩
  cases c with
  | move v =>
    change (moveSegment (g • p) (direction v) (direction_unit v) ‖v‖ T hT).transport
      ((g.val : ℂ) * w) = (g.val : ℂ) *
        (moveSegment p (direction v) (direction_unit v) ‖v‖ T hT).transport w
    simp only [Segment.transport, ParallelTransport.scalar_apply, moveSegment,
      move_representative_frame]
    have hg : (g.val : ℂ) ≠ 0 := g.val.ne_zero
    field_simp
  | turn omega =>
    change (Segment.hold _ T hT).transport _ = (g.val : ℂ) * (Segment.hold _ T hT).transport w
    rw [Segment.hold_transport, Segment.hold_transport]; rfl
  | hold =>
    change (Segment.hold _ T hT).transport _ = (g.val : ℂ) * (Segment.hold _ T hT).transport w
    rw [Segment.hold_transport, Segment.hold_transport]; rfl

theorem develop_transport_equivariant (g : QuarterTurn.C4) (p : Pose) (cs : List Command) (w : ℂ) :
    (develop (g • p) cs).transport ((g.val : ℂ) * w) =
      (g.val : ℂ) * (develop p cs).transport w := by
  induction cs generalizing p w with
  | nil => rfl
  | cons c cs ih =>
    change ((c.path (g • p)).append (develop (c.finish (g • p)) cs)).transport _ = _
    rw [Path.append_transport]
    change (develop (c.finish (g • p)) cs).transport ((c.path (g • p)).transport _) = _
    rw [c.transport_equivariant]
    change (develop (c.control.trajectory (g • p) c.duration) cs).transport _ = _
    rw [c.control.equivariant, ih]
    change _ = (g.val : ℂ) * ((c.path p).append (develop (c.finish p) cs)).transport w
    rw [Path.append_transport]
    rfl

/-- Every local framed trajectory is pushed forward; durations and controls stay fixed. -/
theorem trace_equivariant (g : QuarterTurn.C4) (p : Pose) (cs : List Command) :
    trace (g • p) cs = (trace p cs).map
      (fun q => (q.1, fun t => g • q.2 t)) := by
  induction cs generalizing p with
  | nil => rfl
  | cons c cs ih =>
    simp only [trace, List.map_cons]
    congr 1
    · congr 1; funext t; exact c.control.equivariant g p t
    · change trace (c.control.trajectory (g • p) c.duration) cs = _
      rw [c.control.equivariant, ih]
      rfl

/-- Agreement is independent of the certified matrix representative chosen. -/
theorem certified_execution_frame (p : Pose) (cs : List Command)
    (A : MatrixDisk.Certified)
    (hA : MatrixBackend.Hermitian.decode Pose.standardBasis diskForm A = (execute p cs).motion)
    (w : ℂ) : MatrixDisk.frameAction A.val.val 0 (w / 2) = (execute p cs).frame w := by
  rw [MatrixDisk.frameAction, MatrixDisk.derivative_of_decode_eq A (execute p cs) hA]
  simp [Pose.derivative, Pose.frame]
  ring
end Orbifold.DiskTransport
