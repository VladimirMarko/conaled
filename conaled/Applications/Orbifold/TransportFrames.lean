import Applications.Orbifold.TransportComparison

/-! Experimental observations of parallel frames through pose and matrix realizations.
The terminal pose is constructed from the transported frame, not from an
arbitrary motion increment. -/
noncomputable section
open scoped ComplexConjugate
open CategoryTheory MulAction
namespace Orbifold.DiskTransport
open DiskConnection
namespace Path
variable {x y : Disk}

theorem transport_mul (p : Path x y) (v w : ℂ) :
    p.transport (v * w) = p.transport v * w := by
  induction p generalizing v with
  | nil => rfl
  | cons s p ih =>
    change p.transport (s.transport (v * w)) = p.transport (s.transport v) * w
    rw [show s.transport (v * w) = s.transport v * w by
      simp [Segment.transport, ParallelTransport.scalar]; ring]
    exact ih _

/-- Unit phase recovered from the transported metric-unit frame. -/
def terminalPhase (p : Path x y) (q : Pose) : ℂ :=
  2 * p.transport (q.frame 1) / (gap y.val : ℂ)

theorem terminalPhase_unit (p : Path x y) (q : Pose) (hx : q.a = x.val) :
    Complex.normSq (p.terminalPhase q) = 1 := by
  have hg : gap y.val ≠ 0 := ne_of_gt (sub_pos.mpr ((disk_mem _).mp y.property))
  have hp := p.metric_preserved (q.frame 1)
  have hq := ConnectionAssessment.pose_frame_norm q 1
  have hm (z v : ℂ) : metric z v v = 4 / gap z ^ 2 * Complex.normSq v := by
    simp [metric, Complex.normSq_apply, Complex.mul_re]
  rw [hm, hm, ← hx] at hp
  change 4 / gap q.a ^ 2 * Complex.normSq (q.frame 1) = Complex.normSq 1 at hq
  rw [hq] at hp
  simp only [terminalPhase, map_mul, Complex.normSq_div, Complex.normSq_ofReal]
  norm_num at hp ⊢
  rw [div_eq_mul_inv, mul_assoc, mul_comm (Complex.normSq _), ← mul_assoc]
  simpa [div_eq_mul_inv, pow_two, mul_assoc, mul_comm, mul_left_comm] using hp

def terminalPose (p : Path x y) (q : Pose) (hx : q.a = x.val) : Pose where
  a := y.val
  u := p.terminalPhase q
  inside := (disk_mem _).mp y.property
  unit := p.terminalPhase_unit q hx

/-- Agreement holds for the entire real frame, not just its point or one vector. -/
theorem terminal_frame (p : Path x y) (q : Pose) (hx : q.a = x.val) (w : ℂ) :
    (p.terminalPose q hx).frame w = p.transport (q.frame w) := by
  have hg : (gap y.val : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (sub_pos.mpr ((disk_mem _).mp y.property))
  have hf : q.frame w = q.frame 1 * w := by simp [Pose.frame]; ring
  rw [hf, p.transport_mul]
  simp only [Pose.frame, terminalPose, terminalPhase]
  have hc : 1 - (Complex.normSq y.val : ℂ) = (gap y.val : ℂ) := by simp [gap]
  rw [hc]
  field_simp

/-- The certified matrix of the terminal pose observes the same transported
frame when applied to the normalized frame at the origin. -/
theorem terminal_matrix_frame (p : Path x y) (q : Pose) (hx : q.a = x.val) (w : ℂ) :
    MatrixDisk.frameAction (p.terminalPose q hx).matrix 0 (w / 2) =
      p.transport (q.frame w) := by
  rw [← p.terminal_frame q hx w]
  simp [MatrixDisk.frameAction, MatrixDisk.pose_derivative, Pose.derivative, Pose.frame]
  ring

/-- A lifted loop retains the path and an actual labeled closing arrow from its
terminal representative back to its initial representative. -/
structure ClosedLift (x : Disk) where
  endpoint : Disk
  path : Path x endpoint
  closing : (↑endpoint : ActionCategory QuarterTurn.C4 Disk) ⟶ (↑x : ActionCategory QuarterTurn.C4 Disk)

def ClosedLift.label {x : Disk} (l : ClosedLift x) : QuarterTurn.C4 := l.closing.hom

/-- Closing direction is endpoint to source: apply P first, then D(closing). -/
def ClosedLift.endomorphism {x : Disk} (l : ClosedLift x) (v : ℂ) : ℂ :=
  (l.label.val : ℂ) * l.path.transport v

theorem ClosedLift.closing_evidence {x : Disk} (l : ClosedLift x) :
    l.label • l.endpoint = x := l.closing.map_val

end Path
end Orbifold.DiskTransport
