import Applications.Orbifold.TimedMotion

/-! Experimental finite words of timed body controls. Each command retains its
local trajectory and duration; execution computes matching framed endpoints. -/
noncomputable section
open Set
open scoped ComplexConjugate
namespace Orbifold.DiskTransport
open DiskConnection

/-- The zero velocity uses an arbitrary unit direction and zero speed. -/
def direction (v : ℂ) : ℂ := if v = 0 then 1 else v / (‖v‖ : ℂ)

theorem direction_unit (v : ℂ) : Complex.normSq (direction v) = 1 := by
  by_cases h : v = 0
  · simp [direction, h]
  · simp only [direction, ite_eq_right h, Complex.normSq_div, Complex.normSq_ofReal]
    rw [Complex.normSq_eq_norm_sq, ← pow_two, div_self]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr h)

theorem direction_velocity (v : ℂ) : direction v * (‖v‖ : ℂ) = v := by
  by_cases h : v = 0
  · simp [h]
  · simp [direction, h, norm_ne_zero_iff.mpr h]

inductive Control where
  | move (velocity : ℂ)
  | turn (angularVelocity : ℝ)
  | hold

def Control.velocity : Control → ℂ
  | .move v => v
  | _ => 0

def Control.angularVelocity : Control → ℝ
  | .turn omega => omega
  | _ => 0

def Control.trajectory (c : Control) (p : Pose) (t : ℝ) : Pose :=
  match c with
  | .move v => Orbifold.DiskTransport.move p (direction v) (direction_unit v) ‖v‖ t
  | .turn omega => spin p omega t
  | .hold => p

@[simp] theorem Control.initial (c : Control) (p : Pose) : c.trajectory p 0 = p := by
  cases c <;> simp [Control.trajectory]

theorem Control.position_equation (c : Control) (p : Pose) (t : ℝ) :
    HasDerivAt (fun r => (c.trajectory p r).a)
      ((c.trajectory p t).frame c.velocity) t := by
  cases c with
  | move v => simpa [Control.trajectory, Control.velocity, direction_velocity] using move_velocity p (direction v) (direction_unit v) ‖v‖ t
  | turn omega => exact spin_velocity p omega t
  | hold => simpa [Control.trajectory, Control.velocity, Pose.frame] using! hasDerivAt_const t p.a

theorem Control.frame_equation (c : Control) (p : Pose) (t : ℝ) (w : ℂ) :
    HasDerivAt (fun r => (c.trajectory p r).frame w)
      ((c.trajectory p t).frame ((c.angularVelocity : ℂ) * Complex.I * w) -
        christoffel (c.trajectory p t).a ((c.trajectory p t).frame c.velocity)
          ((c.trajectory p t).frame w)) t := by
  cases c with
  | move v => simpa [Control.trajectory, Control.velocity, Control.angularVelocity,
      Pose.frame, christoffel, direction_velocity] using move_parallel p (direction v) (direction_unit v) ‖v‖ t w
  | turn omega => exact spin_equation p omega t w
  | hold => simpa [Control.trajectory, Control.velocity, Control.angularVelocity,
      Pose.frame, christoffel, coefficient] using! hasDerivAt_const t (p.frame w)

/-- Duration is independent of whether the underlying path changes position. -/
structure Command where
  control : Control
  duration : ℝ
  nonneg : 0 ≤ duration

def Command.finish (c : Command) (p : Pose) : Pose := c.control.trajectory p c.duration

def Command.path (c : Command) (p : Pose) : Path (QuarterTurn.position p) (QuarterTurn.position (c.finish p)) :=
  match c with
  | ⟨.move v, T, hT⟩ => .cons (moveSegment p (direction v) (direction_unit v) ‖v‖ T hT) (.nil _)
  | ⟨.turn _, T, hT⟩ => .cons (Segment.hold (QuarterTurn.position p) T hT) (.nil _)
  | ⟨.hold, T, hT⟩ => .cons (Segment.hold (QuarterTurn.position p) T hT) (.nil _)

@[simp] theorem Command.path_duration (c : Command) (p : Pose) :
    (c.path p).duration = c.duration := by
  rcases c with ⟨c, T, hT⟩
  cases c <;> simp [Command.path, Path.duration, moveSegment, Segment.hold]

@[simp] theorem Command.zero_duration (c : Control) (p : Pose) :
    (Command.mk c 0 le_rfl).finish p = p := c.initial p

def execute (p : Pose) : List Command → Pose
  | [] => p
  | c :: cs => execute (c.finish p) cs

/-- Developed position paths survive execution, including turn and hold clocks. -/
def develop (p : Pose) : (cs : List Command) → Path (QuarterTurn.position p) (QuarterTurn.position (execute p cs))
  | [] => .nil _
  | c :: cs => (c.path p).append (develop (c.finish p) cs)

def elapsed (cs : List Command) : ℝ := (cs.map Command.duration).sum

theorem execute_append (p : Pose) (cs ds : List Command) :
    execute p (cs ++ ds) = execute (execute p cs) ds := by
  induction cs generalizing p with
  | nil => rfl
  | cons c cs ih => exact ih (c.finish p)

theorem develop_duration (p : Pose) (cs : List Command) :
    (develop p cs).duration = elapsed cs := by
  induction cs generalizing p with
  | nil => rfl
  | cons c cs ih =>
    calc
      (develop p (c :: cs)).duration = (c.path p).duration + (develop (c.finish p) cs).duration :=
        Path.append_duration _ _
      _ = elapsed (c :: cs) := by rw [Command.path_duration, ih]; rfl

theorem elapsed_append (cs ds : List Command) :
    elapsed (cs ++ ds) = elapsed cs + elapsed ds := by simp [elapsed]

/-- Every hold retains its full duration while leaving the framed state fixed. -/
theorem hold_execution (p : Pose) (T : ℝ) (hT : 0 ≤ T) :
    execute p [⟨.hold, T, hT⟩] = p ∧ elapsed [⟨.hold, T, hT⟩] = T := by
  simp [execute, Command.finish, Control.trajectory, elapsed]

/-- Local clocks and the whole evolving framed state, including vertical turns. -/
def trace (p : Pose) : List Command → List (ℝ × (ℝ → Pose))
  | [] => []
  | c :: cs => (c.duration, c.control.trajectory p) :: trace (c.finish p) cs

theorem trace_append (p : Pose) (cs ds : List Command) :
    trace p (cs ++ ds) = trace p cs ++ trace (execute p cs) ds := by
  induction cs generalizing p with
  | nil => rfl
  | cons c cs ih =>
    simpa only [trace, execute, List.cons_append] using congrArg
      (List.cons (c.duration, c.control.trajectory p)) (ih (c.finish p))

/-- The next local clock starts at the preceding framed endpoint. -/
theorem command_joint (p : Pose) (c d : Command) :
    d.control.trajectory (c.finish p) 0 = c.control.trajectory p c.duration :=
  d.control.initial (c.finish p)

theorem develop_append_transport (p : Pose) (cs ds : List Command) :
    (develop p (cs ++ ds)).transport =
      (develop p cs).transport.trans (develop (execute p cs) ds).transport := by
  induction cs generalizing p with
  | nil => ext w; rfl
  | cons c cs ih =>
    change ((c.path p).append (develop (c.finish p) (cs ++ ds))).transport = _
    rw [Path.append_transport, ih]
    change _ = ((c.path p).append (develop (c.finish p) cs)).transport.trans _
    rw [Path.append_transport]
    rfl

theorem zero_duration_transport (c : Control) (p : Pose) :
    ((Command.mk c 0 le_rfl).path p).transport = LinearEquiv.refl ℝ ℂ := by
  cases c <;> ext w <;>
    simp [Command.path, Path.transport, Segment.hold,
      Segment.transport, moveSegment, ParallelTransport.scalar, frame_one_nonzero]

/-- Public move controls have constant squared metric speed `normSq v`. -/
theorem control_move_speed (p : Pose) (v : ℂ) (t : ℝ) :
    metric ((Control.move v).trajectory p t).a
      (((Control.move v).trajectory p t).frame v)
      (((Control.move v).trajectory p t).frame v) = Complex.normSq v :=
  frame_metric _ v

theorem control_move_geodesic (p : Pose) (v : ℂ) (t : ℝ) :
    HasDerivAt (fun r => ((Control.move v).trajectory p r).frame v)
      (-christoffel ((Control.move v).trajectory p t).a
        (((Control.move v).trajectory p t).frame v)
        (((Control.move v).trajectory p t).frame v)) t := by
  simpa only [direction_velocity, Control.trajectory] using
    move_geodesic p (direction v) (direction_unit v) ‖v‖ t

theorem command_move_transport (p : Pose) (v : ℂ) (T : ℝ) (hT : 0 ≤ T) (w : ℂ) :
    ((Command.mk (.move v) T hT).path p).transport (p.frame w) =
      ((Control.move v).trajectory p T).frame w :=
  move_transport p (direction v) (direction_unit v) ‖v‖ T hT w
end Orbifold.DiskTransport
