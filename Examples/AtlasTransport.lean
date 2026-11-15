import Applications.Orbifold.ChartedTransport
import Examples.PathTransport

/-! Witnessed local-frame calculations for the fixed hyperbolic connection. -/
noncomputable section
open Set
namespace Examples.AtlasTransport
open Orbifold Orbifold.DiskTransport Orbifold.FrameGauge

/-- The selected radius is strictly inside both open charts. -/
theorem radius_in_chart (z : ℂ) (hz : Complex.normSq z = 1 / 5) (i : Bool) :
    z ∈ chartDomain i := by
  have hr : z.re ^ 2 ≤ 1 / 5 := by
    rw [Complex.normSq_apply] at hz
    nlinarith [sq_nonneg z.im]
  cases i <;> dsimp [chartDomain] <;> nlinarith [sq_nonneg (z.re - 1 / 2), sq_nonneg (z.re + 1 / 2)]

def loopSegment := circle loopPoint loopPoint_radius (2 * Real.pi) (by positivity)

theorem loop_covered (i : Bool) (t : ℝ) : loopSegment.curve t ∈ chartDomain i := by
  apply radius_in_chart
  simp [loopSegment, circle, map_mul, loopPoint_radius]

def loopSingle : Charting loopSegment 0 loopSegment.duration :=
  .single ⟨le_rfl, loopSegment.nonneg⟩ ⟨loopSegment.nonneg, le_rfl⟩
    loopSegment.nonneg false (fun t _ => loop_covered false t)

def loopMixed : Charting loopSegment 0 loopSegment.duration :=
  .split Real.pi ⟨le_rfl, loopSegment.nonneg⟩ (by change Real.pi ∈ Icc 0 (2 * Real.pi); constructor <;> linarith [Real.pi_pos])
    ⟨loopSegment.nonneg, le_rfl⟩ (le_of_lt Real.pi_pos)
    (by change Real.pi ≤ 2 * Real.pi; linarith [Real.pi_pos]) false true
    (fun t _ => loop_covered false t) (fun t _ => loop_covered true t)

def loopPadded : Charting loopSegment 0 loopSegment.duration :=
  .cons ⟨le_rfl, loopSegment.nonneg⟩ ⟨le_rfl, loopSegment.nonneg⟩ le_rfl true
    (fun t _ => loop_covered true t) loopMixed

example : loopPadded.transport standard varying = loopMixed.transport standard varying :=
  loopPadded.independent loopMixed standard varying

/-- The independently calculated holonomy survives a genuine chart switch. -/
example (v : ℂ) : loopMixed.physical v = -v := by
  rw [loopMixed.full_agreement]
  exact loop_transport v

example : loopSingle.transport standard varying = loopMixed.transport standard varying :=
  loopSingle.independent loopMixed standard varying

def loopHold : Segment loopPoint loopPoint := .hold _ (2 * Real.pi) (by positivity)

def loopHoldChart : Charting loopHold 0 loopHold.duration :=
  .single ⟨le_rfl, loopHold.nonneg⟩ ⟨loopHold.nonneg, le_rfl⟩ loopHold.nonneg true
    (fun _ _ => radius_in_chart _ loopPoint_radius true)

/-- Equal source and final point do not determine the selected transport. -/
example : turnPoint loopPoint (2 * Real.pi) = loopPoint ∧
    loopMixed.physical 1 ≠ loopHoldChart.physical 1 := by
  refine ⟨loop_endpoint, ?_⟩
  rw [loopMixed.full_agreement, loopHoldChart.full_agreement]
  exact path_dependence.2

example (v : ℂ) : loopMixed.Parallel standard varying v
    (loopMixed.transport standard varying v) := loopMixed.parallel standard varying v

example (v w : ℂ) (h : loopMixed.Parallel standard varying v w) :
    w = loopSingle.transport standard varying v := by
  rw [loopMixed.unique standard varying v w h, loopMixed.independent loopSingle standard varying]


def originHold (T : ℝ) (hT : 0 ≤ T) : Segment Orbifolds.QuarterTurn.origin Orbifolds.QuarterTurn.origin :=
  .hold _ T hT

def holdChart (T : ℝ) (hT : 0 ≤ T) (i : Bool) :
    Charting (originHold T hT) 0 T :=
  .single ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT i (by
    intro t ht
    cases i <;> norm_num [originHold, Segment.hold, chartDomain, Orbifolds.QuarterTurn.origin])

example : (holdChart 1 (by norm_num) false).physical =
    (holdChart 3 (by norm_num) true).physical := by
  have h1 := Charting.full_agreement (s := originHold 1 (by norm_num)) (holdChart 1 (by norm_num) false)
  have h3 := Charting.full_agreement (s := originHold 3 (by norm_num)) (holdChart 3 (by norm_num) true)
  have he : (originHold 1 (by norm_num)).transport = (originHold 3 (by norm_num)).transport := by
    simp [originHold, Segment.hold_transport]
  exact h1.trans (he.trans h3.symm)

example : (originHold 1 (by norm_num)).duration ≠ (originHold 3 (by norm_num)).duration := by
  norm_num [originHold, Segment.hold]

/-- Stationary motion retains its independently selected closing arrow. -/
def apexAtlas : AtlasPath PathTransport.apexClosed.path :=
  .cons (holdChart 1 (by norm_num) true) (.nil _)

example : AtlasPath.closed PathTransport.apexClosed apexAtlas 1 = Complex.I := by
  rw [AtlasPath.closed_agreement]
  simp [PathTransport.apexClosed, Path.ClosedLift.endomorphism, Path.ClosedLift.label,
    Path.transport, Segment.hold_transport, Orbifolds.QuarterTurn.quarterTurn_scalar]

example : varying.connection 0 1 ≠ standard.connection 0 1 := unchanged_connection_rejected

/-- Differential maps compose in the order used by the executed local maps. -/
example {x y : Disk} (s : Segment x y) (f g h : Gauge)
    (F : ConnectionMap s f g) (G : ConnectionMap s g h) (v : ℂ) :
    G.value s.duration * F.value s.duration *
        localTransport f s 0 s.duration ⟨le_rfl, s.nonneg⟩ ⟨s.nonneg, le_rfl⟩ v =
      localTransport h s 0 s.duration ⟨le_rfl, s.nonneg⟩ ⟨s.nonneg, le_rfl⟩
        (G.value 0 * F.value 0 * v) :=
  (F.comp G).transport 0 s.duration ⟨le_rfl, s.nonneg⟩ ⟨s.nonneg, le_rfl⟩ s.nonneg v

example (v : ℂ) : standard.transition varying (loopSegment.curve loopSegment.duration) *
    localTransport standard loopSegment 0 loopSegment.duration
      ⟨le_rfl, loopSegment.nonneg⟩ ⟨loopSegment.nonneg, le_rfl⟩ v =
    localTransport varying loopSegment 0 loopSegment.duration
      ⟨le_rfl, loopSegment.nonneg⟩ ⟨loopSegment.nonneg, le_rfl⟩
      (standard.transition varying (loopSegment.curve 0) * v) :=
  ConnectionMap.overlap_transport 0 loopSegment.duration
    ⟨le_rfl, loopSegment.nonneg⟩ ⟨loopSegment.nonneg, le_rfl⟩ loopSegment.nonneg v

example (q : Pose) (hq : q.a = Orbifolds.QuarterTurn.origin.val) (v : ℂ) :
    (PathTransport.apexClosed.path.terminalPose q hq).frame v =
      apexAtlas.transport (q.frame v) := apexAtlas.terminal_frame q hq v

example : apexAtlas.clock = 1 := by
  simp [AtlasPath.clock, PathTransport.apexClosed, DiskTransport.Path.duration, Segment.hold]


end Examples.AtlasTransport
