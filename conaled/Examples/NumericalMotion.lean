import Applications.Orbifold.NumericalSymmetry

/-! Executable rational commands with instantiated coordinate error budgets.
The initial point is negative on the real diameter with its metric-unit frame. -/
namespace Examples.NumericalMotion
open Orbifold Orbifold.DiskTransport Orbifold.DiskTransport.Numerical

def initial : Packet := ⟨⟨(-1/4096,0),((1-(1/4096)^2)/2,0)⟩,0⟩
noncomputable def initialPose : Pose :=
  ⟨-1/4096, 1, by norm_num [Complex.normSq_apply], by norm_num⟩

theorem initial_exact : initial.state.decode = coordinates initialPose := by
  apply Prod.ext <;> apply Complex.ext <;>
    norm_num [initial, initialPose, State.decode, QComplex.decode, coordinates,
      Pose.frame, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im]

theorem initial_approx : Approx initial initialPose := by
  unfold Approx
  rw [initial_exact, sub_self, norm_zero]
  norm_num [initial]

def moveTick : Tick := ⟨.move (1,0),1/1024,by norm_num⟩
def halfTick : Tick := ⟨.move (1,0),1/2048,by norm_num⟩
def turnTick : Tick := ⟨.turn 1,1/1024,by norm_num⟩
def holdTick : Tick := ⟨.hold,1/1024,by norm_num⟩
def zeroTick : Tick := ⟨.move (1,0),0,by norm_num⟩
def word : List Tick := [moveTick,turnTick,moveTick]

set_option maxRecDepth 10000 in
theorem move_accepts : Admissible moveTick initial := by decide +kernel
set_option maxRecDepth 10000 in
theorem turn_accepts : Admissible turnTick initial := by decide +kernel
set_option maxRecDepth 10000 in
theorem hold_accepts : Admissible holdTick initial := by decide +kernel
set_option maxRecDepth 10000 in
theorem zero_accepts : Admissible zeroTick initial := by decide +kernel

theorem move_error : Approx (advance moveTick initial) (moveTick.decode.finish initialPose) :=
  advance_correct move_accepts initial_approx
theorem turn_error : Approx (advance turnTick initial) (turnTick.decode.finish initialPose) :=
  advance_correct turn_accepts initial_approx
theorem hold_error : Approx (advance holdTick initial) (holdTick.decode.finish initialPose) :=
  advance_correct hold_accepts initial_approx
theorem zero_error : Approx (advance zeroTick initial) initialPose := by
  simpa [zeroTick, Tick.decode, Command.finish] using advance_correct zero_accepts initial_approx

set_option maxRecDepth 10000 in
theorem word_accepts : (run word initial).isSome = true := by decide +kernel
set_option maxRecDepth 10000 in
theorem refined_accepts : (run [halfTick,halfTick] initial).isSome = true := by decide +kernel

def wordResult : Result := (run word initial).get word_accepts
def refinedResult : Result := (run [halfTick,halfTick] initial).get refined_accepts

theorem word_run : run word initial = some wordResult := (Option.some_get word_accepts).symm
theorem refined_run : run [halfTick,halfTick] initial = some refinedResult :=
  (Option.some_get refined_accepts).symm

theorem word_error : Approx wordResult.final (execute initialPose (word.map Tick.decode)) :=
  (run_correct word_run initial_approx).1

theorem word_budget : wordResult.final.error = 124247487/1099511627776 := by
  rw [run_error word_run]
  norm_num [word, moveTick, turnTick, initial, errorAfter, budget]

theorem word_clock : clock word = 3/1024 := by
  norm_num [word, clock, moveTick, turnTick]

theorem refined_error : Approx refinedResult.final
    (moveTick.control.decode.trajectory initialPose (1/1024)) := by
  have h := run_interval_correct halfTick 2 refined_run initial_approx
  norm_num [halfTick, moveTick] at h ⊢
  exact h

/-- Equal elapsed time and a nonconstant move; halving the step lowers the
certified accumulated bound, not just a measured residual. -/
theorem refinement : refinedResult.final.error < (advance moveTick initial).error := by
  rw [run_error refined_run]
  norm_num [errorAfter, budget, initial, halfTick, advance, moveTick]

theorem regular_representative :
    checkedStep moveTick initial.turn = (checkedStep moveTick initial).map Packet.turn :=
  checkedStep_turn _ _

theorem initial_regular : initialPose.a ≠ 0 := by norm_num [initialPose]

theorem representative_coordinates :
    initial.turn.state.position = (0,-1/4096) ∧
    initial.turn.state.frame = (0,(1-(1/4096)^2)/2) := by
  norm_num [initial, Packet.turn, State.turn, QComplex.turn]

theorem representative_accepts : Admissible moveTick initial.turn :=
  (admissible_turn _ _).mpr move_accepts

theorem representative_error : Approx initial.turn (Orbifolds.QuarterTurn.quarterTurn • initialPose) := by
  have h := (approx_equivariant Orbifolds.QuarterTurn.quarterTurn initial initialPose).mpr initial_approx
  have he : Orbifolds.QuarterTurn.quarterTurn • initial = initial.turn := by
    change Packet.mk (Orbifolds.QuarterTurn.quarterTurn • initial.state) initial.error = _
    rw [quarterTurn_state]
    rfl
  rwa [he] at h

theorem outside_rejected : checkedStep moveTick ⟨⟨(3/4,0),(1/2,0)⟩,0⟩ = none := by
  decide +kernel

theorem move_endpoint_positive : 0 < (moveTick.decode.finish initialPose).a.re := by
  have he := move_error
  have hpos := (norm_fst_le
    ((advance moveTick initial).state.decode-coordinates (moveTick.decode.finish initialPose))).trans he
  have hr := (le_abs_self
    ((advance moveTick initial).state.position.decode-(moveTick.decode.finish initialPose).a).re).trans
      (Complex.abs_re_le_norm _)
  have h : (advance moveTick initial).state.position.decode.re -
      (moveTick.decode.finish initialPose).a.re ≤ ((advance moveTick initial).error : ℝ) := by
    exact hr.trans hpos
  have hn : ((advance moveTick initial).error : ℝ) <
      (advance moveTick initial).state.position.decode.re := by
    norm_num [advance, step, field, initial, moveTick, budget, Input.velocity, Input.angular,
      QComplex.decode, QComplex.mul, QComplex.add, QComplex.scale]
  linarith

theorem move_real_axis (t : ℝ) : (moveTick.control.decode.trajectory initialPose t).a.im = 0 := by
  have hc : moveTick.control.decode = .move 1 := by
    change Control.move (QComplex.decode (1,0)) = Control.move 1
    congr 1
    apply Complex.ext <;> norm_num [QComplex.decode]
  rw [hc]
  simp [Control.trajectory, direction, move, diameterPose, initialPose, Pose.comp, gyroAdd,
    Complex.div_im, Complex.mul_im, Complex.mul_re]

/-- Negative start and positive certified endpoint force an actual apex crossing
of the exact trajectory; the imaginary coordinate stays zero throughout. -/
theorem apex_crossing : ∃ t ∈ Set.Icc (0 : ℝ) (1/1024),
    (moveTick.control.decode.trajectory initialPose t).a = 0 := by
  let f := fun t => (moveTick.control.decode.trajectory initialPose t).a.re
  have hc : ContinuousOn f (Set.Icc 0 (1/1024)) := by
    intro t _
    exact (Complex.continuous_re.continuousAt.comp
      (moveTick.control.decode.position_equation initialPose t).continuousAt).continuousWithinAt
  have h0 : f 0 ≤ 0 := by simp [f, initialPose]; norm_num
  have h1 : 0 ≤ f (1/1024) := by
    simpa [f, Tick.decode, Command.finish, moveTick] using le_of_lt move_endpoint_positive
  obtain ⟨t, ht, hz⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1/1024) hc ⟨h0,h1⟩
  refine ⟨t,ht,?_⟩
  apply Complex.ext
  · exact hz
  · exact move_real_axis t

/-- info: true -/
#guard_msgs in
#eval (run word initial).isSome
/-- info: some (160251 / 8589934592) -/
#guard_msgs in
#eval (run [halfTick,halfTick] initial).map (fun r => r.final.error)
/-- info: some true -/
#guard_msgs in
#eval (checkedStep holdTick initial).map (fun q => q.state == initial.state)
/-- info: some true -/
#guard_msgs in
#eval (checkedStep turnTick initial).map (fun q => q.state.frame != initial.state.frame)
/-- info: true -/
#guard_msgs in
#eval (checkedStep moveTick initial.turn).isSome

end Examples.NumericalMotion
