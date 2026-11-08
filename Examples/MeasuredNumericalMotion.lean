import Applications.Orbifold.MeasuredNumericalExecution
import Examples.NumericalMotion

/-! Checked motion preserves successful contracts and work spent before whole-run rejection. -/
namespace Examples.MeasuredNumericalMotion
open Orbifold Orbifold.DiskTransport Orbifold.DiskTransport.Numerical Resources
open Examples.NumericalMotion

def badTick : Tick := ⟨.move (2,0),0,by norm_num⟩

theorem bad_rejects (q : Packet) : checkedStep badTick q = none := by
  simp [checkedStep, Admissible, badTick, Input.velocity, QComplex.normSq]

theorem empty : Measured.run [] initial = (some ⟨initial,[],0⟩,0) := rfl

theorem word_value : (Measured.run word initial).1 = some wordResult :=
  (Measured.run_erases _ _).trans word_run

theorem word_measured : Measured.run word initial = (some wordResult,(3,(3,0))) :=
  Prod.ext word_value (Measured.run_success_counts word_value)

theorem move_value : (Measured.run [moveTick] initial).1 =
    some ⟨advance moveTick initial,[advance moveTick initial],moveTick.duration⟩ := by
  simp [Measured.run, checkedStep, move_accepts, Measured.prepend]

/-- The suffix is arbitrary and does not contribute any attempts after failure. -/
theorem rejected_after_progress (suffix : List Tick) :
    Measured.run (moveTick::badTick::suffix) initial = (none,(2,(1,1))) :=
  Measured.run_first_failure [moveTick] suffix initial _ badTick move_value (bad_rejects _)

theorem immediate_rejection (suffix : List Tick) :
    Measured.run (badTick::suffix) initial = (none,(1,(0,1))) := by
  simp [Measured.run, bad_rejects, rejectedAttempt]

example : (Measured.run [badTick] initial).1 = (Measured.run [moveTick,badTick] initial).1 ∧
    (Measured.run [badTick] initial).2 ≠ (Measured.run [moveTick,badTick] initial).2 := by
  rw [immediate_rejection, rejected_after_progress]
  decide

example : Measured.run ([moveTick]++[turnTick,moveTick]) initial =
    Resources.bind (Measured.run [moveTick] initial) (Measured.continueWith [turnTick,moveTick]) :=
  Measured.run_append _ _ _

example : reweight branchTariff (Measured.run ([moveTick]++[badTick,turnTick]) initial) =
    Resources.bind (reweight branchTariff (Measured.run [moveTick] initial))
      (fun a => reweight branchTariff (Measured.continueWith [badTick,turnTick] a)) :=
  Measured.reweight_append _ _ _ _

example : reweight attemptTariff (Measured.run [moveTick,badTick,turnTick] initial) = (none,2) := by
  rw [rejected_after_progress]
  rfl
example : reweight branchTariff (Measured.run [moveTick,badTick,turnTick] initial) = (none,8) := by
  rw [rejected_after_progress]
  rfl

example : Approx wordResult.final (execute initialPose (word.map Tick.decode)) ∧
    List.Forall₂ Approx wordResult.samples (endpoints initialPose word) ∧
    List.Forall (fun s => Domain s.state.decode) wordResult.samples :=
  Measured.run_correct word_value initial_approx

example : wordResult.final.error = errorAfter word initial.error := Measured.run_error word_value
example : wordResult.elapsed = clock word := Measured.run_clock word_value
example : (Measured.run [moveTick,badTick,turnTick] initial).2.1 ≤ 3 :=
  (Measured.run_counts _ _).2.2

end Examples.MeasuredNumericalMotion
