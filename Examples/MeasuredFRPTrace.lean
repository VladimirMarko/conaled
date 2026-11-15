import Applications.FRP.MeasuredTrace
import Examples.FRPTrace

/-! Branch accounting for continued source-window processing. -/
namespace Examples.MeasuredFRPTrace
open FRPSpec.Frontier FRPSpec.Frontier.Trace Resources

def initialState : State ℚ Nat := initial 2
def accepted : Message ℚ Nat := FRPTrace.packets .left 0
def rejected : Message ℚ Nat := FRPTrace.packets .left 1
def later : Message ℚ Nat := ⟨4,[]⟩
def messages := [accepted,rejected,later]
def expected : State ℚ Nat := ⟨4,[(2,[3,4]),(2,[3])]⟩

theorem empty : Measured.run [] initialState = (initialState,0) := rfl

theorem continued : Measured.run messages initialState = (expected,(3,(2,1))) := by decide

example : (Measured.run messages initialState).1 = messages.foldl process initialState :=
  Measured.run_erases _ _

example : Measured.run ([accepted]++[rejected,later]) initialState =
    Resources.bind (Measured.run [accepted] initialState) (Measured.run [rejected,later]) :=
  Measured.run_append _ _ _

example : (Measured.run messages initialState).2.1 = messages.length :=
  (Measured.run_counts _ _).1

example : (Measured.run messages initialState).1.Valid :=
  Measured.run_valid _ _ (by simp [initialState, initial, State.Valid])

example : Refines initialState (Measured.run messages initialState).1 :=
  Measured.run_refines _ _

/-- Rejection cannot be detected from the resulting state alone. -/
theorem same_value_different_work :
    (Measured.run [accepted] initialState).1 = (Measured.run [accepted,rejected] initialState).1 ∧
    (Measured.run [accepted] initialState).2 ≠ (Measured.run [accepted,rejected] initialState).2 := by decide

/-- An accepted empty window can also stutter; it must retain its acceptance label. -/
example : Measured.step (⟨2,[]⟩ : Message ℚ Nat) initialState = (initialState,acceptedAttempt) := by decide

example : reweight attemptTariff (Measured.run messages initialState) = (expected,3) := by decide
example : reweight branchTariff (Measured.run messages initialState) = (expected,11) := by decide

example : reweight branchTariff (Measured.run messages initialState) =
    Resources.run (fun m s => reweight branchTariff (Measured.step m s)) messages initialState :=
  Measured.reweight_run _ _ _

example : (reweight branchTariff (Measured.run messages initialState)).2 ≤ branchTariff (3,(3,3)) :=
  reweight_bound branchTariff branchTariff_mono _ _ (by rw [continued]; decide)

example (n : Nat) :
    (Measured.run ((List.range n).map (FRPTrace.packets .left)) initialState).1 =
      sourcePrefix initialState (FRPTrace.packets .left) n := Measured.run_prefix _ _ _

end Examples.MeasuredFRPTrace
