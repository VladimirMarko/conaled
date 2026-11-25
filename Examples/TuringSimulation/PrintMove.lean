import Applications.Resources.TuringSimulation.PolynomialDeciderPrintMove

set_option autoImplicit false
set_option warningAsError true

namespace Resources.TuringSimulation.PrintMove.Cases

open Function Turing

abbrev Cell := Option Bool

def bit : Bool ↪ Cell := ⟨some, by intro a b h; exact Option.some.inj h⟩

def stoppedMachine : TM0.Machine Cell Unit := fun _ _ => none

def stoppedCfg (answer : Bool) : TM0.Cfg Cell Unit := ⟨(), Tape.mk₁ [some answer]⟩

def zeroNativeRun (answer : Bool) :
    StateTransition.EvalsToInTime (TM0.step stoppedMachine) (stoppedCfg answer)
      (some (stoppedCfg answer)) 0 :=
  StateTransition.EvalsToInTime.refl _ _

def zeroNormalRun (answer : Bool) :
    StateTransition.EvalsTo (step (adapter stoppedMachine (some true)))
      (normalCfg (stoppedCfg answer)) (some (normalCfg (stoppedCfg answer))) :=
  StateTransition.EvalsTo.refl _ _

theorem zeroNormalRun_steps (answer : Bool) : (zeroNormalRun answer).steps = 0 := rfl

def zeroDecisionRun (answer : Bool) :
    StateTransition.EvalsTo (step (adapter stoppedMachine (some true)))
      (normalCfg (stoppedCfg answer)) (some (decidedCfg answer (stoppedCfg answer).Tape)) :=
  decisionRun stoppedMachine bit (stoppedCfg answer) answer rfl rfl

theorem zeroDecisionRun_steps (answer : Bool) : (zeroDecisionRun answer).steps = 1 := rfl

/-- The actual zero-step native witness exercises the generic paid theorem. -/
theorem zero_paid_bound (answer : Bool) :
    ∃ run : StateTransition.EvalsToInTime (step (adapter stoppedMachine (some true)))
        (normalCfg (stoppedCfg answer)) (some (decidedCfg answer (stoppedCfg answer).Tape))
        (2 * 0 + 1),
      run.steps = 1 := by
  obtain ⟨run, hcount, _hbound, _halt⟩ :=
    decide_of_native_run stoppedMachine bit (stoppedCfg answer) (stoppedCfg answer)
      answer 0 (zeroNativeRun answer) rfl rfl
  change run.steps = 1 at hcount
  exact ⟨run, hcount⟩

theorem zero_false_rejects :
    Trace.cfgAt (adapter stoppedMachine (some true)) (normalCfg (stoppedCfg false)) 1 =
      some ⟨.reject, (stoppedCfg false).Tape.move .right⟩ :=
  (zeroDecisionRun false).evals_in_steps

theorem zero_true_accepts :
    Trace.cfgAt (adapter stoppedMachine (some true)) (normalCfg (stoppedCfg true)) 1 =
      some ⟨.accept, (stoppedCfg true).Tape.move .right⟩ :=
  (zeroDecisionRun true).evals_in_steps

theorem zero_false_outer_none :
    Trace.cfgAt (adapter stoppedMachine (some true)) (normalCfg (stoppedCfg false)) 2 = none := by
  rw [Trace.cfgAt_succ, zero_false_rejects]
  rfl

theorem zero_true_outer_none :
    Trace.cfgAt (adapter stoppedMachine (some true)) (normalCfg (stoppedCfg true)) 2 = none := by
  rw [Trace.cfgAt_succ, zero_true_accepts]
  rfl

theorem zero_normal_visits_only_origin :
    Trace.visitedCells (adapter stoppedMachine (some true)) (normalCfg (stoppedCfg true)) 0 0 =
      {0} := by decide

theorem zero_decision_visits_right :
    Trace.visitedCells (adapter stoppedMachine (some true)) (normalCfg (stoppedCfg true)) 0 1 =
      {0, 1} := by decide

theorem zero_outer_none_adds_no_visit :
    Trace.visitedCells (adapter stoppedMachine (some true)) (normalCfg (stoppedCfg true)) 0 2 =
      {0, 1} := by decide

/-- Actual supplied start=true. The ambient Bool default remains false. -/
def constantMachine (answer : Bool) : @TM0.Machine Cell Bool ⟨true⟩
  | true, _ => some (false, .write (some answer))
  | false, _ => none

def constantStart (raw : List Bool) : TM0.Cfg Cell Bool := by
  let : Inhabited Bool := ⟨true⟩
  exact TM0.init (raw.map some)

def constantFinish (answer : Bool) (raw : List Bool) : TM0.Cfg Cell Bool :=
  ⟨false, (Tape.mk₁ (raw.map some)).write (some answer)⟩

def constantCombined (answer : Bool) : Machine Cell (Control Bool) := by
  let : Inhabited Bool := ⟨true⟩
  exact adapter (constantMachine answer) (some true)

theorem ambient_bool_default_is_false : (default : Bool) = false := rfl
theorem supplied_native_control_is_true (raw : List Bool) : (constantStart raw).q = true := rfl

theorem supplied_combined_control_is_normal_true (raw : List Bool) :
    (normalCfg (constantStart raw)).q = .normal true := rfl

theorem supplied_combined_literal_init (raw : List Bool) :
    normalCfg (constantStart raw) = init (.normal true) (raw.map some) := rfl

theorem empty_literal_head : (constantStart []).Tape.head = none := rfl
theorem present_false_literal_head : (constantStart [false]).Tape.head = some false := rfl

def constantNativeRun (answer : Bool) (raw : List Bool) :
    StateTransition.EvalsTo (@TM0.step Cell Bool ⟨true⟩ inferInstance (constantMachine answer))
      (constantStart raw) (some (constantFinish answer raw)) where
  steps := 1
  evals_in_steps := rfl

def constantNormalRun (answer : Bool) (raw : List Bool) :
    StateTransition.EvalsTo (step (constantCombined answer))
      (normalCfg (constantStart raw)) (some (normalCfg (constantFinish answer raw))) := by
  let : Inhabited Bool := ⟨true⟩
  exact writeRun (constantMachine answer) (some true) true false
    (Tape.mk₁ (raw.map some)) (some answer) rfl

theorem constantNormalRun_steps (answer : Bool) (raw : List Bool) :
    (constantNormalRun answer raw).steps = 2 := rfl

def constantDecisionRun (answer : Bool) (raw : List Bool) :
    StateTransition.EvalsTo (step (constantCombined answer))
      (normalCfg (constantStart raw)) (some (decidedCfg answer (constantFinish answer raw).Tape)) := by
  let : Inhabited Bool := ⟨true⟩
  exact StateTransition.EvalsTo.trans (step (constantCombined answer)) _
    (normalCfg (constantFinish answer raw)) _ (constantNormalRun answer raw)
    (decisionRun (constantMachine answer) bit (constantFinish answer raw) answer rfl rfl)

theorem constantDecisionRun_steps (answer : Bool) (raw : List Bool) :
    (constantDecisionRun answer raw).steps = 3 := rfl

def constantOuterNoneRun (answer : Bool) (raw : List Bool) :
    StateTransition.EvalsTo (step (constantCombined answer))
      (normalCfg (constantStart raw)) none := by
  let : Inhabited Bool := ⟨true⟩
  exact StateTransition.EvalsTo.trans (step (constantCombined answer)) _
    (decidedCfg answer (constantFinish answer raw).Tape) _ (constantDecisionRun answer raw)
    (terminalOuterNone (constantMachine answer) (some true) answer (constantFinish answer raw).Tape)

theorem constantOuterNoneRun_steps (answer : Bool) (raw : List Bool) :
    (constantOuterNoneRun answer raw).steps = 4 := rfl

/-- Both answers on both independently fixed literal inputs. -/
theorem one_write_four_normal_counts :
    (constantNormalRun false []).steps = 2 ∧
    (constantNormalRun true []).steps = 2 ∧
    (constantNormalRun false [false]).steps = 2 ∧
    (constantNormalRun true [false]).steps = 2 := by decide

theorem one_write_four_decision_counts :
    (constantDecisionRun false []).steps = 3 ∧
    (constantDecisionRun true []).steps = 3 ∧
    (constantDecisionRun false [false]).steps = 3 ∧
    (constantDecisionRun true [false]).steps = 3 := by decide

theorem one_write_false_empty_endpoint :
    Trace.cfgAt (constantCombined false) (normalCfg (constantStart [])) 3 =
      some ⟨.reject, (Tape.mk₁ [some false]).move .right⟩ := by
  exact (constantDecisionRun false []).evals_in_steps

theorem one_write_true_empty_endpoint :
    Trace.cfgAt (constantCombined true) (normalCfg (constantStart [])) 3 =
      some ⟨.accept, (Tape.mk₁ [some true]).move .right⟩ := by
  exact (constantDecisionRun true []).evals_in_steps

theorem one_write_false_present_false_endpoint :
    Trace.cfgAt (constantCombined false) (normalCfg (constantStart [false])) 3 =
      some ⟨.reject, (Tape.mk₁ [some false]).move .right⟩ := by
  exact (constantDecisionRun false [false]).evals_in_steps

theorem one_write_true_present_false_endpoint :
    Trace.cfgAt (constantCombined true) (normalCfg (constantStart [false])) 3 =
      some ⟨.accept, (Tape.mk₁ [some true]).move .right⟩ := by
  exact (constantDecisionRun true [false]).evals_in_steps

theorem one_write_positions :
    (List.range 4).map (Trace.headPosition (constantCombined true)
      (normalCfg (constantStart [])) 0) = [0, 1, 0, 1] := by decide

theorem one_write_retains_right_visit_at_boundary :
    Trace.visitedCells (constantCombined true) (normalCfg (constantStart [])) 0 2 = {0, 1} := by
  decide

theorem one_write_outer_none_keeps_visits :
    Trace.visitedCells (constantCombined true) (normalCfg (constantStart [])) 0 4 = {0, 1} := by
  decide

inductive Phase
  | first
  | second
  | stopped
  deriving Inhabited, DecidableEq

instance : Fintype Phase where
  elems := {.first, .second, .stopped}
  complete := by
    intro phase
    cases phase <;> simp

def rightLeftMachine : TM0.Machine Cell Phase
  | .first, _ => some (.second, .move .right)
  | .second, _ => some (.stopped, .move .left)
  | .stopped, _ => none

def rightLeftTape : Tape Cell := Tape.mk₁ [some false]
def rightLeftStart : TM0.Cfg Cell Phase := ⟨.first, rightLeftTape⟩
def rightLeftFinish : TM0.Cfg Cell Phase := ⟨.stopped, rightLeftTape⟩

def rightLeftNativeRun :
    StateTransition.EvalsTo (TM0.step rightLeftMachine) rightLeftStart (some rightLeftFinish) where
  steps := 2
  evals_in_steps := by
    change some (⟨.stopped, (rightLeftTape.move .right).move .left⟩ : TM0.Cfg Cell Phase) =
      some ⟨.stopped, rightLeftTape⟩
    rw [Tape.move_right_left]

def rightLeftNormalRun :
    StateTransition.EvalsTo (step (adapter rightLeftMachine (some true)))
      (normalCfg rightLeftStart) (some (normalCfg rightLeftFinish)) where
  steps := 2
  evals_in_steps := by
    change Option.bind
      (step (adapter rightLeftMachine (some true)) (normalCfg ⟨.first, rightLeftTape⟩))
      (step (adapter rightLeftMachine (some true))) =
        some (normalCfg ⟨.stopped, rightLeftTape⟩)
    rw [move_step rightLeftMachine (some true) .first .second rightLeftTape .right rfl]
    change step (adapter rightLeftMachine (some true))
      (normalCfg ⟨.second, rightLeftTape.move .right⟩) =
        some (normalCfg ⟨.stopped, rightLeftTape⟩)
    rw [move_step rightLeftMachine (some true) .second .stopped
      (rightLeftTape.move .right) .left rfl, Tape.move_right_left]

def rightLeftDecisionRun :
    StateTransition.EvalsTo (step (adapter rightLeftMachine (some true)))
      (normalCfg rightLeftStart) (some (decidedCfg false rightLeftTape)) :=
  StateTransition.EvalsTo.trans (step (adapter rightLeftMachine (some true))) _
    (normalCfg rightLeftFinish) _ rightLeftNormalRun
    (decisionRun rightLeftMachine bit rightLeftFinish false rfl rfl)

theorem rightLeft_counts : rightLeftNormalRun.steps = 2 ∧ rightLeftDecisionRun.steps = 3 := by decide

theorem rightLeft_positions :
    (List.range 4).map (Trace.headPosition (adapter rightLeftMachine (some true))
      (normalCfg rightLeftStart) 0) = [0, 1, 0, 1] := by decide

theorem rightLeft_visits :
    Trace.visitedCells (adapter rightLeftMachine (some true)) (normalCfg rightLeftStart) 0 3 =
      {0, 1} := by decide

def writeEraseMachine : TM0.Machine Cell Phase
  | .first, _ => some (.second, .write (some true))
  | .second, _ => some (.stopped, .write none)
  | .stopped, _ => none

def blankTape : Tape Cell := Tape.mk₁ []
def writeEraseStart : TM0.Cfg Cell Phase := ⟨.first, blankTape⟩
def writeEraseFinish : TM0.Cfg Cell Phase := ⟨.stopped, blankTape⟩

def writeEraseNormalRun :
    StateTransition.EvalsTo (step (adapter writeEraseMachine (some true)))
      (normalCfg writeEraseStart) (some (normalCfg writeEraseFinish)) where
  steps := 4
  evals_in_steps := by
    let first := writeRun writeEraseMachine (some true) .first .second blankTape (some true) rfl
    let second := writeRun writeEraseMachine (some true) .second .stopped
      (blankTape.write (some true)) none rfl
    exact (StateTransition.EvalsTo.trans (step (adapter writeEraseMachine (some true)))
      _ _ _ first second).evals_in_steps

theorem writeErase_count : writeEraseNormalRun.steps = 4 := rfl

theorem writeErase_positions :
    (List.range 5).map (Trace.headPosition (adapter writeEraseMachine (some true))
      (normalCfg writeEraseStart) 0) = [0, 1, 0, 1, 0] := by decide

theorem writeErase_visits :
    Trace.visitedCells (adapter writeEraseMachine (some true)) (normalCfg writeEraseStart) 0 4 =
      {0, 1} := by decide

theorem writeErase_interval :
    Trace.visitedInterval (adapter writeEraseMachine (some true))
      (normalCfg writeEraseStart) 0 0 4 = Finset.Icc 0 1 := by decide

/-- This remains a simulation case, not a Boolean decider output assertion. -/
theorem writeErase_head_is_blank : writeEraseFinish.Tape.head = none := rfl

theorem finite_bool_control_count : Fintype.card (Control Bool) = 6 := by
  simpa using (card_control (Q := Bool))

end Resources.TuringSimulation.PrintMove.Cases
