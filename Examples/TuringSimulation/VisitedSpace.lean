import Applications.Resources.TuringSimulation.VisitedSpace
import Applications.Resources.TuringSimulation.TapeToPrimitive

set_option autoImplicit false
set_option warningAsError true

namespace Examples.TuringSimulation.VisitedSpace

open Function Turing
open Resources.TuringSimulation.VisitedSpace

inductive Phase
  | first
  | second
  | stopped
  deriving Inhabited, DecidableEq

abbrev Cell := Option Bool
abbrev Cfg := TM0.Cfg Cell Phase

def haltMachine : TM0.Machine Cell Phase := fun _ _ => none

def rightLeftMachine : TM0.Machine Cell Phase
  | .first, _ => some (.second, .move .right)
  | .second, _ => some (.stopped, .move .left)
  | .stopped, _ => none

def writeEraseMachine : TM0.Machine Cell Phase
  | .first, _ => some (.second, .write (some true))
  | .second, _ => some (.stopped, .write none)
  | .stopped, _ => none

def twoLeftMachine : TM0.Machine Cell Phase
  | .first, _ => some (.second, .move .left)
  | .second, _ => some (.stopped, .move .left)
  | .stopped, _ => none

def emptyStart : Cfg := TM0.init []
def falseStart : Cfg := TM0.init [some false]
def twoInputStart : Cfg := TM0.init [some false, some true]

theorem empty_input_head : emptyStart.Tape.head = none := rfl
theorem present_false_input_head : falseStart.Tape.head = some false := rfl

theorem halt_empty_visits_origin : visitedCells haltMachine emptyStart 0 2 = {0} := by decide

theorem halt_false_visits_origin : visitedCells haltMachine falseStart 0 2 = {0} := by decide

theorem halt_empty_outer_none : cfgAt haltMachine emptyStart 1 = none := rfl

theorem halt_false_outer_none : cfgAt haltMachine falseStart 1 = none := rfl

/-- The endpoint tape is blank again, but the genuine primitive trace has
visited the adjacent right cell. A final-support observer would lose it. -/
theorem rightLeftMachine_positions :
    (List.range 4).map (headPosition rightLeftMachine emptyStart 0) = [0, 1, 0, 0] := by decide

theorem rightLeftMachine_visits : visitedCells rightLeftMachine emptyStart 0 3 = {0, 1} := by decide

theorem rightLeftMachine_interval :
    visitedInterval rightLeftMachine emptyStart 0 0 3 = Finset.Icc 0 1 := by decide

theorem rightLeftMachine_live_halt :
    cfgAt rightLeftMachine emptyStart 2 = some ⟨.stopped, emptyStart.Tape⟩ := by
  change some (⟨.stopped, (emptyStart.Tape.move Dir.right).move Dir.left⟩ : Cfg) = _
  rw [Tape.move_right_left]

theorem rightLeftMachine_outer_none : cfgAt rightLeftMachine emptyStart 3 = none := rfl

theorem writeEraseMachine_positions :
    (List.range 4).map (headPosition writeEraseMachine emptyStart 0) = [0, 0, 0, 0] := by decide

theorem writeEraseMachine_visits : visitedCells writeEraseMachine emptyStart 0 3 = {0} := by decide

theorem writeEraseMachine_live_halt :
    cfgAt writeEraseMachine emptyStart 2 = some ⟨.stopped, emptyStart.Tape⟩ := rfl

theorem twoLeftMachine_positions :
    (List.range 3).map (headPosition twoLeftMachine twoInputStart 0) = [0, -1, -2] := by decide

theorem twoLeftMachine_visits :
    visitedCells twoLeftMachine twoInputStart 0 2 = {-2, -1, 0} := by decide

/-- Cell 1 is declared input but has never been visited; the union is named
explicitly so this stronger input-inclusive convention cannot be mistaken. -/
theorem twoLeftMachine_input_plus_visits :
    inputVisitedCells twoLeftMachine twoInputStart 0 2 2 = {-2, -1, 0, 1} := by decide

theorem twoLeftMachine_interval :
    visitedInterval twoLeftMachine twoInputStart 0 2 2 = Finset.Icc (-2) 1 := by decide

theorem twoLeftMachine_attains_bound :
    (visitedInterval twoLeftMachine twoInputStart 0 2 2).card = max 2 1 + 2 := by decide

theorem shifted_rightLeftMachine_positions :
    (List.range 4).map (headPosition rightLeftMachine emptyStart 7) = [7, 8, 7, 7] := by decide

theorem shifted_rightLeftMachine_visits :
    visitedCells rightLeftMachine emptyStart 7 3 = {7, 8} := by decide

/- Genuine native initialization of the actual two-stage empty-peek simulator.
These are not arbitrary continuation fragments. The main label is Unit.unit,
the actual Bool register default is false, and the native translated alphabet's
blank has marker false and every stack track none. -/

local instance : Inhabited (Unit → Option Bool) := Pi.instInhabited

abbrev PeekAlphabet := TM2to1.Γ' Unit (fun _ => Bool)
abbrev PeekTapeControl := TM2to1.Λ' Unit (fun _ => Bool) Unit Bool

def peekSource : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit Bool :=
  fun _ => .peek () (fun _ observed => observed.isNone) .halt

def peekTapeProgram : PeekTapeControl → TM1.Stmt PeekAlphabet PeekTapeControl Bool :=
  TM2to1.tr peekSource

abbrev PeekControl := TM1to0.Λ' peekTapeProgram
abbrev PeekCfg := TM0.Cfg PeekAlphabet PeekControl

-- The explicit instance has exactly the native translated default: the source
-- main Unit.unit in its normal tape control, and source register Bool.false.
-- It prevents a reducible product carrier from selecting an unrelated default.
local instance : Inhabited PeekControl :=
  ⟨(some (peekTapeProgram (.normal ())), false)⟩

def peekMachine : TM0.Machine PeekAlphabet PeekControl := TM1to0.tr peekTapeProgram

def peekInput : List PeekAlphabet := TM2to1.trInit () []
def peekTape : Tape PeekAlphabet := Tape.mk₁ peekInput
def peekStart : PeekCfg := TM0.init peekInput

def peekAction : TM2to1.StAct Unit (fun _ => Bool) Bool () :=
  .peek (fun _ observed => observed.isNone)

def peekGo : PeekCfg :=
  TM1to0.trCfg peekTapeProgram ⟨some (.go () peekAction .halt), false, peekTape⟩

def peekGotoRet : TM1.Stmt PeekAlphabet PeekTapeControl Bool :=
  .goto (fun _ _ => .ret .halt)

def peekAfterLeft : TM1.Stmt PeekAlphabet PeekTapeControl Bool :=
  .load (fun a _ => (a.2 ()).isNone) (.move .right peekGotoRet)

def peekLeft : PeekCfg := ⟨(some peekAfterLeft, false), peekTape.move .left⟩
def peekBack : PeekCfg := ⟨(some peekGotoRet, true), peekTape⟩

def peekRet : PeekCfg :=
  TM1to0.trCfg peekTapeProgram ⟨some (.ret .halt), true, peekTape⟩

def peekHalt : PeekCfg := ⟨(none, true), peekTape⟩

/-- This pins the actual native default, rather than relying on an arbitrary
ambient product default for a continuation-bearing control type. -/
theorem peekStart_actual_default :
    peekStart = ⟨(some (peekTapeProgram (.normal ())), false), peekTape⟩ := rfl

theorem peek_step0 : TM0.step peekMachine peekStart = some peekGo := by
  change some (⟨peekGo.q, peekTape.write peekTape.head⟩ : PeekCfg) = some peekGo
  rw [Tape.write_self]; rfl

theorem peek_step1 : TM0.step peekMachine peekGo = some peekLeft := rfl

theorem peek_step2 : TM0.step peekMachine peekLeft = some peekBack := by
  change some (⟨(some peekGotoRet, true), (peekTape.move Dir.left).move Dir.right⟩ : PeekCfg) = _
  rw [Tape.move_left_right]; rfl

theorem peek_step3 : TM0.step peekMachine peekBack = some peekRet := by
  change some (⟨peekRet.q, peekTape.write peekTape.head⟩ : PeekCfg) = some peekRet
  rw [Tape.write_self]; rfl

theorem peek_step4 : TM0.step peekMachine peekRet = some peekHalt := by
  change some (⟨(none, true), peekTape.write peekTape.head⟩ : PeekCfg) = some peekHalt
  rw [Tape.write_self]; rfl

theorem peek_step5 : TM0.step peekMachine peekHalt = none := rfl

theorem peek_actual_prefixes :
    cfgAt peekMachine peekStart 1 = some peekGo ∧
    cfgAt peekMachine peekStart 2 = some peekLeft ∧
    cfgAt peekMachine peekStart 3 = some peekBack ∧
    cfgAt peekMachine peekStart 4 = some peekRet ∧
    cfgAt peekMachine peekStart 5 = some peekHalt ∧
    cfgAt peekMachine peekStart 6 = none := by
  have h1 : cfgAt peekMachine peekStart 1 = some peekGo := by
    rw [cfgAt_succ, cfgAt_zero]; exact peek_step0
  have h2 : cfgAt peekMachine peekStart 2 = some peekLeft := by
    rw [cfgAt_succ, h1]; exact peek_step1
  have h3 : cfgAt peekMachine peekStart 3 = some peekBack := by
    rw [cfgAt_succ, h2]; exact peek_step2
  have h4 : cfgAt peekMachine peekStart 4 = some peekRet := by
    rw [cfgAt_succ, h3]; exact peek_step3
  have h5 : cfgAt peekMachine peekStart 5 = some peekHalt := by
    rw [cfgAt_succ, h4]; exact peek_step4
  have h6 : cfgAt peekMachine peekStart 6 = none := by
    rw [cfgAt_succ, h5]; exact peek_step5
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem peek_positions :
    (List.range 7).map (headPosition peekMachine peekStart 0) =
      [0, 0, -1, 0, 0, 0, 0] := by decide

theorem peek_before_excursion : visitedCells peekMachine peekStart 0 1 = {0} := by decide

theorem peek_excursion_is_visited : visitedCells peekMachine peekStart 0 2 = {-1, 0} := by decide

theorem peek_live_halt_retains_excursion :
    visitedCells peekMachine peekStart 0 5 = {-1, 0} := by decide

theorem peek_outer_none_adds_no_cell :
    visitedCells peekMachine peekStart 0 6 = {-1, 0} := by decide

theorem peek_final_interval :
    visitedInterval peekMachine peekStart 0 peekInput.length 6 = Finset.Icc (-1) 0 := by decide

theorem peek_initial_raw_empty : peekStart.Tape.head.2 () = none := rfl
theorem peek_initial_marker : peekStart.Tape.head.1 = true := rfl
theorem peek_halt_register : peekHalt.q.2 = true := rfl
theorem peek_halt_tape : peekHalt.Tape = peekStart.Tape := rfl

end Examples.TuringSimulation.VisitedSpace

namespace Examples.TuringSimulation.VisitedSpace.TraceConcatenation

open Turing
open Resources.TuringSimulation.VisitedSpace

-- Match the existing genuine initialized fixture's native alphabet and control
-- defaults. Local instance commands from its earlier namespace are not inherited.
local instance : Inhabited (Unit → Option Bool) := Pi.instInhabited
local instance : Inhabited PeekControl :=
  ⟨(some (peekTapeProgram (.normal ())), false)⟩

/-- Split the existing genuine initialized empty-peek run at its transient
left cell. Every suffix length retains its full cfg, command, and coordinate. -/
theorem peek_resume_trace (k : ℕ) :
    cfgAt peekMachine peekStart (2 + k) = cfgAt peekMachine peekLeft k ∧
      commandAt peekMachine peekStart (2 + k) = commandAt peekMachine peekLeft k ∧
      headPosition peekMachine peekStart 0 (2 + k) =
        headPosition peekMachine peekLeft (-1) k := by
  have hcfg : cfgAt peekMachine peekStart 2 = some peekLeft :=
    peek_actual_prefixes.2.1
  have hpos : headPosition peekMachine peekStart 0 2 = -1 := by decide
  exact ⟨cfgAt_add_of_live peekMachine peekStart peekLeft 2 hcfg k,
    commandAt_add_of_live peekMachine peekStart peekLeft 2 hcfg k,
    (headPosition_add_of_live peekMachine peekStart peekLeft 0 2 hcfg k).trans
      (congrArg (fun p : ℤ => headPosition peekMachine peekLeft p k) hpos)⟩

/-- The split preserves the actual right-move command and its updated true
register, not just a command with the same displacement. -/
theorem peek_split_selected_command :
    commandAt peekMachine peekStart 2 =
        some ((some peekGotoRet, true), TM0.Stmt.move Dir.right) ∧
      commandOffset (commandAt peekMachine peekStart 2) = 1 := by
  have hcmd : commandAt peekMachine peekStart 2 =
      some ((some peekGotoRet, true), TM0.Stmt.move Dir.right) := by
    calc
      commandAt peekMachine peekStart 2 = commandAt peekMachine peekLeft 0 :=
        (peek_resume_trace 0).2.1
      _ = (some ((some peekGotoRet, true), TM0.Stmt.move Dir.right) :
        Option (PeekControl × TM0.Stmt PeekAlphabet)) := rfl
  refine ⟨hcmd, ?_⟩
  rw [hcmd]
  rfl

private theorem peek_left_prefixes :
    cfgAt peekMachine peekLeft 1 = some peekBack ∧
      cfgAt peekMachine peekLeft 2 = some peekRet ∧
      cfgAt peekMachine peekLeft 3 = some peekHalt ∧
      cfgAt peekMachine peekLeft 4 = none := by
  have h1 : cfgAt peekMachine peekLeft 1 = some peekBack := by
    rw [cfgAt_succ, cfgAt_zero]
    exact peek_step2
  have h2 : cfgAt peekMachine peekLeft 2 = some peekRet := by
    rw [cfgAt_succ, h1]
    exact peek_step3
  have h3 : cfgAt peekMachine peekLeft 3 = some peekHalt := by
    rw [cfgAt_succ, h2]
    exact peek_step4
  have h4 : cfgAt peekMachine peekLeft 4 = none := by
    rw [cfgAt_succ, h3]
    exact peek_step5
  exact ⟨h1, h2, h3, h4⟩

/-- Composing the actual suffix recovers live-five and outer-none-six, with
the full live endpoint tape, updated register, and both observed coordinates. -/
theorem peek_split_completion :
    cfgAt peekMachine peekStart 5 = some peekHalt ∧
      cfgAt peekMachine peekStart 6 = none ∧
      headPosition peekMachine peekStart 0 5 = 0 ∧
      headPosition peekMachine peekStart 0 6 = 0 ∧
      commandAt peekMachine peekStart 6 = none ∧
      peekHalt.q.2 = true ∧ peekHalt.Tape = peekStart.Tape := by
  have hlocal := peek_left_prefixes
  have hpos3 : headPosition peekMachine peekLeft (-1) 3 = 0 := by decide
  have hpos4 : headPosition peekMachine peekLeft (-1) 4 = 0 := by decide
  exact ⟨((peek_resume_trace 3).1).trans hlocal.2.2.1,
    ((peek_resume_trace 4).1).trans hlocal.2.2.2,
    ((peek_resume_trace 3).2.2).trans hpos3,
    ((peek_resume_trace 4).2.2).trans hpos4,
    ((peek_resume_trace 4).2.1).trans
      (commandAt_of_none peekMachine peekLeft 4 hlocal.2.2.2),
    peek_halt_register, peek_halt_tape⟩

/-- The same supplied initial cfg can be observed in another global frame.
Origin seven gives split coordinate six, and the next move returns to seven. -/
theorem peek_resume_shifted :
    (∀ k : ℕ, headPosition peekMachine peekStart 7 (2 + k) =
      headPosition peekMachine peekLeft 6 k) ∧
      headPosition peekMachine peekStart 7 3 = 7 := by
  have hcfg : cfgAt peekMachine peekStart 2 = some peekLeft :=
    peek_actual_prefixes.2.1
  have hpos : headPosition peekMachine peekStart 7 2 = 6 := by decide
  have hcat (k : ℕ) : headPosition peekMachine peekStart 7 (2 + k) =
      headPosition peekMachine peekLeft 6 k :=
    (headPosition_add_of_live peekMachine peekStart peekLeft 7 2 hcfg k).trans
      (congrArg (fun p : ℤ => headPosition peekMachine peekLeft p k) hpos)
  have hreturn : headPosition peekMachine peekLeft 6 1 = 7 := by decide
  exact ⟨hcat, (hcat 1).trans hreturn⟩

end Examples.TuringSimulation.VisitedSpace.TraceConcatenation
