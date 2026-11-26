import Applications.Resources.TuringSimulation.TapeToPrimitive
import Applications.Resources.TuringSimulation.TapeReflection

set_option autoImplicit false
set_option warningAsError true

namespace Examples.TuringSimulation.Primitive

open Resources.TuringSimulation.TapeToPrimitive

open Function Turing

def gotoProgram : Unit → TM1.Stmt Bool Unit Bool := fun _ => .halt

def gotoBody : TM1.Stmt Bool Unit Bool := .goto (fun _ _ => ())

/-- A goto emits one genuine dummy write, retaining the entire tape. -/
def gotoRun (v : Bool) (T : Tape Bool) :
    StateTransition.EvalsTo (TM0.step (TM1to0.tr gotoProgram))
      ⟨(some gotoBody, v), T⟩ (some ⟨(some TM1.Stmt.halt, v), T⟩) where
  steps := 1
  evals_in_steps := by
    simpa only [gotoBody, gotoProgram, primitiveSteps, TM1.stepAux,
      TM1to0.trCfg, Option.map] using statement_exact gotoProgram gotoBody v T

theorem gotoRun_steps (v : Bool) (T : Tape Bool) : (gotoRun v T).steps = 1 := rfl

local instance : Inhabited (Unit → Option Bool) := Pi.instInhabited

abbrev StackAlphabet := TM2to1.Γ' Unit (fun _ => Bool)
abbrev StackControl := TM2to1.Λ' Unit (fun _ => Bool) Unit Bool

def stackProgram : Unit → TM2.Stmt (fun _ : Unit => Bool) Unit Bool := fun _ => .halt

def tapeProgram : StackControl → TM1.Stmt StackAlphabet StackControl Bool :=
  TM2to1.tr stackProgram

abbrev PrimitiveCfg := TM0.Cfg StackAlphabet (TM1to0.Λ' tapeProgram)

def primitiveStep : PrimitiveCfg → Option PrimitiveCfg :=
  TM0.step (TM1to0.tr tapeProgram)

def emptyColumns : ListBlank (Unit → Option Bool) := ListBlank.mk []

def emptyTape : Tape StackAlphabet := Tape.mk' ∅ (TM2to1.addBottom emptyColumns)

def singletonColumns : ListBlank (Unit → Option Bool) :=
  ListBlank.mk [fun _ => some false]

def singletonTape : Tape StackAlphabet := Tape.mk' ∅ (TM2to1.addBottom singletonColumns)

def pushTrue : TM2to1.StAct Unit (fun _ => Bool) Bool () := .push (fun _ => true)

def popIsNone : TM2to1.StAct Unit (fun _ => Bool) Bool () := .pop (fun _ a => a.isNone)

def peekIsNone : TM2to1.StAct Unit (fun _ => Bool) Bool () := .peek (fun _ a => a.isNone)

def goCfg (o : TM2to1.StAct Unit (fun _ => Bool) Bool ()) (v : Bool)
    (T : Tape StackAlphabet) : PrimitiveCfg :=
  TM1to0.trCfg tapeProgram ⟨some (TM2to1.Λ'.go () o .halt), v, T⟩

def retCfg (v : Bool) (T : Tape StackAlphabet) : PrimitiveCfg :=
  TM1to0.trCfg tapeProgram ⟨some (TM2to1.Λ'.ret .halt), v, T⟩

/-- One actual outward TM1 boundary requires a move and then a dummy write. -/
def outwardRun : StateTransition.EvalsTo primitiveStep
    (goCfg pushTrue false singletonTape)
    (some (goCfg pushTrue false (singletonTape.move Dir.right))) where
  steps := 2
  evals_in_steps := by
    have h := statement_exact tapeProgram
      (tapeProgram (TM2to1.Λ'.go () pushTrue .halt)) false singletonTape
    change (flip bind primitiveStep)^[2] (some (goCfg pushTrue false singletonTape)) =
      some (goCfg pushTrue false (singletonTape.move Dir.right)) at h
    exact h

theorem outwardRun_steps : outwardRun.steps = 2 := rfl

theorem unit_update_constant (a : Option Bool) :
    Function.update (fun _ : Unit => (none : Option Bool)) () a = fun _ => a := by
  funext k
  cases k
  exact Function.update_self () a (fun _ : Unit => (none : Option Bool))

/-- Full independently specified tape: the bottom cell now contains true,
and the head is one position to its right. -/
def emptyPushedTape : Tape StackAlphabet :=
  (emptyTape.write (true, fun _ => some true)).move Dir.right

def emptyPushRun : StateTransition.EvalsTo primitiveStep
    (goCfg pushTrue false emptyTape) (some (retCfg false emptyPushedTape)) where
  steps := 3
  evals_in_steps := by
    have h := statement_exact tapeProgram
      (tapeProgram (TM2to1.Λ'.go () pushTrue .halt)) false emptyTape
    change (flip bind primitiveStep)^[3] (some (goCfg pushTrue false emptyTape)) =
      some (retCfg false
        ((emptyTape.write
          (true, Function.update (fun _ : Unit => (none : Option Bool)) () (some true))).move
            Dir.right)) at h
    simpa only [unit_update_constant, emptyPushedTape] using h

theorem emptyPushRun_steps : emptyPushRun.steps = 3 := rfl

theorem emptyPushedTape_retains_symbol : emptyPushedTape.left.head.2 () = some true := rfl

/-- Empty pop takes the marker branch, folds its register load, and emits
only the final dummy write. The updated register and full tape are explicit. -/
def emptyPopRun : StateTransition.EvalsTo primitiveStep
    (goCfg popIsNone false emptyTape) (some (retCfg true emptyTape)) where
  steps := 1
  evals_in_steps := by
    have h := statement_exact tapeProgram
      (tapeProgram (TM2to1.Λ'.go () popIsNone .halt)) false emptyTape
    change (flip bind primitiveStep)^[1] (some (goCfg popIsNone false emptyTape)) =
      some (retCfg true emptyTape) at h
    exact h

theorem emptyPopRun_steps : emptyPopRun.steps = 1 := rfl

def gotoRet : TM1.Stmt StackAlphabet StackControl Bool :=
  .goto (fun _ _ => TM2to1.Λ'.ret .halt)

def peekAfterLeft : TM1.Stmt StackAlphabet StackControl Bool :=
  .load (fun a _ => (a.2 ()).isNone) (.move Dir.right gotoRet)

/-- The primitive trace exposes the left excursion hidden by TM1.stepAux. -/
theorem empty_peek_first_moves_left :
    primitiveStep (goCfg peekIsNone false emptyTape) =
      some ⟨(some peekAfterLeft, false), emptyTape.move Dir.left⟩ := rfl

theorem emptyTape_move_left_head_eq_false : (emptyTape.move Dir.left).head.1 = false := rfl

/-- The second primitive folds the load and returns to the bottom; the goto
still remains in the actual primitive control state. -/
theorem empty_peek_second_returns :
    primitiveStep ⟨(some peekAfterLeft, false), emptyTape.move Dir.left⟩ =
      some ⟨(some gotoRet, true), emptyTape⟩ := by
  change some (⟨(some gotoRet, true), (emptyTape.move Dir.left).move Dir.right⟩ :
      PrimitiveCfg) = _
  rw [Tape.move_left_right]

theorem empty_peek_third_selects_ret :
    primitiveStep ⟨(some gotoRet, true), emptyTape⟩ = some (retCfg true emptyTape) := by
  change some (⟨(some (tapeProgram (TM2to1.Λ'.ret .halt)), true),
    emptyTape.write emptyTape.head⟩ : PrimitiveCfg) = _
  rw [Tape.write_self]
  rfl

def emptyPeekRun : StateTransition.EvalsTo primitiveStep
    (goCfg peekIsNone false emptyTape) (some (retCfg true emptyTape)) where
  steps := 3
  evals_in_steps := by
    have h := statement_exact tapeProgram
      (tapeProgram (TM2to1.Λ'.go () peekIsNone .halt)) false emptyTape
    change (flip bind primitiveStep)^[3] (some (goCfg peekIsNone false emptyTape)) =
      some (retCfg true ((emptyTape.move Dir.left).move Dir.right)) at h
    simpa only [Tape.move_left_right] using h

theorem emptyPeekRun_steps : emptyPeekRun.steps = 3 := rfl

def twoProgram : Bool → TM1.Stmt Bool Bool Bool
  | false => .goto (fun _ _ => true)
  | true => .halt

def twoInitial (T : Tape Bool) : TM1.Cfg Bool Bool Bool := ⟨some false, true, T⟩

def twoLiveHalt (T : Tape Bool) : TM1.Cfg Bool Bool Bool := ⟨none, true, T⟩

theorem two_native_steps (T : Tape Bool) :
    (flip bind (TM1.step twoProgram))^[2] (some (twoInitial T)) =
      some (twoLiveHalt T) := rfl

/-- This connected example consumes the whole-run theorem; its premise is
the actual two-step source execution, with a syntax bound of one per label. -/
theorem two_primitive_bound (T : Tape Bool) :
    Nonempty (StateTransition.EvalsToInTime (TM0.step (TM1to0.tr twoProgram))
      (TM1to0.trCfg twoProgram (twoInitial T))
      (some (TM1to0.trCfg twoProgram (twoLiveHalt T))) 2) := by
  have bounded : ∀ l, primitiveBound (twoProgram l) ≤ 1 := by
    intro l
    cases l <;> exact le_rfl
  simpa only [Nat.mul_one] using
    finite_run_bounded twoProgram 1 bounded (twoInitial T) (twoLiveHalt T) 2
      (two_native_steps T)

/-- Independent exact observation alongside the upper-bound consumer. -/
def twoPrimitiveRun (T : Tape Bool) :
    StateTransition.EvalsTo (TM0.step (TM1to0.tr twoProgram))
      (TM1to0.trCfg twoProgram (twoInitial T))
      (some (TM1to0.trCfg twoProgram (twoLiveHalt T))) where
  steps := 2
  evals_in_steps := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply,
      Function.flip_def, bind, Option.bind_some, TM1to0.trCfg, Option.map,
      twoInitial, twoLiveHalt, twoProgram, TM0.step, TM1to0.tr, TM1to0.trAux,
      Tape.write_self]

def threePrimitiveOuterNone (T : Tape Bool) :
    StateTransition.EvalsTo (TM0.step (TM1to0.tr twoProgram))
      (TM1to0.trCfg twoProgram (twoInitial T)) none :=
  StateTransition.EvalsTo.trans (TM0.step (TM1to0.tr twoProgram)) _ _ _
    (twoPrimitiveRun T)
    { steps := 1
      evals_in_steps := by
        simp only [Function.iterate_one, Function.flip_def, bind, Option.bind_some]
        exact halted_step twoProgram true T }

theorem twoPrimitiveRun_steps (T : Tape Bool) : (twoPrimitiveRun T).steps = 2 := rfl

theorem threePrimitiveOuterNone_steps (T : Tape Bool) :
    (threePrimitiveOuterNone T).steps = 3 := rfl

end Examples.TuringSimulation.Primitive

namespace Examples.TuringSimulation.PrimitiveReflection

open Function Turing
open Examples.TuringSimulation.Primitive
open Resources.TuringSimulation

def reflectedStep : PrimitiveCfg → Option PrimitiveCfg :=
  TM0.step (TapeReflection.machine (TM1to0.tr tapeProgram))

theorem empty_peek_first_moves_right :
    reflectedStep (TapeReflection.configuration (goCfg peekIsNone false emptyTape)) =
      some ⟨(some peekAfterLeft, false), emptyTape.move Dir.right⟩ := by
  rw [reflectedStep, TapeReflection.step]
  change (primitiveStep (goCfg peekIsNone false emptyTape)).map
    TapeReflection.configuration = _
  rw [empty_peek_first_moves_left]
  rfl

theorem emptyTape_move_right_head_eq_false : (emptyTape.move Dir.right).head.1 = false := rfl

theorem empty_peek_second_returns_left :
    reflectedStep ⟨(some peekAfterLeft, false), emptyTape.move Dir.right⟩ =
      some ⟨(some gotoRet, true), emptyTape⟩ := by
  change reflectedStep (TapeReflection.configuration
    (⟨(some peekAfterLeft, false), emptyTape.move Dir.left⟩ : PrimitiveCfg)) = _
  rw [reflectedStep, TapeReflection.step]
  change (primitiveStep ⟨(some peekAfterLeft, false), emptyTape.move Dir.left⟩).map
    TapeReflection.configuration = _
  rw [empty_peek_second_returns]
  rfl

theorem empty_peek_third_still_selects_ret :
    reflectedStep ⟨(some gotoRet, true), emptyTape⟩ =
      some (retCfg true emptyTape) := by
  change reflectedStep (TapeReflection.configuration
    (⟨(some gotoRet, true), emptyTape⟩ : PrimitiveCfg)) = _
  rw [reflectedStep, TapeReflection.step]
  change (primitiveStep ⟨(some gotoRet, true), emptyTape⟩).map
    TapeReflection.configuration = _
  rw [empty_peek_third_selects_ret]
  rfl

/-- The actual existing native witness is transported, retaining its entire
endpoint tape and updated true register with identical count. -/
def emptyPeekRun : StateTransition.EvalsTo reflectedStep
    (TapeReflection.configuration (goCfg peekIsNone false emptyTape))
    (some (TapeReflection.configuration (retCfg true emptyTape))) where
  steps := Primitive.emptyPeekRun.steps
  evals_in_steps := by
    have transported := TapeReflection.iterate_option (TM1to0.tr tapeProgram)
      Primitive.emptyPeekRun.steps (some (goCfg peekIsNone false emptyTape))
    have original := Primitive.emptyPeekRun.evals_in_steps
    change (flip bind (TM0.step (TM1to0.tr tapeProgram)))^[Primitive.emptyPeekRun.steps]
      (some (goCfg peekIsNone false emptyTape)) = some (retCfg true emptyTape) at original
    rw [original] at transported
    exact transported.symm

theorem emptyPeekRun_steps : emptyPeekRun.steps = 3 := rfl

end Examples.TuringSimulation.PrimitiveReflection
