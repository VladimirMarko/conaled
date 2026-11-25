import Applications.Resources.TuringSimulation.OrdinaryPackage
import Applications.Resources.TuringSimulation.PolynomialDeciderPrintMove
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod

import Applications.Resources.TuringSimulation.TapeReflection
import Applications.Resources.TuringSimulation.MarkedInput
import Applications.Resources.TuringSimulation.PolynomialDecider
import Applications.Resources.TuringSimulation.VisitedSpace

import Applications.Resources.TuringSimulation.StackToTape
import Applications.Resources.TuringSimulation.TapeToPrimitive
import Applications.Resources.TuringSimulation.FiniteControl

/-!
# Connected native stack-to-tape timing examples

Fixed calculations distinguish the selected track from a longer unrelated
track, preserve empty-pop/peek register effects, count internal push/pop work,
separate live halt from outer none, follow a register-changing branch, and
compose two actual source steps. The final two-step example has exact target
time eight and a separately derived upper bound fourteen.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.TuringSimulation

open Function
open Turing Turing.TM2to1
open Resources.TuringSimulation.StackToTape

namespace Cases

local instance : Inhabited (Bool → Option Bool) := Pi.instInhabited

/- Independent expectations, fixed before these connections:
   * selected stack false = [true, false], other stack true has length four;
   * outward travel takes two transitions even though the other track is longer;
   * pushing false gives selected [false, true, false], preserves the other
     stack and registers, and takes 2 + 3 + 1 = 6 shuttle transitions;
   * empty peek/pop each take one shuttle transition and update registers by
     the supplied function. Empty peek still has an internal left excursion,
     which this boundary-transition contract does not observe. -/

def sourceStacks : Bool → List Bool
  | false => [true, false]
  | true => [true, false, true, true]

def columns : ListBlank (Bool → Option Bool) := ListBlank.mk
  [ (fun j => if j then some true else some false),
    (fun _ => some true),
    (fun j => if j then some false else none),
    (fun j => if j then some true else none) ]

theorem columns_projects (j : Bool) :
    columns.map (Turing.proj j) = ListBlank.mk ((sourceStacks j).map some).reverse := by
  cases j
  · change ListBlank.mk [some false, some true, none, none] =
      ListBlank.mk [some false, some true]
    exact Quotient.sound' (Or.inr ⟨2, rfl⟩)
  · rfl

def program : Unit → TM2.Stmt (fun _ : Bool => Bool) Unit Bool :=
  fun _ => TM2.Stmt.halt

def pushFalse : StAct Bool (fun _ => Bool) Bool false := StAct.push (fun _ => false)

theorem outward_selected_two :
    (flip bind (TM1.step (tr program)))^[2]
      (some ⟨some (Λ'.go false pushFalse TM2.Stmt.halt), false,
        Tape.mk' ∅ (addBottom columns)⟩) =
      some ⟨some (Λ'.go false pushFalse TM2.Stmt.halt), false,
        (Tape.move Dir.right)^[2] (Tape.mk' ∅ (addBottom columns))⟩ :=
  outward_exact program false pushFalse TM2.Stmt.halt false
    sourceStacks columns columns_projects 2 (by decide)

theorem push_selected_two_other_four :
    ∃ L' : ListBlank (Bool → Option Bool),
      (∀ j, L'.map (Turing.proj j) = ListBlank.mk
        (((Function.update sourceStacks false [false, true, false]) j).map some).reverse) ∧
      ∃ run : StateTransition.EvalsTo (TM1.step (tr program))
        ⟨some (Λ'.go false pushFalse TM2.Stmt.halt), false,
          Tape.mk' ∅ (addBottom columns)⟩
        (some ⟨some (Λ'.ret TM2.Stmt.halt), false, Tape.mk' ∅ (addBottom L')⟩),
        run.steps = 6 := by
  simpa only [pushFalse, stVar, stWrite, sourceStacks, Function.update_self,
    List.length_cons, List.length_nil] using
    shuttle_witness program false pushFalse TM2.Stmt.halt false
      sourceStacks columns columns_projects

def emptySelectedStacks : Bool → List Bool
  | false => []
  | true => [true, false, true, true]

def emptySelectedColumns : ListBlank (Bool → Option Bool) := ListBlank.mk
  [ (fun j => if j then some true else none),
    (fun j => if j then some true else none),
    (fun j => if j then some false else none),
    (fun j => if j then some true else none) ]

theorem emptySelectedColumns_projects (j : Bool) :
    emptySelectedColumns.map (Turing.proj j) =
      ListBlank.mk ((emptySelectedStacks j).map some).reverse := by
  cases j
  · change ListBlank.mk [none, none, none, none] = ListBlank.mk ([] : List (Option Bool))
    exact Quotient.sound' (Or.inr ⟨4, rfl⟩)
  · rfl

def emptyPeek : StAct Bool (fun _ => Bool) Bool false :=
  StAct.peek (fun _ o => o.isNone)

def emptyPop : StAct Bool (fun _ => Bool) Bool false :=
  StAct.pop (fun _ o => o.isNone)

theorem peek_empty_other_four :
    ∃ L' : ListBlank (Bool → Option Bool),
      (∀ j, L'.map (Turing.proj j) =
        ListBlank.mk ((emptySelectedStacks j).map some).reverse) ∧
      ∃ run : StateTransition.EvalsTo (TM1.step (tr program))
        ⟨some (Λ'.go false emptyPeek TM2.Stmt.halt), false,
          Tape.mk' ∅ (addBottom emptySelectedColumns)⟩
        (some ⟨some (Λ'.ret TM2.Stmt.halt), true, Tape.mk' ∅ (addBottom L')⟩),
        run.steps = 1 := by
  have unchanged : Function.update emptySelectedStacks false [] = emptySelectedStacks :=
    Function.update_eq_self false emptySelectedStacks
  simpa only [emptyPeek, stVar, stWrite, unchanged, Function.update_self,
    emptySelectedStacks, List.head?, Option.isNone, List.length_nil, Nat.zero_add] using
    shuttle_witness program false emptyPeek TM2.Stmt.halt false
      emptySelectedStacks emptySelectedColumns emptySelectedColumns_projects

theorem pop_empty_other_four :
    ∃ L' : ListBlank (Bool → Option Bool),
      (∀ j, L'.map (Turing.proj j) =
        ListBlank.mk ((emptySelectedStacks j).map some).reverse) ∧
      ∃ run : StateTransition.EvalsTo (TM1.step (tr program))
        ⟨some (Λ'.go false emptyPop TM2.Stmt.halt), false,
          Tape.mk' ∅ (addBottom emptySelectedColumns)⟩
        (some ⟨some (Λ'.ret TM2.Stmt.halt), true, Tape.mk' ∅ (addBottom L')⟩),
        run.steps = 1 := by
  have unchanged : Function.update emptySelectedStacks false [] = emptySelectedStacks :=
    Function.update_eq_self false emptySelectedStacks
  simpa only [emptyPop, stVar, stWrite, emptySelectedStacks, List.head?,
    List.tail_nil, unchanged, Function.update_self,
    Option.isNone, List.length_nil, Nat.zero_add] using
    shuttle_witness program false emptyPop TM2.Stmt.halt false
      emptySelectedStacks emptySelectedColumns emptySelectedColumns_projects


end Cases

namespace StatementCases

open Function
open Turing Turing.TM2to1

local instance : Inhabited (Unit → Option Unit) := Pi.instInhabited
local instance : Inhabited (Bool → Option Bool) := Pi.instInhabited

def emptyFamily : Unit → List Unit := fun _ => []

def emptyColumns : ListBlank (Unit → Option Unit) := ListBlank.mk []

theorem emptyColumns_projects (j : Unit) :
    emptyColumns.map (Turing.proj j) =
      ListBlank.mk ((emptyFamily j).map some).reverse := rfl

def pushPopBody : TM2.Stmt (fun _ : Unit => Unit) Unit Unit :=
  .push () (fun _ => ()) (.pop () (fun _ _ => ()) .halt)

def pushPopProgram : Unit → TM2.Stmt (fun _ : Unit => Unit) Unit Unit :=
  fun _ => pushPopBody

theorem pushPop_source_step :
    TM2.step pushPopProgram ⟨some (), (), emptyFamily⟩ =
      some ⟨none, (), emptyFamily⟩ := by
  simp only [TM2.step, TM2.stepAux, pushPopProgram, pushPopBody,
    Function.update_self, List.tail_cons]
  congr 2

theorem pushPop_tail_steps : tailSteps pushPopBody () emptyFamily = 6 := rfl

theorem pushPop_seven_live_halt :
    ∃ b : TM1.Cfg (Γ' Unit (fun _ => Unit))
        (Λ' Unit (fun _ => Unit) Unit Unit) Unit,
      TrCfg (⟨none, (), emptyFamily⟩ : TM2.Cfg (fun _ : Unit => Unit) Unit Unit) b ∧
      ∃ run : StateTransition.EvalsTo (TM1.step (tr pushPopProgram))
        ⟨some (Λ'.normal ()), (), Tape.mk' ∅ (addBottom emptyColumns)⟩ (some b),
        run.steps = 7 := by
  have hsource : TM2.stepAux pushPopBody () emptyFamily =
      (⟨none, (), emptyFamily⟩ : TM2.Cfg (fun _ : Unit => Unit) Unit Unit) := by
    exact Option.some.inj pushPop_source_step
  simpa only [pushPopProgram, hsource, pushPop_tail_steps] using
    normal_step_witness pushPopProgram () () emptyFamily emptyColumns emptyColumns_projects

theorem pushPop_eight_outer_none :
    ∃ run : StateTransition.EvalsTo (TM1.step (tr pushPopProgram))
      ⟨some (Λ'.normal ()), (), Tape.mk' ∅ (addBottom emptyColumns)⟩ none,
      run.steps = 8 := by
  obtain ⟨b, hb, run, hrun⟩ := pushPop_seven_live_halt
  have hhalt : TM1.step (tr pushPopProgram) b = none := by
    cases hb
    rfl
  let last : StateTransition.EvalsTo (TM1.step (tr pushPopProgram)) b none :=
    { steps := 1
      evals_in_steps := by
        simp only [Function.iterate_one, Function.flip_def, bind, Option.bind_some]
        exact hhalt }
  refine ⟨StateTransition.EvalsTo.trans (TM1.step (tr pushPopProgram))
    _ _ _ run last, ?_⟩
  change 1 + run.steps = 8
  rw [hrun]

def branchBody : TM2.Stmt (fun _ : Bool => Bool) Unit Bool :=
  .load Bool.not (.branch (fun v => v) (.push false (fun _ => false) .halt) .halt)

def branchProgram : Unit → TM2.Stmt (fun _ : Bool => Bool) Unit Bool :=
  fun _ => branchBody

theorem loaded_true_branch_eight :
    ∃ b : TM1.Cfg (Γ' Bool (fun _ => Bool))
        (Λ' Bool (fun _ => Bool) Unit Bool) Bool,
      TrCfg (⟨none, true, Function.update Cases.sourceStacks false [false, true, false]⟩ :
        TM2.Cfg (fun _ : Bool => Bool) Unit Bool) b ∧
      ∃ run : StateTransition.EvalsTo (TM1.step (tr branchProgram))
        ⟨some (Λ'.normal ()), false, Tape.mk' ∅ (addBottom Cases.columns)⟩ (some b),
        run.steps = 8 := by
  simpa only [branchProgram, branchBody, TM2.stepAux, tailSteps, Bool.not_false,
    Bool.cond_true, Cases.sourceStacks, Function.update_self,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero] using
    normal_step_witness branchProgram () false Cases.sourceStacks
      Cases.columns Cases.columns_projects

theorem loaded_false_branch_one :
    ∃ b : TM1.Cfg (Γ' Bool (fun _ => Bool))
        (Λ' Bool (fun _ => Bool) Unit Bool) Bool,
      TrCfg (⟨none, false, Cases.sourceStacks⟩ :
        TM2.Cfg (fun _ : Bool => Bool) Unit Bool) b ∧
      ∃ run : StateTransition.EvalsTo (TM1.step (tr branchProgram))
        ⟨some (Λ'.normal ()), true, Tape.mk' ∅ (addBottom Cases.columns)⟩ (some b),
        run.steps = 1 := by
  simpa only [branchProgram, branchBody, TM2.stepAux, tailSteps, Bool.not_true,
    Bool.cond_false, Nat.zero_add] using
    normal_step_witness branchProgram () true Cases.sourceStacks
      Cases.columns Cases.columns_projects


end StatementCases

namespace FiniteRunCases

open Function
open Turing Turing.TM2to1

local instance : Inhabited (Unit → Option Unit) := Pi.instInhabited

def emptyFamily : Unit → List Unit := fun _ => []

def oneFamily : Unit → List Unit := fun _ => [()]

def program : Bool → TM2.Stmt (fun _ : Unit => Unit) Bool Unit
  | false => .push () (fun _ => ()) (.goto (fun _ => true))
  | true => .pop () (fun _ _ => ()) .halt

def initial : TM2.Cfg (fun _ : Unit => Unit) Bool Unit :=
  ⟨some false, (), emptyFamily⟩

def middle : TM2.Cfg (fun _ : Unit => Unit) Bool Unit :=
  ⟨some true, (), oneFamily⟩

def finished : TM2.Cfg (fun _ : Unit => Unit) Bool Unit :=
  ⟨none, (), emptyFamily⟩

def emptyColumns : ListBlank (Unit → Option Unit) := ListBlank.mk []

def targetInitial : TM1.Cfg (Γ' Unit (fun _ => Unit))
    (Λ' Unit (fun _ => Unit) Bool Unit) Unit :=
  ⟨some (Λ'.normal false), (), Tape.mk' ∅ (addBottom emptyColumns)⟩

theorem emptyColumns_projects (j : Unit) :
    emptyColumns.map (Turing.proj j) =
      ListBlank.mk ((emptyFamily j).map some).reverse := rfl

theorem initial_related : TrCfg initial targetInitial :=
  TrCfg.mk emptyColumns emptyColumns_projects

theorem first_source_step : TM2.step program initial = some middle := by
  have updated : Function.update emptyFamily () [()] = oneFamily := by
    funext j
    cases j
    rfl
  change some ⟨some true, (), Function.update emptyFamily () [()]⟩ = some middle
  rw [updated]
  rfl

theorem second_source_step : TM2.step program middle = some finished := by
  have updated : Function.update oneFamily () [] = emptyFamily := by
    funext j
    cases j
    rfl
  change some ⟨none, (), Function.update oneFamily () []⟩ = some finished
  rw [updated]
  rfl

theorem two_source_steps :
    (flip bind (TM2.step program))^[2] (some initial) = some finished := by
  rw [Function.iterate_succ_apply']
  simp only [Function.iterate_one, Function.flip_def, bind, Option.bind_some,
    first_source_step, second_source_step]

theorem program_actionBound (l : Bool) : actionBound (program l) ≤ 1 := by
  cases l <;> exact le_rfl

theorem prefix_bounds :
    ∀ (i : ℕ) (c : TM2.Cfg (fun _ : Unit => Unit) Bool Unit), i < 2 →
      (flip bind (TM2.step program))^[i] (some initial) = some c →
      (∀ j, (c.stk j).length ≤ 1) ∧
      (∀ l, c.l = some l → actionBound (program l) ≤ 1) := by
  intro i c hi hc
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · have hic : initial = c := by
      simpa only [Function.iterate_zero_apply, Option.some.injEq] using hc
    subst c
    exact ⟨fun _ => Nat.zero_le _, fun l _ => program_actionBound l⟩
  · have hmc : middle = c := by
      simpa only [Function.iterate_one, Function.flip_def, bind, Option.bind_some,
        first_source_step, Option.some.injEq] using hc
    subst c
    exact ⟨fun _ => le_rfl, fun l _ => program_actionBound l⟩

theorem two_source_steps_target_bound_fourteen :
    ∃ e : TM1.Cfg (Γ' Unit (fun _ => Unit))
        (Λ' Unit (fun _ => Unit) Bool Unit) Unit,
      TrCfg finished e ∧
      Nonempty (StateTransition.EvalsToInTime (TM1.step (tr program))
        targetInitial (some e) 14) :=
  finite_run_bounded program initial finished targetInitial initial_related
    2 1 1 two_source_steps prefix_bounds

theorem two_source_steps_target_exact_eight :
    ∃ e : TM1.Cfg (Γ' Unit (fun _ => Unit))
        (Λ' Unit (fun _ => Unit) Bool Unit) Unit,
      TrCfg finished e ∧
      ∃ run : StateTransition.EvalsTo (TM1.step (tr program)) targetInitial (some e),
        run.steps = 8 := by
  have hsource₁ : TM2.stepAux (program false) () emptyFamily = middle :=
    Option.some.inj first_source_step
  have hsource₂ : TM2.stepAux (program true) () oneFamily = finished :=
    Option.some.inj second_source_step
  have htime₁ : tailSteps (program false) () emptyFamily + 1 = 4 := rfl
  have htime₂ : tailSteps (program true) () oneFamily + 1 = 4 := rfl
  obtain ⟨d, hd, first, hfirst⟩ :=
    normal_step_witness program false () emptyFamily emptyColumns emptyColumns_projects
  rw [hsource₁] at hd
  cases hd with
  | mk L hL =>
    obtain ⟨e, he, second, hsecond⟩ := normal_step_witness program true () oneFamily L hL
    rw [hsource₂] at he
    refine ⟨e, he, StateTransition.EvalsTo.trans (TM1.step (tr program))
      _ _ _ first second, ?_⟩
    change second.steps + first.steps = 8
    rw [hfirst, hsecond, htime₁, htime₂]


end FiniteRunCases

end Examples.TuringSimulation


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
theorem emptyPeek_first_moves_left :
    primitiveStep (goCfg peekIsNone false emptyTape) =
      some ⟨(some peekAfterLeft, false), emptyTape.move Dir.left⟩ := rfl

theorem emptyPeek_left_is_off_bottom : (emptyTape.move Dir.left).head.1 = false := rfl

/-- The second primitive folds the load and returns to the bottom; the goto
still remains in the actual primitive control state. -/
theorem emptyPeek_second_returns :
    primitiveStep ⟨(some peekAfterLeft, false), emptyTape.move Dir.left⟩ =
      some ⟨(some gotoRet, true), emptyTape⟩ := by
  change some (⟨(some gotoRet, true), (emptyTape.move Dir.left).move Dir.right⟩ :
      PrimitiveCfg) = _
  rw [Tape.move_left_right]

theorem emptyPeek_third_selects_ret :
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


namespace Examples.TuringSimulation.FiniteControl

open Resources.TuringSimulation.FiniteControl

open Function Turing

def ambient : TM0.Machine Bool ℕ
  | 0, a => some (1, .write a)
  | 1, _ => none
  | n + 2, _ => some (n + 3, .move .right)

def support : Finset ℕ := {0, 1}

theorem supported : TM0.Supports ambient (↑support) := by
  constructor
  · change 0 ∈ support
    simp [support]
  · intro q a q' act hstep hq
    have choices : q = 0 ∨ q = 1 := by
      simpa only [Finset.mem_coe, support, Finset.mem_insert,
        Finset.mem_singleton] using hq
    rcases choices with rfl | rfl
    · change some (1, TM0.Stmt.write a) = some (q', act) at hstep
      cases hstep
      simp [support]
    · change (none : Option (ℕ × TM0.Stmt Bool)) = some (q', act) at hstep
      cases hstep

theorem source_zero_step (T : Tape Bool) :
    TM0.step ambient ⟨0, T⟩ = some ⟨1, T⟩ := by
  change some (TM0.Cfg.mk 1 (T.write T.head)) = some (TM0.Cfg.mk 1 T)
  rw [Tape.write_self]

theorem source_one_halts (T : Tape Bool) :
    TM0.step ambient ⟨1, T⟩ = none := rfl

def sourceLiveRun (l : List Bool) :
    StateTransition.EvalsToInTime (TM0.step ambient)
      (TM0.init l) (some ⟨1, Tape.mk₁ l⟩) 1 where
  toEvalsTo := {
    steps := 1
    evals_in_steps := by
      change TM0.step ambient (⟨0, Tape.mk₁ l⟩ : TM0.Cfg Bool ℕ) =
        some ⟨1, Tape.mk₁ l⟩
      exact source_zero_step (Tape.mk₁ l) }
  steps_le_m := Nat.le_refl 1

def sourceNoneRun (l : List Bool) :
    StateTransition.EvalsToInTime (TM0.step ambient) (TM0.init l) none 2 where
  toEvalsTo := {
    steps := 2
    evals_in_steps := by
      rw [Function.iterate_succ_apply']
      simp only [Function.iterate_one, Function.flip_def, bind, Option.bind_some]
      rw [show TM0.step ambient (TM0.init l) = some ⟨1, Tape.mk₁ l⟩ from
        source_zero_step (Tape.mk₁ l)]
      rfl }
  steps_le_m := Nat.le_refl 2

local instance : Inhabited {q : ℕ // q ∈ support} :=
  restrictedInhabited support supported.1

example : Infinite ℕ := inferInstance
example : Fintype {q : ℕ // q ∈ support} := inferInstance

noncomputable def finiteMachine : TM0.Machine Bool {q : ℕ // q ∈ support} :=
  restrictMachine ambient support supported.1

def finiteHalt (l : List Bool) : TM0.Cfg Bool {q : ℕ // q ∈ support} :=
  ⟨⟨1, by simp [support]⟩, Tape.mk₁ l⟩

/-- The actual subtype machine starts at native init on the original tape
and returns outer none with precisely the source witness's two transitions. -/
noncomputable def finiteNoneRun (l : List Bool) :
    StateTransition.EvalsToInTime (TM0.step finiteMachine)
      (TM0.init l) none 2 :=
  restrictInitialEvalsToInTime ambient support supported l none 2 (sourceNoneRun l)

theorem finiteNoneRun_steps (l : List Bool) : (finiteNoneRun l).steps = 2 := rfl

/-- The preceding live halt is represented separately and retains the full
initial tape, including the original Boolean input list. -/
noncomputable def finiteLiveRun (l : List Bool) :
    StateTransition.EvalsToInTime (TM0.step finiteMachine)
      (TM0.init l) (some (finiteHalt l)) 1 := by
  refine {
    toEvalsTo := { steps := 1, evals_in_steps := ?_ }
    steps_le_m := Nat.le_refl 1 }
  have e := (restrictInitialEvalsToInTime ambient support supported
    l (some ⟨1, Tape.mk₁ l⟩) 1 (sourceLiveRun l)).evals_in_steps
  change (flip bind (TM0.step finiteMachine))^[1] (some (TM0.init l)) =
    some (restrictCfg support supported.1 (⟨1, Tape.mk₁ l⟩ : TM0.Cfg Bool ℕ)) at e
  rw [restrictCfg_supported support supported.1
    (⟨1, Tape.mk₁ l⟩ : TM0.Cfg Bool ℕ) (by simp [support])] at e
  exact e

theorem finiteLiveRun_steps (l : List Bool) : (finiteLiveRun l).steps = 1 := rfl

theorem finiteHalt_halts (l : List Bool) :
    TM0.step finiteMachine (finiteHalt l) = none := by
  have e := restrict_step ambient support supported
    (⟨1, Tape.mk₁ l⟩ : TM0.Cfg Bool ℕ) (by simp [support])
  rw [source_one_halts, Option.map_none,
    restrictCfg_supported support supported.1
      (⟨1, Tape.mk₁ l⟩ : TM0.Cfg Bool ℕ) (by simp [support])] at e
  exact e.symm

end Examples.TuringSimulation.FiniteControl


namespace Examples.TuringSimulation.FiniteControl

open Resources.TuringSimulation.FiniteControl

open Turing

local instance : Inhabited {q : ℕ // q ∈ support} :=
  restrictedInhabited support supported.1

def closedFiniteMachine : TM0.Machine Bool {q : ℕ // q ∈ support} :=
  closedRestrictMachine ambient support supported

theorem closedFiniteMachine_eq : closedFiniteMachine = finiteMachine :=
  closedRestrictMachine_eq ambient support supported

def closedFiniteLiveRun (l : List Bool) :
    StateTransition.EvalsToInTime (TM0.step closedFiniteMachine)
      (TM0.init l) (some (finiteHalt l)) 1 where
  toEvalsTo := {
    steps := 1
    evals_in_steps := by
      rw [closedFiniteMachine_eq]
      exact (finiteLiveRun l).evals_in_steps }
  steps_le_m := Nat.le_refl 1

def closedFiniteNoneRun (l : List Bool) :
    StateTransition.EvalsToInTime (TM0.step closedFiniteMachine)
      (TM0.init l) none 2 where
  toEvalsTo := {
    steps := 2
    evals_in_steps := by
      rw [closedFiniteMachine_eq]
      exact (finiteNoneRun l).evals_in_steps }
  steps_le_m := Nat.le_refl 2

theorem closedFiniteLiveRun_steps (l : List Bool) :
    (closedFiniteLiveRun l).steps = 1 := rfl

theorem closedFiniteNoneRun_steps (l : List Bool) :
    (closedFiniteNoneRun l).steps = 2 := rfl

end Examples.TuringSimulation.FiniteControl

namespace Examples.TuringSimulation.OrdinaryInput

open Function Turing
open Resources.TuringSimulation

abbrev Letters := TM2to1.Γ' Bool (fun _ => Bool)

def haltSource : @TM0.Machine Letters Bool ⟨true⟩ := fun _ _ => none

def emit (a : Letters) : Letters := MarkedInput.symbol false ((a.2 true).getD false)

def marked (b : Bool) : Letters := (true, (MarkedInput.symbol false b).2)

theorem empty_prelude_is_one_actual_write :
    letI : Inhabited Bool := ⟨true⟩
    (flip Bind.bind (TM0.step (MarkedInput.machine false haltSource emit)))^[1]
      (some (TM0.init (MarkedInput.input false ([] : List Bool)))) =
      some ⟨.run true, Tape.mk (true, fun _ => none) ∅ ∅⟩ := by
  let : Inhabited Bool := ⟨true⟩
  exact MarkedInput.prelude_exact false haltSource emit []

theorem false_prelude_costs_three_and_keeps_present_false :
    letI : Inhabited Bool := ⟨true⟩
    (flip Bind.bind (TM0.step (MarkedInput.machine false haltSource emit)))^[3]
      (some (TM0.init (MarkedInput.input false [false]))) =
      some ⟨.run true, Tape.mk (marked false) ∅ ∅⟩ := by
  let : Inhabited Bool := ⟨true⟩
  exact MarkedInput.prelude_exact false haltSource emit [false]

theorem true_prelude_costs_three :
    letI : Inhabited Bool := ⟨true⟩
    (flip Bind.bind (TM0.step (MarkedInput.machine false haltSource emit)))^[3]
      (some (TM0.init (MarkedInput.input false [true]))) =
      some ⟨.run true, Tape.mk (marked true) ∅ ∅⟩ := by
  let : Inhabited Bool := ⟨true⟩
  exact MarkedInput.prelude_exact false haltSource emit [true]

theorem false_true_prelude_exposes_the_reflected_orientation :
    letI : Inhabited Bool := ⟨true⟩
    (flip Bind.bind (TM0.step (MarkedInput.machine false haltSource emit)))^[4]
      (some (TM0.init (MarkedInput.input false [false, true]))) =
      some ⟨.run true,
        Tape.mk (marked true) (ListBlank.mk [MarkedInput.symbol false false]) ∅⟩ := by
  let : Inhabited Bool := ⟨true⟩
  exact MarkedInput.prelude_exact false haltSource emit [false, true]

theorem true_false_prelude_is_a_different_complete_tape :
    letI : Inhabited Bool := ⟨true⟩
    (flip Bind.bind (TM0.step (MarkedInput.machine false haltSource emit)))^[4]
      (some (TM0.init (MarkedInput.input false [true, false]))) =
      some ⟨.run true,
        Tape.mk (marked false) (ListBlank.mk [MarkedInput.symbol false true]) ∅⟩ := by
  let : Inhabited Bool := ⟨true⟩
  exact MarkedInput.prelude_exact false haltSource emit [true, false]

theorem repeated_false_does_not_terminate_the_scan :
    letI : Inhabited Bool := ⟨true⟩
    (flip Bind.bind (TM0.step (MarkedInput.machine false haltSource emit)))^[4]
      (some (TM0.init (MarkedInput.input false [false, false]))) =
      some ⟨.run true,
        Tape.mk (marked false) (ListBlank.mk [MarkedInput.symbol false false]) ∅⟩ := by
  let : Inhabited Bool := ⟨true⟩
  exact MarkedInput.prelude_exact false haltSource emit [false, false]

theorem length_three_prelude_has_nearest_first_left_order :
    letI : Inhabited Bool := ⟨true⟩
    (flip Bind.bind (TM0.step (MarkedInput.machine false haltSource emit)))^[5]
      (some (TM0.init (MarkedInput.input false [true, false, false]))) =
      some ⟨.run true,
        Tape.mk (marked false)
          (ListBlank.mk [MarkedInput.symbol false false, MarkedInput.symbol false true]) ∅⟩ := by
  let : Inhabited Bool := ⟨true⟩
  exact MarkedInput.prelude_exact false haltSource emit [true, false, false]

theorem ordinary_false_is_not_the_blank :
    (MarkedInput.symbol false false : Letters) ≠ default :=
  MarkedInput.symbol_ne_blank (Γ := fun _ : Bool => Bool) false false

theorem empty_and_false_have_distinct_complete_native_input_tapes :
    (Tape.mk₁ (MarkedInput.input false ([] : List Bool)) : Tape Letters) ≠
      Tape.mk₁ (MarkedInput.input false [false]) := by
  intro same
  have observed := congrArg (fun T : Tape Letters => T.head.2 false) same
  change none = some false at observed
  cases observed

theorem ordinary_false_and_true_are_distinct :
    (MarkedInput.symbol false false : Letters) ≠ MarkedInput.symbol false true := by
  intro same
  have impossible := MarkedInput.symbol_injective false same
  cases impossible

theorem input_and_fuel_are_distinct : (false : Bool) ≠ true := by decide

theorem output_write_and_following_none (answer : Bool) :
    letI : Inhabited Bool := ⟨true⟩
    let a : Letters := (true, Function.update (fun _ => none) true (some answer))
    TM0.step (MarkedInput.machine false haltSource emit)
        ⟨.run true, Tape.mk₁ [a]⟩ =
      some ⟨.done, Tape.mk₁ [MarkedInput.symbol false answer]⟩ ∧
    TM0.step (MarkedInput.machine false haltSource emit)
        ⟨.done, Tape.mk₁ [MarkedInput.symbol false answer]⟩ = none := by
  let : Inhabited Bool := ⟨true⟩
  dsimp only
  constructor
  · exact MarkedInput.emit_singleton_step false haltSource emit true
      (true, Function.update (fun _ => none) true (some answer)) rfl
  · exact MarkedInput.done_step false haltSource emit _

end Examples.TuringSimulation.OrdinaryInput

namespace Examples.TuringSimulation.PolynomialDecider

open Function Turing
open Resources.TuringSimulation

/-- A fixed one-write decider; the supplied starting state is true, whereas
the ambient Boolean default is false and would already be stopped. -/
def constantMachine (answer : Bool) : @TM0.Machine (Option Bool) Bool ⟨true⟩
  | true, _ => some (false, .write (some answer))
  | false, _ => none

def constantRun (answer : Bool) (raw : List Bool) :
    letI : Inhabited Bool := ⟨true⟩
    StateTransition.EvalsTo (TM0.step (constantMachine answer))
      (TM0.init (raw.map some))
      (some ⟨false, (Tape.mk₁ (raw.map some)).write (some answer)⟩) := by
  let : Inhabited Bool := ⟨true⟩
  exact { steps := 1, evals_in_steps := rfl }

theorem constantRun_steps (answer : Bool) (raw : List Bool) :
    (constantRun answer raw).steps = 1 := rfl

noncomputable def constantDecider (answer : Bool) :
    PolynomialBooleanDecider (fun _ => answer) where
  Alphabet := Option Bool
  Control := Bool
  alphabetFintype := inferInstance
  controlFintype := inferInstance
  blank := none
  start := true
  bit := ⟨some, by intro a b h; exact Option.some.inj h⟩
  bit_ne_blank := by intro b h; cases h
  machine := constantMachine answer
  time := Polynomial.C 1
  run := by
    intro raw
    refine ⟨⟨false, (Tape.mk₁ (raw.map some)).write (some answer)⟩, ⟨?_⟩, rfl, ?_⟩
    · exact
        { toEvalsTo := constantRun answer raw
          steps_le_m := by simp only [constantRun_steps, Polynomial.eval_C, le_refl] }
    · rfl

theorem constantDecider_uses_true_start (answer : Bool) :
    (constantDecider answer).start = true := rfl

theorem empty_and_present_false_inputs_differ (answer : Bool) :
    ([] : List Bool).map (constantDecider answer).bit ≠
      [false].map (constantDecider answer).bit := by
  intro h
  cases h

theorem present_false_output_is_not_blank :
    (constantDecider false).bit false ≠ (constantDecider false).blank :=
  (constantDecider false).false_ne_blank

end Examples.TuringSimulation.PolynomialDecider

namespace Examples.TuringSimulation.PrimitiveReflection

open Function Turing
open Examples.TuringSimulation.Primitive
open Resources.TuringSimulation

def reflectedStep : PrimitiveCfg → Option PrimitiveCfg :=
  TM0.step (TapeReflection.machine (TM1to0.tr tapeProgram))

theorem emptyPeek_first_moves_right :
    reflectedStep (TapeReflection.configuration (goCfg peekIsNone false emptyTape)) =
      some ⟨(some peekAfterLeft, false), emptyTape.move Dir.right⟩ := by
  rw [reflectedStep, TapeReflection.step]
  change (primitiveStep (goCfg peekIsNone false emptyTape)).map
    TapeReflection.configuration = _
  rw [emptyPeek_first_moves_left]
  rfl

theorem emptyPeek_right_is_off_bottom : (emptyTape.move Dir.right).head.1 = false := rfl

theorem emptyPeek_second_returns_left :
    reflectedStep ⟨(some peekAfterLeft, false), emptyTape.move Dir.right⟩ =
      some ⟨(some gotoRet, true), emptyTape⟩ := by
  change reflectedStep (TapeReflection.configuration
    (⟨(some peekAfterLeft, false), emptyTape.move Dir.left⟩ : PrimitiveCfg)) = _
  rw [reflectedStep, TapeReflection.step]
  change (primitiveStep ⟨(some peekAfterLeft, false), emptyTape.move Dir.left⟩).map
    TapeReflection.configuration = _
  rw [emptyPeek_second_returns]
  rfl

theorem emptyPeek_third_still_selects_ret :
    reflectedStep ⟨(some gotoRet, true), emptyTape⟩ =
      some (retCfg true emptyTape) := by
  change reflectedStep (TapeReflection.configuration
    (⟨(some gotoRet, true), emptyTape⟩ : PrimitiveCfg)) = _
  rw [reflectedStep, TapeReflection.step]
  change (primitiveStep ⟨(some gotoRet, true), emptyTape⟩).map
    TapeReflection.configuration = _
  rw [emptyPeek_third_selects_ret]
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
theorem rightLeft_positions :
    (List.range 4).map (headPosition rightLeftMachine emptyStart 0) = [0, 1, 0, 0] := by decide

theorem rightLeft_visits : visitedCells rightLeftMachine emptyStart 0 3 = {0, 1} := by decide

theorem rightLeft_interval :
    visitedInterval rightLeftMachine emptyStart 0 0 3 = Finset.Icc 0 1 := by decide

theorem rightLeft_live_halt :
    cfgAt rightLeftMachine emptyStart 2 = some ⟨.stopped, emptyStart.Tape⟩ := by
  change some (⟨.stopped, (emptyStart.Tape.move Dir.right).move Dir.left⟩ : Cfg) = _
  rw [Tape.move_right_left]

theorem rightLeft_outer_none : cfgAt rightLeftMachine emptyStart 3 = none := rfl

theorem writeErase_positions :
    (List.range 4).map (headPosition writeEraseMachine emptyStart 0) = [0, 0, 0, 0] := by decide

theorem writeErase_visits : visitedCells writeEraseMachine emptyStart 0 3 = {0} := by decide

theorem writeErase_live_halt :
    cfgAt writeEraseMachine emptyStart 2 = some ⟨.stopped, emptyStart.Tape⟩ := rfl

theorem twoLeft_positions :
    (List.range 3).map (headPosition twoLeftMachine twoInputStart 0) = [0, -1, -2] := by decide

theorem twoLeft_visits :
    visitedCells twoLeftMachine twoInputStart 0 2 = {-2, -1, 0} := by decide

/-- Cell 1 is declared input but has never been visited; the union is named
explicitly so this stronger input-inclusive convention cannot be mistaken. -/
theorem twoLeft_input_plus_visits :
    inputVisitedCells twoLeftMachine twoInputStart 0 2 2 = {-2, -1, 0, 1} := by decide

theorem twoLeft_interval :
    visitedInterval twoLeftMachine twoInputStart 0 2 2 = Finset.Icc (-2) 1 := by decide

theorem twoLeft_attains_bound :
    (visitedInterval twoLeftMachine twoInputStart 0 2 2).card = max 2 1 + 2 := by decide

theorem shifted_rightLeft_positions :
    (List.range 4).map (headPosition rightLeftMachine emptyStart 7) = [7, 8, 7, 7] := by decide

theorem shifted_rightLeft_visits :
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

namespace Examples.TuringSimulation.OrdinaryPackageCases

open Function Turing
open Resources.TuringSimulation
open Resources.TuringSimulation.StackToTape

def fixtureAlphabet : Bool → Type
  | false => Option Bool
  | true => Bool

instance fixtureAlphabetFintype (k : Bool) : Fintype (fixtureAlphabet k) := by
  cases k with
  | false => exact (inferInstance : Fintype (Option Bool))
  | true => exact (inferInstance : Fintype Bool)

def fixture : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := fixtureAlphabet
  Λ := Bool
  main := true
  σ := Bool
  initialState := true
  m _ := .halt

def outputLetter : Bool → Option Bool := some

def cell (a : Option Bool) : OrdinaryPackage.Alphabet fixture :=
  MarkedInput.symbol (Γ := fixture.Γ) fixture.k₀ a

def nativeInput (raw : List (Option Bool)) : List (OrdinaryPackage.Alphabet fixture) :=
  raw.map cell

def M : @TM0.Machine (OrdinaryPackage.Alphabet fixture) (OrdinaryPackage.Control fixture)
    (OrdinaryPackage.controlInhabited fixture) :=
  OrdinaryPackage.machine fixture outputLetter true

theorem stores_are_distinct : fixture.k₀ ≠ fixture.k₁ := by
  intro impossible
  cases impossible

theorem alphabet_is_finite : Nonempty (Fintype (OrdinaryPackage.Alphabet fixture)) := by
  let : ∀ k : fixture.K, Fintype (fixture.Γ k) := fixtureAlphabetFintype
  exact ⟨OrdinaryPackage.alphabetFintype fixture⟩

theorem working_alphabet_has_twenty_four_symbols :
    letI : ∀ k : fixture.K, Fintype (fixture.Γ k) := fixtureAlphabetFintype
    letI : Fintype (OrdinaryPackage.Alphabet fixture) := OrdinaryPackage.alphabetFintype fixture
    Fintype.card (OrdinaryPackage.Alphabet fixture) = 24 := by
  let : ∀ k : Bool, Fintype (fixtureAlphabet k) := fixtureAlphabetFintype
  change Fintype.card (Bool × ((k : Bool) → Option (fixtureAlphabet k))) = 24
  rw [Fintype.card_prod, Fintype.card_pi,
    Fintype.prod_bool (fun k : Bool => Fintype.card (Option (fixtureAlphabet k)))]
  change Fintype.card Bool * (Fintype.card (Option Bool) *
    Fintype.card (Option (Option Bool))) = 24
  simp only [Fintype.card_option, Fintype.card_bool]

theorem wrapper_control_is_finite : Nonempty (Fintype (OrdinaryPackage.Control fixture)) :=
  ⟨OrdinaryPackage.controlFintype fixture⟩

theorem supplied_main_is_true : fixture.main = true := rfl

theorem supplied_register_is_true : (OrdinaryPackage.sourceDefault fixture).val.2 = true := rfl

theorem supplied_source_control :
    (OrdinaryPackage.sourceDefault fixture).val =
      (some ((TM2to1.tr fixture.m) (.normal true)), true) := rfl

theorem wrapper_starts_at_prelude :
    (OrdinaryPackage.controlInhabited fixture).default =
      (MarkedInput.Control.start : OrdinaryPackage.Control fixture) := rfl

theorem designated_input_preserves_length (raw : List (Option Bool)) :
    (nativeInput raw).length = raw.length := by
  simp only [nativeInput, List.length_map]

theorem delimiter_cell_is_present : (cell none).2 fixture.k₀ = some none :=
  MarkedInput.symbol_selected (Γ := fixture.Γ) fixture.k₀ none

theorem false_cell_is_present : (cell (some false)).2 fixture.k₀ = some (some false) :=
  MarkedInput.symbol_selected (Γ := fixture.Γ) fixture.k₀ (some false)

theorem true_cell_is_present : (cell (some true)).2 fixture.k₀ = some (some true) :=
  MarkedInput.symbol_selected (Γ := fixture.Γ) fixture.k₀ (some true)

theorem delimiter_cell_ne_blank : cell none ≠ (default : OrdinaryPackage.Alphabet fixture) :=
  MarkedInput.symbol_ne_blank (Γ := fixture.Γ) fixture.k₀ none

theorem false_cell_ne_blank : cell (some false) ≠ (default : OrdinaryPackage.Alphabet fixture) :=
  MarkedInput.symbol_ne_blank (Γ := fixture.Γ) fixture.k₀ (some false)

theorem delimiter_cell_ne_false : cell none ≠ cell (some false) := by
  intro same
  have impossible : (none : Option Bool) = some false :=
    MarkedInput.symbol_injective (Γ := fixture.Γ) fixture.k₀ same
  cases impossible

theorem empty_input_ne_delimiter : nativeInput [] ≠ nativeInput [none] := by
  intro impossible
  cases impossible

theorem empty_prelude_one_step :
    (flip Bind.bind (TM0.step M))^[1] (some (TM0.init (nativeInput []))) =
      some ⟨.run (OrdinaryPackage.sourceDefault fixture),
        Tape.mk (true, fun _ => none) ∅ ∅⟩ :=
  OrdinaryPackage.prelude_exact fixture outputLetter true []

private theorem singleton_prelude_three_steps (a : Option Bool) :
    (flip Bind.bind (TM0.step M))^[3] (some (TM0.init (nativeInput [a]))) =
      some ⟨.run (OrdinaryPackage.sourceDefault fixture), Tape.mk (true, (cell a).2) ∅ ∅⟩ := by
  have boundary : TapeReflection.tape
      (Tape.mk₁ (TM2to1.trInit (Γ := fixture.Γ) fixture.k₀ [a])) =
        Tape.mk (true, (cell a).2) ∅ ∅ := rfl
  exact (OrdinaryPackage.prelude_exact fixture outputLetter true [a]).trans
    (congrArg
      (fun T : Tape (OrdinaryPackage.Alphabet fixture) =>
        (some ⟨.run (OrdinaryPackage.sourceDefault fixture), T⟩ :
          Option (TM0.Cfg (OrdinaryPackage.Alphabet fixture) (OrdinaryPackage.Control fixture))))
      boundary)

theorem delimiter_prelude_three_steps :
    (flip Bind.bind (TM0.step M))^[3] (some (TM0.init (nativeInput [none]))) =
      some ⟨.run (OrdinaryPackage.sourceDefault fixture), Tape.mk (true, (cell none).2) ∅ ∅⟩ :=
  singleton_prelude_three_steps none

theorem present_false_prelude_three_steps :
    (flip Bind.bind (TM0.step M))^[3] (some (TM0.init (nativeInput [some false]))) =
      some ⟨.run (OrdinaryPackage.sourceDefault fixture),
        Tape.mk (true, (cell (some false)).2) ∅ ∅⟩ :=
  singleton_prelude_three_steps (some false)

theorem present_true_prelude_three_steps :
    (flip Bind.bind (TM0.step M))^[3] (some (TM0.init (nativeInput [some true]))) =
      some ⟨.run (OrdinaryPackage.sourceDefault fixture),
        Tape.mk (true, (cell (some true)).2) ∅ ∅⟩ :=
  singleton_prelude_three_steps (some true)

/-- The left list is nearest first. The final input letter is marked, and
the two preceding letters remain in their actual reversed physical order. -/
theorem orientation_prelude_five_steps :
    (flip Bind.bind (TM0.step M))^[5]
      (some (TM0.init (nativeInput [some false, none, some true]))) =
      some ⟨.run (OrdinaryPackage.sourceDefault fixture),
        Tape.mk (true, (cell (some true)).2)
          (ListBlank.mk [cell none, cell (some false)]) ∅⟩ := by
  have boundary : TapeReflection.tape
      (Tape.mk₁ (TM2to1.trInit (Γ := fixture.Γ) fixture.k₀ [some false, none, some true])) =
        Tape.mk (true, (cell (some true)).2)
          (ListBlank.mk [cell none, cell (some false)]) ∅ := rfl
  exact (OrdinaryPackage.prelude_exact fixture outputLetter true
    [some false, none, some true]).trans
      (congrArg
        (fun T : Tape (OrdinaryPackage.Alphabet fixture) =>
          (some ⟨.run (OrdinaryPackage.sourceDefault fixture), T⟩ :
            Option (TM0.Cfg (OrdinaryPackage.Alphabet fixture) (OrdinaryPackage.Control fixture))))
        boundary)

theorem false_halt_has_empty_input_track :
    SingletonOutput.haltRow fixture false fixture.k₀ = none :=
  OrdinaryPackage.haltRow_input fixture false stores_are_distinct

theorem false_halt_has_present_output_track :
    SingletonOutput.haltRow fixture false fixture.k₁ = some false :=
  OrdinaryPackage.haltRow_output fixture false

theorem false_output_ignores_true_fallback :
    OrdinaryPackage.emitter fixture outputLetter true
        (true, SingletonOutput.haltRow fixture false) = cell (some false) :=
  OrdinaryPackage.emitter_halt_row fixture outputLetter true false

theorem true_output_ignores_false_fallback :
    OrdinaryPackage.emitter fixture outputLetter false
        (true, SingletonOutput.haltRow fixture true) = cell (some true) :=
  OrdinaryPackage.emitter_halt_row fixture outputLetter false true

/-- This is a function-totality case, not a claim that blank is a valid
singleton source output. -/
theorem blank_cell_uses_total_fallback :
    OrdinaryPackage.emitter fixture outputLetter true
        (default : OrdinaryPackage.Alphabet fixture) = cell (some true) := rfl

noncomputable def haltedControl : Package.Control fixture :=
  ⟨(none, true), SingletonOutput.package_halt_supported fixture true⟩

private theorem native_output_one_step (fallback answer : Bool) :
    TM0.step (OrdinaryPackage.machine fixture outputLetter fallback)
      ⟨.run haltedControl, Tape.mk₁ [(true, SingletonOutput.haltRow fixture answer)]⟩ =
      some ⟨.done, Tape.mk₁ [cell (some answer)]⟩ := by
  let : Inhabited (Package.Control fixture) := Package.controlInhabited fixture
  have actual := MarkedInput.emit_singleton_step (Γ := fixture.Γ) fixture.k₀
    (Package.closedMachine fixture) (OrdinaryPackage.emitter fixture outputLetter fallback)
    haltedControl (true, SingletonOutput.haltRow fixture answer) (by rfl)
  exact actual.trans
    (congrArg
      (fun a : OrdinaryPackage.Alphabet fixture =>
        (some ⟨MarkedInput.Control.done, Tape.mk₁ [a]⟩ :
          Option (TM0.Cfg (OrdinaryPackage.Alphabet fixture) (OrdinaryPackage.Control fixture))))
      (OrdinaryPackage.emitter_halt_row fixture outputLetter fallback answer))

theorem false_output_one_step :
    TM0.step M
      ⟨.run haltedControl, Tape.mk₁ [(true, SingletonOutput.haltRow fixture false)]⟩ =
      some ⟨.done, Tape.mk₁ [cell (some false)]⟩ :=
  native_output_one_step true false

theorem true_output_one_step :
    TM0.step (OrdinaryPackage.machine fixture outputLetter false)
      ⟨.run haltedControl, Tape.mk₁ [(true, SingletonOutput.haltRow fixture true)]⟩ =
      some ⟨.done, Tape.mk₁ [cell (some true)]⟩ :=
  native_output_one_step false true

theorem false_output_next_step_is_none :
    TM0.step M ⟨.done, Tape.mk₁ [cell (some false)]⟩ = none := rfl

theorem false_output_outer_none_at_two :
    (flip Bind.bind (TM0.step M))^[2]
      (some ⟨.run haltedControl, Tape.mk₁ [(true, SingletonOutput.haltRow fixture false)]⟩) =
      none := by
  change Bind.bind
    (TM0.step M ⟨.run haltedControl, Tape.mk₁ [(true, SingletonOutput.haltRow fixture false)]⟩)
    (TM0.step M) = none
  rw [false_output_one_step]
  rfl

/-- These literals test the count formula on a retained count of 7, rather
than replacing that count by its allowance 10. They do not assert a fixture
source run from input to output. -/
theorem stored_count_literals :
    1 + (7 + MarkedInput.preludeSteps ([] : List (Option Bool))) = 9 ∧
      1 + (7 + MarkedInput.preludeSteps [some false]) = 11 ∧
      1 + (7 + MarkedInput.preludeSteps [some false, none, some true]) = 13 :=
  ⟨rfl, rfl, rfl⟩

theorem bound_literals :
    MarkedInput.preludeSteps ([] : List (Option Bool)) + 10 + 1 = 12 ∧
      MarkedInput.preludeSteps [some false] + 10 + 1 = 14 ∧
      MarkedInput.preludeSteps [some false, none, some true] + 10 + 1 = 16 :=
  ⟨rfl, rfl, rfl⟩

theorem distinct_outer_none_literals :
    1 + 9 = 10 ∧ 1 + 11 = 12 ∧ 1 + 13 = 14 ∧
      MarkedInput.preludeSteps ([] : List (Option Bool)) + 10 + 2 = 13 ∧
      MarkedInput.preludeSteps [some false] + 10 + 2 = 15 ∧
      MarkedInput.preludeSteps [some false, none, some true] + 10 + 2 = 17 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Examples.TuringSimulation.OrdinaryPackageCases

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
