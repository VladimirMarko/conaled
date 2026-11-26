import Applications.Resources.TuringSimulation.StackToTape

set_option autoImplicit false
set_option warningAsError true

/-!
# Connected native stack-to-tape timing examples

Fixed calculations distinguish the selected track from a longer unrelated
track, preserve empty-pop/peek register effects, count internal push/pop work,
separate live halt from outer none, follow a register-changing branch, and
compose two actual source steps. The final two-step example has exact target
time eight and a separately derived upper bound fourteen.
-/

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

theorem pushPopProgram_source_step :
    TM2.step pushPopProgram ⟨some (), (), emptyFamily⟩ =
      some ⟨none, (), emptyFamily⟩ := by
  simp only [TM2.step, TM2.stepAux, pushPopProgram, pushPopBody,
    Function.update_self, List.tail_cons]
  congr 2

theorem tailSteps_pushPopBody : tailSteps pushPopBody () emptyFamily = 6 := rfl

theorem pushPopProgram_seven_live_halt :
    ∃ b : TM1.Cfg (Γ' Unit (fun _ => Unit))
        (Λ' Unit (fun _ => Unit) Unit Unit) Unit,
      TrCfg (⟨none, (), emptyFamily⟩ : TM2.Cfg (fun _ : Unit => Unit) Unit Unit) b ∧
      ∃ run : StateTransition.EvalsTo (TM1.step (tr pushPopProgram))
        ⟨some (Λ'.normal ()), (), Tape.mk' ∅ (addBottom emptyColumns)⟩ (some b),
        run.steps = 7 := by
  have hsource : TM2.stepAux pushPopBody () emptyFamily =
      (⟨none, (), emptyFamily⟩ : TM2.Cfg (fun _ : Unit => Unit) Unit Unit) := by
    exact Option.some.inj pushPopProgram_source_step
  simpa only [pushPopProgram, hsource, tailSteps_pushPopBody] using
    normal_step_witness pushPopProgram () () emptyFamily emptyColumns emptyColumns_projects

theorem pushPopProgram_eight_outer_none :
    ∃ run : StateTransition.EvalsTo (TM1.step (tr pushPopProgram))
      ⟨some (Λ'.normal ()), (), Tape.mk' ∅ (addBottom emptyColumns)⟩ none,
      run.steps = 8 := by
  obtain ⟨b, hb, run, hrun⟩ := pushPopProgram_seven_live_halt
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
