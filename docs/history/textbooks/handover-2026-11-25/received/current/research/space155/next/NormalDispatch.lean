import Applications.Resources.TuringSimulation.TapeToPrimitive
import Applications.Resources.TuringSimulation.VisitedSpace
import Examples.TuringSimulation

/-!
# The actual stationary primitive dispatch of a translated normal body

Uncompiled external draft. EXPECTATIONS.md was frozen before this file.
The emitted action is proved from trAux. Full tape equality is a consequence
of that actual self-write, not the premise used to infer displacement.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.TuringSimulation.TapeToPrimitive

open Turing
open Resources.TuringSimulation.VisitedSpace

variable {K : Type*} {Δ : K → Type*} {L R : Type*}

/-- The existing positive exact count and syntax bound meet at one for every
translated normal body, including actual register loads and branch choices. -/
theorem primitiveSteps_trNormal (q : TM2.Stmt Δ L R) (v : R)
    (T : Tape (TM2to1.Γ' K Δ)) :
    primitiveSteps (TM2to1.trNormal q) v T = 1 := by
  have hle := primitiveSteps_le_bound (TM2to1.trNormal q) v T
  rw [primitiveBound_trNormal] at hle
  exact Nat.le_antisymm hle
    (Nat.succ_le_of_lt (primitiveSteps_pos (TM2to1.trNormal q) v T))

/-- Every native leaf reached through a translated normal body's folded
loads and branches emits a write of the actual current symbol. -/
theorem trAux_trNormal_command
    (P : TM2to1.Λ' K Δ L R →
      TM1.Stmt (TM2to1.Γ' K Δ) (TM2to1.Λ' K Δ L R) R)
    (q : TM2.Stmt Δ L R) (v : R) (a : TM2to1.Γ' K Δ) :
    (TM1to0.trAux P a (TM2to1.trNormal q) v).2 = TM0.Stmt.write a := by
  induction q using TM2to1.stmtStRec generalizing v with
  | run _ _ _ _ => simp only [TM2to1.trNormal_run, TM1to0.trAux]
  | load f _ ih => exact ih (f v)
  | branch p _ _ ih₁ ih₂ =>
    cases h : p v
    · simpa only [TM2to1.trNormal, TM1to0.trAux, h, Bool.cond_false] using ih₂ v
    · simpa only [TM2to1.trNormal, TM1to0.trAux, h, Bool.cond_true] using ih₁ v
  | goto _ => rfl
  | halt => rfl

section Dispatch

variable [Inhabited L] [Inhabited R]

/-- One actual primitive prefix executes the full normal body, retaining its
complete translated endpoint and actual command. Its self-write preserves the
entire tape and the supplied integer head coordinate. -/
theorem trNormal_prefix
    (P : TM2to1.Λ' K Δ L R →
      TM1.Stmt (TM2to1.Γ' K Δ) (TM2to1.Λ' K Δ L R) R)
    (q : TM2.Stmt Δ L R) (v : R) (T : Tape (TM2to1.Γ' K Δ)) (origin : ℤ) :
    let start : TM0.Cfg (TM2to1.Γ' K Δ) (TM1to0.Λ' P) :=
      ⟨(some (TM2to1.trNormal q), v), T⟩
    let finish := TM1to0.trCfg P (TM1.stepAux (TM2to1.trNormal q) v T)
    commandAt (TM1to0.tr P) start 0 =
        some ((TM1to0.trAux P T.head (TM2to1.trNormal q) v).1,
          TM0.Stmt.write T.head) ∧
      cfgAt (TM1to0.tr P) start 1 = some finish ∧
      headPosition (TM1to0.tr P) start origin 1 = origin ∧ finish.Tape = T := by
  let start : TM0.Cfg (TM2to1.Γ' K Δ) (TM1to0.Λ' P) :=
    ⟨(some (TM2to1.trNormal q), v), T⟩
  let finish := TM1to0.trCfg P (TM1.stepAux (TM2to1.trNormal q) v T)
  have hcommand : TM1to0.tr P start.q start.Tape.head =
      some ((TM1to0.trAux P T.head (TM2to1.trNormal q) v).1,
        TM0.Stmt.write T.head) := by
    change some (TM1to0.trAux P T.head (TM2to1.trNormal q) v) = _
    exact congrArg some (Prod.ext rfl (trAux_trNormal_command P q v T.head))
  have hcommandAt : commandAt (TM1to0.tr P) start 0 =
      some ((TM1to0.trAux P T.head (TM2to1.trNormal q) v).1,
        TM0.Stmt.write T.head) := hcommand
  have hcfg : cfgAt (TM1to0.tr P) start 1 = some finish := by
    have h := statement_exact P (TM2to1.trNormal q) v T
    rw [primitiveSteps_trNormal q v T] at h
    exact h
  have hpos : headPosition (TM1to0.tr P) start origin 1 = origin := by
    rw [headPosition_succ, headPosition_zero, hcommandAt]
    exact add_zero origin
  have hstep : TM0.step (TM1to0.tr P) start = some finish := by
    have h := hcfg
    rw [cfgAt_succ, cfgAt_zero] at h
    exact h
  have hpreserve : TM0.step (TM1to0.tr P) start =
      some (⟨(TM1to0.trAux P T.head (TM2to1.trNormal q) v).1, T⟩ :
        TM0.Cfg (TM2to1.Γ' K Δ) (TM1to0.Λ' P)) := by
    change (TM1to0.tr P start.q start.Tape.head).map _ = _
    rw [hcommand]
    change some (⟨(TM1to0.trAux P T.head (TM2to1.trNormal q) v).1,
      T.write T.head⟩ : TM0.Cfg (TM2to1.Γ' K Δ) (TM1to0.Λ' P)) = _
    rw [Tape.write_self]
  have htape : finish.Tape = T :=
    congrArg (fun c : TM0.Cfg (TM2to1.Γ' K Δ) (TM1to0.Λ' P) => c.Tape)
      (Option.some.inj (hstep.symm.trans hpreserve))
  exact ⟨hcommandAt, hcfg, hpos, htape⟩

/-- Specialize the stationary prefix to the actual source program's normal
control. Source register updates and branch selection remain inside stepAux. -/
theorem normal_control_prefix [DecidableEq K]
    (M : L → TM2.Stmt Δ L R) (l : L) (v : R)
    (T : Tape (TM2to1.Γ' K Δ)) (origin : ℤ) :
    let P := TM2to1.tr M
    let start := TM1to0.trCfg P
      (⟨some (TM2to1.Λ'.normal l), v, T⟩ :
        TM1.Cfg (TM2to1.Γ' K Δ) (TM2to1.Λ' K Δ L R) R)
    let finish := TM1to0.trCfg P (TM1.stepAux (TM2to1.trNormal (M l)) v T)
    commandAt (TM1to0.tr P) start 0 =
        some ((TM1to0.trAux P T.head (TM2to1.trNormal (M l)) v).1,
          TM0.Stmt.write T.head) ∧
      cfgAt (TM1to0.tr P) start 1 = some finish ∧
      headPosition (TM1to0.tr P) start origin 1 = origin ∧ finish.Tape = T := by
  exact trNormal_prefix (TM2to1.tr M) (M l) v T origin

end Dispatch

end Resources.TuringSimulation.TapeToPrimitive

namespace Examples.TuringSimulation.NormalDispatch

open Turing
open Resources.TuringSimulation.VisitedSpace
open Resources.TuringSimulation.TapeToPrimitive
open Examples.TuringSimulation.VisitedSpace

local instance : Inhabited (Unit → Option Bool) := Pi.instInhabited
local instance : Inhabited PeekControl :=
  ⟨(some (peekTapeProgram (.normal ())), false)⟩

/-- The first primitive of the genuine initialized empty-peek run is the
stationary dispatch to go. Its later left excursion is not included here. -/
theorem empty_peek_dispatch :
    commandAt peekMachine peekStart 0 =
        some (peekGo.q, TM0.Stmt.write peekTape.head) ∧
      cfgAt peekMachine peekStart 1 = some peekGo ∧
      headPosition peekMachine peekStart 0 1 = 0 ∧
      peekGo.Tape = peekStart.Tape := by
  exact normal_control_prefix peekSource () false peekTape 0

local instance : Inhabited (Bool → Option Bool) := Pi.instInhabited

abbrev BranchAlphabet := TM2to1.Γ' Bool (fun _ => Bool)
abbrev BranchTapeControl := TM2to1.Λ' Bool (fun _ => Bool) Unit Bool

def branchTapeProgram : BranchTapeControl →
    TM1.Stmt BranchAlphabet BranchTapeControl Bool :=
  TM2to1.tr StatementCases.branchProgram

abbrev BranchControl := TM1to0.Λ' branchTapeProgram
abbrev BranchCfg := TM0.Cfg BranchAlphabet BranchControl

local instance : Inhabited BranchControl :=
  ⟨(some (branchTapeProgram (.normal ())), false)⟩

def branchMachine : TM0.Machine BranchAlphabet BranchControl :=
  TM1to0.tr branchTapeProgram

def branchTape : Tape BranchAlphabet := Tape.mk' ∅ (TM2to1.addBottom Cases.columns)

/-- A supplied translated normal configuration; v is not a new native default. -/
def branchStart (v : Bool) : BranchCfg :=
  TM1to0.trCfg branchTapeProgram ⟨some (.normal ()), v, branchTape⟩

def branchPush : BranchCfg :=
  TM1to0.trCfg branchTapeProgram
    ⟨some (.go false Cases.pushFalse .halt), true, branchTape⟩

def branchHalt : BranchCfg := ⟨(none, false), branchTape⟩

/-- Loading not false chooses push with register true. Only the stationary
dispatch is counted; neither stack has been modified by this prefix. -/
theorem loaded_true_dispatch :
    commandAt branchMachine (branchStart false) 0 =
        some (branchPush.q, TM0.Stmt.write branchTape.head) ∧
      cfgAt branchMachine (branchStart false) 1 = some branchPush ∧
      headPosition branchMachine (branchStart false) 7 1 = 7 ∧
      branchPush.Tape = branchTape := by
  exact normal_control_prefix StatementCases.branchProgram () false branchTape 7

/-- Loading not true chooses live halt with register false. The native
outer-none observation is the distinct second transition from this supplied start. -/
theorem loaded_false_dispatch :
    commandAt branchMachine (branchStart true) 0 =
        some (branchHalt.q, TM0.Stmt.write branchTape.head) ∧
      cfgAt branchMachine (branchStart true) 1 = some branchHalt ∧
      headPosition branchMachine (branchStart true) 7 1 = 7 ∧
      branchHalt.Tape = branchTape ∧
      cfgAt branchMachine (branchStart true) 2 = none := by
  have h : commandAt branchMachine (branchStart true) 0 =
        some (branchHalt.q, TM0.Stmt.write branchTape.head) ∧
      cfgAt branchMachine (branchStart true) 1 = some branchHalt ∧
      headPosition branchMachine (branchStart true) 7 1 = 7 ∧
      branchHalt.Tape = branchTape :=
    normal_control_prefix StatementCases.branchProgram () true branchTape 7
  have hnone : cfgAt branchMachine (branchStart true) 2 = none := by
    rw [cfgAt_succ, h.2.1]
    rfl
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hnone⟩

end Examples.TuringSimulation.NormalDispatch
