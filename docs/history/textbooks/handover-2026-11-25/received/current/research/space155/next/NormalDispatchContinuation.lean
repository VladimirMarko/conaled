import Applications.Resources.TuringSimulation.TapeToPrimitive
import Applications.Resources.TuringSimulation.VisitedSpace
import Examples.TuringSimulation

/-!
# Continue after the actual stationary normal dispatch

Uncompiled external continuation draft. This file needs the new trace
concatenation lemmas and NormalDispatch declarations to be available in the
imported owners or in a separately assembled root-owned check copy. They are
not exports of the unchanged recovery154 source. No alternate theorem bodies
or assumed simulation interface are provided here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.TuringSimulation.TapeToPrimitive

open Turing
open Resources.TuringSimulation.VisitedSpace

variable {K : Type*} {Δ : K → Type*} {L R : Type*}
variable [DecidableEq K] [Inhabited L] [Inhabited R]

/-- Split the actual normal control's run after its one stationary native
dispatch. Both suffix configurations and complete commands agree, and the
suffix uses the original global origin because the first command self-writes. -/
theorem normal_control_resume (M : L → TM2.Stmt Δ L R) (l : L) (v : R)
    (T : Tape (TM2to1.Γ' K Δ)) (origin : ℤ) (k : ℕ) :
    let P := TM2to1.tr M
    let start := TM1to0.trCfg P
      (⟨some (TM2to1.Λ'.normal l), v, T⟩ :
        TM1.Cfg (TM2to1.Γ' K Δ) (TM2to1.Λ' K Δ L R) R)
    let finish := TM1to0.trCfg P (TM1.stepAux (TM2to1.trNormal (M l)) v T)
    cfgAt (TM1to0.tr P) start (1 + k) = cfgAt (TM1to0.tr P) finish k ∧
      commandAt (TM1to0.tr P) start (1 + k) = commandAt (TM1to0.tr P) finish k ∧
      headPosition (TM1to0.tr P) start origin (1 + k) =
        headPosition (TM1to0.tr P) finish origin k := by
  let P := TM2to1.tr M
  let start := TM1to0.trCfg P
    (⟨some (TM2to1.Λ'.normal l), v, T⟩ :
      TM1.Cfg (TM2to1.Γ' K Δ) (TM2to1.Λ' K Δ L R) R)
  let finish := TM1to0.trCfg P (TM1.stepAux (TM2to1.trNormal (M l)) v T)
  have hprefix := normal_control_prefix M l v T origin
  have hcfg : cfgAt (TM1to0.tr P) start 1 = some finish := hprefix.2.1
  have hpos : headPosition (TM1to0.tr P) start origin 1 = origin := hprefix.2.2.1
  exact ⟨cfgAt_add_of_live (TM1to0.tr P) start finish 1 hcfg k,
    commandAt_add_of_live (TM1to0.tr P) start finish 1 hcfg k,
    (headPosition_add_of_live (TM1to0.tr P) start finish origin 1 hcfg k).trans
      (congrArg (fun p : ℤ => headPosition (TM1to0.tr P) finish p k) hpos)⟩

end Resources.TuringSimulation.TapeToPrimitive

namespace Examples.TuringSimulation.NormalDispatch

open Turing
open Resources.TuringSimulation.VisitedSpace
open Resources.TuringSimulation.TapeToPrimitive
open Examples.TuringSimulation.VisitedSpace

local instance : Inhabited (Unit → Option Bool) := Pi.instInhabited
local instance : Inhabited PeekControl :=
  ⟨(some (peekTapeProgram (.normal ())), false)⟩

/-- The genuine initialized empty peek splits after dispatch to its actual
go control. Its first suffix move is the retained negative-coordinate visit. -/
theorem empty_peek_resume :
    (∀ k : ℕ,
      cfgAt peekMachine peekStart (1 + k) = cfgAt peekMachine peekGo k ∧
        commandAt peekMachine peekStart (1 + k) = commandAt peekMachine peekGo k ∧
        headPosition peekMachine peekStart 0 (1 + k) =
          headPosition peekMachine peekGo 0 k) ∧
      headPosition peekMachine peekStart 0 2 = -1 := by
  have hcat (k : ℕ) :
      cfgAt peekMachine peekStart (1 + k) = cfgAt peekMachine peekGo k ∧
        commandAt peekMachine peekStart (1 + k) = commandAt peekMachine peekGo k ∧
        headPosition peekMachine peekStart 0 (1 + k) =
          headPosition peekMachine peekGo 0 k :=
    normal_control_resume peekSource () false peekTape 0 k
  have hleft : headPosition peekMachine peekGo 0 1 = -1 := by decide
  exact ⟨hcat, ((hcat 1).2.2).trans hleft⟩

end Examples.TuringSimulation.NormalDispatch
