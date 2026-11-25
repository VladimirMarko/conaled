import Applications.Resources.TuringSimulation.VisitedSpace
import Examples.TuringSimulation

/-!
# Actual native trace concatenation

Uncompiled external implementation draft. The fixed calculations are recorded
in EXPECTATIONS.md before this file was written. The generic declarations are
intended for the existing VisitedSpace owner; the connected fixture belongs with
the existing Examples.TuringSimulation.VisitedSpace cases.

The live split premise is the actual native optional iterate. Full commands,
including their next controls, are transported before head coordinates are
composed. No displacement is inferred from equality of endpoint tapes.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.TuringSimulation.VisitedSpace

open Turing

variable {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]

/-- Restarting at an actual live prefix preserves every subsequent complete
optional configuration, including any later outer-none prefix. -/
theorem cfgAt_add_of_live (M : TM0.Machine Γ Q) (start finish : TM0.Cfg Γ Q)
    (n : ℕ) (h : cfgAt M start n = some finish) (k : ℕ) :
    cfgAt M start (n + k) = cfgAt M finish k := by
  induction k with
  | zero => simpa only [Nat.add_zero, cfgAt_zero] using h
  | succ k ih =>
    rw [Nat.add_succ, cfgAt_succ, ih, cfgAt_succ]

/-- The entire actual command is preserved by a live split: next control,
movement or written symbol, and absence of a command. -/
theorem commandAt_add_of_live (M : TM0.Machine Γ Q) (start finish : TM0.Cfg Γ Q)
    (n : ℕ) (h : cfgAt M start n = some finish) (k : ℕ) :
    commandAt M start (n + k) = commandAt M finish k := by
  unfold commandAt
  rw [cfgAt_add_of_live M start finish n h k]

/-- The suffix uses the actual coordinate reached at the live split. This
follows the native command offsets, not an equality of endpoint tapes. -/
theorem headPosition_add_of_live (M : TM0.Machine Γ Q)
    (start finish : TM0.Cfg Γ Q) (origin : ℤ)
    (n : ℕ) (h : cfgAt M start n = some finish) (k : ℕ) :
    headPosition M start origin (n + k) =
      headPosition M finish (headPosition M start origin n) k := by
  induction k with
  | zero => simp only [Nat.add_zero, headPosition_zero]
  | succ k ih =>
    rw [Nat.add_succ, headPosition_succ, ih,
      commandAt_add_of_live M start finish n h k, headPosition_succ]

end Resources.TuringSimulation.VisitedSpace

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
      _ = some ((some peekGotoRet, true), TM0.Stmt.move Dir.right) := rfl
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
