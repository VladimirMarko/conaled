import Applications.Suspensions.Machine
import Mathlib.Tactic.FailIfNoProgress

/-!
# Finite evaluation inside an appended continuation

The existing machine returns a value, exception, matched environment or mismatch
only when its own frame stack is empty. Appending a caller's frames preserves
every earlier transition; those frames begin processing the terminal control
instead of performing the isolated run's final delivery step. Stuck outcomes
remain stuck and cannot be recovered by appending frames.

These laws use `Progress.Evaluates` directly. No termination or type-safety
assumption is added to arbitrary configurations. The converse assumes only a
given finite plugged run whose final result is not stuck.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Machine
variable {Primitive : Type}

def boundaryControl : Result Primitive → Option (Control Primitive)
  | .value result => some (.value result)
  | .raised packet => some (.raised packet)
  | .matched bindings => some (.matched bindings)
  | .mismatch => some .mismatch
  | .stuck _ => none

def appendFrames (config : Config Primitive) (tail : List (Frame Primitive)) :
    Config Primitive := { config with stack := config.stack ++ tail }

@[simp] theorem appendFrames_nil (config : Config Primitive) : appendFrames config [] = config := by
  cases config
  simp [appendFrames]

theorem appendFrames_append (config : Config Primitive) (first second : List (Frame Primitive)) :
    appendFrames (appendFrames config first) second = appendFrames config (first ++ second) := by
  cases config
  simp [appendFrames, List.append_assoc]

/-- A single structural classification supplies all three public frame laws.
Only the existing stack prefix is inspected by a nonterminal transition. -/
private theorem step_classifies (parameters : Parameters Primitive) (config : Config Primitive)
    (tail : List (Frame Primitive)) :
    match step parameters config with
    | .inr next => step parameters (appendFrames config tail) = .inr (appendFrames next tail)
    | .inl answer => match boundaryControl answer.result with
        | some control => config = ⟨answer.memory, control, []⟩
        | none => step parameters (appendFrames config tail) = .inl answer := by
  rcases config with ⟨memory, control, stack⟩
  cases control <;>
    simp only [step, transition, appendFrames, continue, finish, boundaryControl]
  all_goals
    repeat' first
      | (fail_if_no_progress simp_all [appendFrames, continue, finish, boundaryControl])
      | split at *

theorem step_append {parameters : Parameters Primitive} {config next : Config Primitive}
    (moved : step parameters config = .inr next) (tail : List (Frame Primitive)) :
    step parameters (appendFrames config tail) = .inr (appendFrames next tail) := by
  simpa only [moved] using step_classifies parameters config tail

/-- A delivered non-stuck result is exactly its corresponding terminal
control at an empty stack, with the same current memory. -/
theorem step_boundary {parameters : Parameters Primitive} {config : Config Primitive}
    {answer : Answer Primitive} {control : Control Primitive}
    (finished : step parameters config = .inl answer)
    (boundary : boundaryControl answer.result = some control) :
    config = ⟨answer.memory, control, []⟩ := by
  simpa only [finished, boundary] using step_classifies parameters config []

/-- Stuck is a machine fault, not a raised source exception that a newly
appended handler might catch. Its entire answer is unchanged. -/
theorem step_stuck_append {parameters : Parameters Primitive} {config : Config Primitive}
    {answer : Answer Primitive} (finished : step parameters config = .inl answer)
    (stuck : boundaryControl answer.result = none) (tail : List (Frame Primitive)) :
    step parameters (appendFrames config tail) = .inl answer := by
  simpa only [finished, stuck] using step_classifies parameters config tail

private theorem evaluates_positive {parameters : Parameters Primitive} {config : Config Primitive}
    {answer : Answer Primitive} {steps : Nat}
    (evaluation : Progress.Evaluates (step parameters) config answer steps) : 0 < steps := by
  cases evaluation <;> omega

/-- The isolated run's final delivery is replaced by the residual run from
the same terminal control. This explains the subtraction of exactly one step. -/
theorem evaluates_append {parameters : Parameters Primitive} {config : Config Primitive}
    {bodyAnswer answer : Answer Primitive} {control : Control Primitive} {n m : Nat}
    (body : Progress.Evaluates (step parameters) config bodyAnswer n)
    (boundary : boundaryControl bodyAnswer.result = some control)
    (tail : List (Frame Primitive))
    (residual : Progress.Evaluates (step parameters) ⟨bodyAnswer.memory, control, tail⟩ answer m) :
    Progress.Evaluates (step parameters) (appendFrames config tail) answer ((n - 1) + m) := by
  induction body with
  | done finished =>
      have shape := step_boundary finished boundary
      simpa only [shape, appendFrames, List.nil_append, Nat.sub_self, Nat.zero_add] using residual
  | @next input next output steps moved body ih =>
      have positive := evaluates_positive body
      have count : ((steps - 1) + m) + 1 = ((steps + 1) - 1) + m := by omega
      simpa only [count] using
        Progress.Evaluates.next (step_append moved tail) (ih boundary residual)

/-- Every finite plugged run to a non-stuck answer splits at the original
machine's first delivered boundary. No global safety premise is needed: a
stuck original step would force the plugged run to have the same stuck result. -/
theorem evaluates_split {parameters : Parameters Primitive} {config : Config Primitive}
    {tail : List (Frame Primitive)} {answer : Answer Primitive} {steps : Nat}
    (whole : Progress.Evaluates (step parameters) (appendFrames config tail) answer steps)
    {finalControl : Control Primitive} (finalBoundary : boundaryControl answer.result = some finalControl) :
    ∃ bodyAnswer control n m,
      Progress.Evaluates (step parameters) config bodyAnswer n ∧
      boundaryControl bodyAnswer.result = some control ∧
      Progress.Evaluates (step parameters) ⟨bodyAnswer.memory, control, tail⟩ answer m ∧
      steps = (n - 1) + m := by
  induction steps using Nat.strong_induction_on generalizing config with
  | h steps ih =>
      cases first : step parameters config with
      | inl bodyAnswer =>
          cases boundary : boundaryControl bodyAnswer.result with
          | some control =>
              have shape := step_boundary first boundary
              refine ⟨bodyAnswer, control, 1, steps, .done first, boundary, ?_, by simp⟩
              simpa only [shape, appendFrames, List.nil_append] using whole
          | none =>
              have finished := step_stuck_append first boundary tail
              have equal := (Progress.Evaluates.done finished).unique whole
              have resultEq := congrArg (fun result : Answer Primitive => boundaryControl result.result)
                equal.1
              rw [boundary, finalBoundary] at resultEq
              cases resultEq
      | inr next =>
          have moved := step_append first tail
          cases whole with
          | done finished => simp [moved] at finished
          | @next _ actual _ remaining actualMoved rest =>
              have equal : appendFrames next tail = actual :=
                Sum.inr.inj (moved.symm.trans actualMoved)
              subst actual
              obtain ⟨bodyAnswer, control, n, m, body, boundary, residual, count⟩ :=
                ih remaining (by omega) rest
              refine ⟨bodyAnswer, control, n + 1, m, .next first body, boundary, residual, ?_⟩
              have positive := evaluates_positive body
              omega

/-- A connected continuation client: a finite value-producing body is followed
by an actual cache write and wildcard match. Its final state is the body's
state updated at the cache address; earlier body effects remain present. -/
theorem memoize_wildcard_after_body {parameters : Parameters Primitive} {config : Config Primitive}
    {memory : Memory Primitive} {value : Value Primitive} {n : Nat}
    (body : Progress.Evaluates (step parameters) config ⟨memory, .value value⟩ n)
    (address : Nat) (environment : Env Primitive) :
    Progress.Evaluates (step parameters)
      (appendFrames config [.memoize address environment .wildcard])
      ⟨Suspensions.memoize memory address value, .matched []⟩ (n + 2) := by
  have residual : Progress.Evaluates (step parameters)
      ⟨memory, .value value, [.memoize address environment .wildcard]⟩
      ⟨Suspensions.memoize memory address value, .matched []⟩ 3 :=
    .next rfl (.next rfl (.done rfl))
  have composed := evaluates_append body rfl [.memoize address environment .wildcard] residual
  have positive := evaluates_positive body
  have count : (n - 1) + 3 = n + 2 := by omega
  simpa only [count] using composed

end Suspensions.Core.Machine
