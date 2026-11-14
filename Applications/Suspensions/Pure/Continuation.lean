import Applications.Suspensions.Pure.Machine
import Mathlib.Tactic.FailIfNoProgress

/-!
# Continuations in the unshared suspension interpretation

The pure machine inspects its current stack prefix until it delivers a result.
Appending caller frames preserves those earlier transitions. A normal, raised,
matched or mismatch result supplies a boundary for the caller; a machine fault
remains terminal and cannot be caught by an appended source handler.

These are source-specific laws over the existing `Progress.Evaluates` judgment.
The all-outcome split requires no typing, effect restriction or termination
premise beyond the particular finite plugged run being decomposed.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Machine
variable {Primitive : Type}

def boundaryControl : Result Primitive → Option (Control Primitive)
  | .value result => some (.value result)
  | .raised packet => some (.raised packet)
  | .matched bindings => some (.matched bindings)
  | .mismatch => some .mismatch
  | .stuck _ => none

def appendFrames (config : Config Primitive) (tail : List (Frame Primitive)) :
    Config Primitive := {config with stack := config.stack ++ tail}

@[simp] theorem appendFrames_nil (config : Config Primitive) : appendFrames config [] = config := by
  cases config
  simp [appendFrames]

theorem appendFrames_append (config : Config Primitive) (first second : List (Frame Primitive)) :
    appendFrames (appendFrames config first) second = appendFrames config (first ++ second) := by
  cases config
  simp [appendFrames, List.append_assoc]

private def ClassifiesStep (parameters : Parameters Primitive) (config : Config Primitive)
    (tail : List (Frame Primitive)) : Prop :=
    match step parameters config with
    | .inr next => step parameters (appendFrames config tail) = .inr (appendFrames next tail)
    | .inl answer => match boundaryControl answer with
        | some control => config = ⟨control, []⟩
        | none => step parameters (appendFrames config tail) = .inl answer

private theorem eval_classifies (parameters : Parameters Primitive)
    (environment : Env Primitive) (expression : Core.Expr Primitive)
    (stack tail : List (Frame Primitive)) :
    ClassifiesStep parameters ⟨.eval environment expression, stack⟩ tail := by
  cases expression <;>
    simp only [ClassifiesStep, step, transition, appendFrames, proceed, finish, boundaryControl]
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all)
      | split at *

private theorem value_classifies (parameters : Parameters Primitive) (value : Value Primitive)
    (stack tail : List (Frame Primitive)) :
    ClassifiesStep parameters ⟨.value value, stack⟩ tail := by
  cases stack with
  | nil => rfl
  | cons frame rest =>
      cases frame <;>
        simp only [ClassifiesStep, step, transition, appendFrames, proceed, finish, boundaryControl]
      all_goals
        repeat' first
          | (fail_if_no_progress subst_vars)
          | (fail_if_no_progress simp_all)
          | split at *

private theorem raised_classifies (parameters : Parameters Primitive) (packet : Value Primitive)
    (stack tail : List (Frame Primitive)) :
    ClassifiesStep parameters ⟨.raised packet, stack⟩ tail := by
  cases stack with
  | nil => rfl
  | cons frame rest => cases frame <;> rfl

private theorem pattern_classifies (parameters : Parameters Primitive)
    (environment : Env Primitive) (pattern : Core.Pattern) (value : Value Primitive)
    (stack tail : List (Frame Primitive)) :
    ClassifiesStep parameters ⟨.pattern environment pattern value, stack⟩ tail := by
  cases pattern <;>
    simp only [ClassifiesStep, step, transition, appendFrames, proceed, finish, boundaryControl]
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all)
      | split at *

private theorem matched_classifies (parameters : Parameters Primitive) (bindings : Env Primitive)
    (stack tail : List (Frame Primitive)) :
    ClassifiesStep parameters ⟨.matched bindings, stack⟩ tail := by
  cases stack with
  | nil => rfl
  | cons frame rest => cases frame <;> rfl

private theorem mismatch_classifies (parameters : Parameters Primitive)
    (stack tail : List (Frame Primitive)) :
    ClassifiesStep parameters ⟨.mismatch, stack⟩ tail := by
  cases stack with
  | nil => rfl
  | cons frame rest => cases frame <;> rfl

private theorem clauses_classifies (parameters : Parameters Primitive)
    (environment : Env Primitive) (clauses : List (Core.Pattern × Core.Expr Primitive))
    (value : Value Primitive) (stack tail : List (Frame Primitive)) :
    ClassifiesStep parameters ⟨.clauses environment clauses value, stack⟩ tail := by
  cases clauses with
  | nil => rfl
  | cons clause rest => cases clause; rfl

private theorem rows_classifies (parameters : Parameters Primitive)
    (environment : Env Primitive) (patterns : List (Nat × Core.Pattern))
    (fields : List (Nat × Value Primitive)) (bindings : Env Primitive)
    (stack tail : List (Frame Primitive)) :
    ClassifiesStep parameters ⟨.rows environment patterns fields bindings, stack⟩ tail := by
  cases patterns with
  | nil => rfl
  | cons row rest =>
      rcases row with ⟨label, pattern⟩
      simp only [ClassifiesStep, step, transition, appendFrames, proceed, finish, boundaryControl]
      repeat' first
        | (fail_if_no_progress subst_vars)
        | (fail_if_no_progress simp_all)
        | split at *

private theorem step_classifies (parameters : Parameters Primitive) (config : Config Primitive)
    (tail : List (Frame Primitive)) : ClassifiesStep parameters config tail := by
  rcases config with ⟨control, stack⟩
  cases control with
  | eval environment expression => exact eval_classifies parameters environment expression stack tail
  | value value => exact value_classifies parameters value stack tail
  | raised packet => exact raised_classifies parameters packet stack tail
  | pattern environment pattern value =>
      exact pattern_classifies parameters environment pattern value stack tail
  | matched bindings => exact matched_classifies parameters bindings stack tail
  | mismatch => exact mismatch_classifies parameters stack tail
  | clauses environment clauses value =>
      exact clauses_classifies parameters environment clauses value stack tail
  | rows environment patterns fields bindings =>
      exact rows_classifies parameters environment patterns fields bindings stack tail

theorem step_append {parameters : Parameters Primitive} {config next : Config Primitive}
    (moved : step parameters config = .inr next) (tail : List (Frame Primitive)) :
    step parameters (appendFrames config tail) = .inr (appendFrames next tail) := by
  simpa only [ClassifiesStep, moved] using step_classifies parameters config tail

theorem step_boundary {parameters : Parameters Primitive} {config : Config Primitive}
    {answer : Result Primitive} {control : Control Primitive}
    (finished : step parameters config = .inl answer)
    (boundary : boundaryControl answer = some control) : config = ⟨control, []⟩ := by
  simpa only [ClassifiesStep, finished, boundary] using step_classifies parameters config []

theorem step_stuck_append {parameters : Parameters Primitive} {config : Config Primitive}
    {answer : Result Primitive} (finished : step parameters config = .inl answer)
    (stuck : boundaryControl answer = none) (tail : List (Frame Primitive)) :
    step parameters (appendFrames config tail) = .inl answer := by
  simpa only [ClassifiesStep, finished, stuck] using step_classifies parameters config tail

/-- The caller replaces exactly the isolated run's last delivery transition. -/
theorem evaluates_append {parameters : Parameters Primitive} {config : Config Primitive}
    {bodyAnswer answer : Result Primitive} {control : Control Primitive} {n m : Nat}
    (body : Progress.Evaluates (step parameters) config bodyAnswer n)
    (boundary : boundaryControl bodyAnswer = some control) (tail : List (Frame Primitive))
    (residual : Progress.Evaluates (step parameters) ⟨control, tail⟩ answer m) :
    Progress.Evaluates (step parameters) (appendFrames config tail) answer ((n - 1) + m) := by
  induction body with
  | done finished =>
      have shape := step_boundary finished boundary
      simpa only [shape, appendFrames, List.nil_append, Nat.sub_self, Nat.zero_add] using residual
  | @next input next output steps moved body ih =>
      have positive := evaluates_positive body
      have count : ((steps - 1) + m) + 1 = ((steps + 1) - 1) + m := by omega
      simpa only [count] using
        Progress.Evaluates.next (step_append moved tail) (ih boundary)

/-- A source handler cannot recover a machine fault in the isolated body. -/
theorem evaluates_stuck_append {parameters : Parameters Primitive} {config : Config Primitive}
    {answer : Result Primitive} {steps : Nat}
    (body : Progress.Evaluates (step parameters) config answer steps)
    (stuck : boundaryControl answer = none) (tail : List (Frame Primitive)) :
    Progress.Evaluates (step parameters) (appendFrames config tail) answer steps := by
  induction body with
  | done finished => exact .done (step_stuck_append finished stuck tail)
  | next moved _ ih => exact .next (step_append moved tail) (ih stuck)

/-- An isolated fault and a later caller fault occupy different alternatives.
The result of the complete run is unrestricted in this decomposition. -/
theorem evaluates_split_all {parameters : Parameters Primitive} {config : Config Primitive}
    {tail : List (Frame Primitive)} {answer : Result Primitive} {steps : Nat}
    (whole : Progress.Evaluates (step parameters) (appendFrames config tail) answer steps) :
    (Progress.Evaluates (step parameters) config answer steps ∧ boundaryControl answer = none) ∨
    ∃ bodyAnswer control n m,
      Progress.Evaluates (step parameters) config bodyAnswer n ∧
      boundaryControl bodyAnswer = some control ∧
      Progress.Evaluates (step parameters) ⟨control, tail⟩ answer m ∧
      steps = (n - 1) + m := by
  induction steps using Nat.strong_induction_on generalizing config with
  | h steps ih =>
      cases first : step parameters config with
      | inl bodyAnswer =>
          cases boundary : boundaryControl bodyAnswer with
          | some control =>
              have shape := step_boundary first boundary
              refine .inr ⟨bodyAnswer, control, 1, steps, .done first, boundary, ?_, by simp⟩
              simpa only [shape, appendFrames, List.nil_append] using whole
          | none =>
              have finished := step_stuck_append first boundary tail
              have same := (Progress.Evaluates.done finished).unique whole
              refine .inl ⟨?_, ?_⟩
              · rw [← same.1, ← same.2]
                exact .done first
              · simpa only [← same.1] using boundary
      | inr next =>
          have moved := step_append first tail
          cases whole with
          | done finished => simp [moved] at finished
          | @next _ actual _ remaining actualMoved rest =>
              have same : appendFrames next tail = actual := Sum.inr.inj (moved.symm.trans actualMoved)
              subst actual
              rcases ih remaining (by omega) rest with ⟨body, stuck⟩ |
                ⟨bodyAnswer, control, n, m, body, boundary, residual, count⟩
              · exact .inl ⟨.next first body, stuck⟩
              · refine .inr ⟨bodyAnswer, control, n + 1, m, .next first body,
                  boundary, residual, ?_⟩
                have positive := evaluates_positive body
                omega

/-- A finite caller run always contains an isolated finite body run, of no
greater transition count. This includes both fault alternatives. -/
theorem evaluates_isolated_le {parameters : Parameters Primitive} {config : Config Primitive}
    {tail : List (Frame Primitive)} {answer : Result Primitive} {steps : Nat}
    (whole : Progress.Evaluates (step parameters) (appendFrames config tail) answer steps) :
    ∃ bodyAnswer n, Progress.Evaluates (step parameters) config bodyAnswer n ∧ n ≤ steps := by
  rcases evaluates_split_all whole with ⟨body, _⟩ |
    ⟨bodyAnswer, control, n, m, body, _, residual, count⟩
  · exact ⟨answer, steps, body, Nat.le_refl _⟩
  · have bodyPositive := evaluates_positive body
    have residualPositive := evaluates_positive residual
    exact ⟨bodyAnswer, n, body, by omega⟩

theorem terminates_of_append {parameters : Parameters Primitive} {config : Config Primitive}
    {tail : List (Frame Primitive)}
    (whole : Progress.Terminates (step parameters) (appendFrames config tail)) :
    Progress.Terminates (step parameters) config := by
  obtain ⟨answer, steps, evaluated⟩ := whole
  obtain ⟨bodyAnswer, n, body, _⟩ := evaluates_isolated_le evaluated
  exact ⟨bodyAnswer, n, body⟩

theorem not_terminates_append {parameters : Parameters Primitive} {config : Config Primitive}
    (body : ¬ Progress.Terminates (step parameters) config) (tail : List (Frame Primitive)) :
    ¬ Progress.Terminates (step parameters) (appendFrames config tail) :=
  fun whole => body (terminates_of_append whole)

/-- A value-producing body returns to the caller's wildcard match, without
memoization. The two additional transitions are return-to-pattern and match. -/
theorem force_wildcard_after_body {parameters : Parameters Primitive} {config : Config Primitive}
    {value : Value Primitive} {n : Nat}
    (body : Progress.Evaluates (step parameters) config (.value value) n)
    (environment : Env Primitive) :
    Progress.Evaluates (step parameters)
      (appendFrames config [.force environment .wildcard]) (.matched []) (n + 2) := by
  have residual : Progress.Evaluates (step parameters)
      ⟨.value value, [.force environment .wildcard]⟩ (.matched []) 3 :=
    .next rfl (.next rfl (.done rfl))
  have composed := evaluates_append body rfl [.force environment .wildcard] residual
  have positive := evaluates_positive body
  have count : (n - 1) + 3 = n + 2 := by omega
  simpa only [count] using composed

end Suspensions.Pure.Machine
