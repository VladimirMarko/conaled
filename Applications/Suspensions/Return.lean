import Applications.Suspensions.Machine
import Mathlib.Tactic.FailIfNoProgress

/-!
# Source-core return classes

This is a control-flow invariant, not value-type preservation. Expressions,
patterns and ordered clauses have different successful/failing result classes.
Raised packets and stuck faults can arise in every class. Explicit frame
input/output classes preserve those distinctions through arbitrary finite
execution, including recursive forcing and ill-typed source expressions.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Return
open Machine

inductive Mode where
  | expression
  | pattern
  | clauses
  deriving DecidableEq

def admitsValue : Mode → Prop
  | .expression | .clauses => True
  | .pattern => False

def admitsBindings : Mode → Prop
  | .pattern => True
  | _ => False

def admitsMismatch : Mode → Prop
  | .pattern | .clauses => True
  | .expression => False

/-- An expression result is also a legitimate selected-clause result. -/
def fits : Mode → Mode → Prop
  | .expression, target => admitsValue target
  | .pattern, target => admitsBindings target ∧ admitsMismatch target
  | .clauses, target => admitsValue target ∧ admitsMismatch target

variable {Primitive : Type}

def frameInput : Frame Primitive → Mode
  | .bindMatch _ _ | .clause _ _ _ _ | .row _ _ _ _ | .layered _ _ => .pattern
  | .applicationResult | .handlerResult _ => .clauses
  | _ => .expression

def frameOutput : Frame Primitive → Mode
  | .memoize _ _ _ | .row _ _ _ _ | .layered _ _ => .pattern
  | .clause _ _ _ _ => .clauses
  | _ => .expression

def expected (stack : List (Frame Primitive)) (outer : Mode) : Mode :=
  match stack with
  | [] => outer
  | frame :: _ => frameInput frame

def stackAllowed : List (Frame Primitive) → Mode → Prop
  | [], _ => True
  | frame :: rest, outer =>
      fits (frameOutput frame) (expected rest outer) ∧ stackAllowed rest outer

@[simp] theorem expected_nil (outer : Mode) : expected ([] : List (Frame Primitive)) outer = outer := rfl

@[simp] theorem expected_cons (frame : Frame Primitive) (rest : List (Frame Primitive))
    (outer : Mode) : expected (frame :: rest) outer = frameInput frame := rfl

@[simp] theorem stackAllowed_nil (outer : Mode) : stackAllowed ([] : List (Frame Primitive)) outer :=
  trivial

@[simp] theorem stackAllowed_cons (frame : Frame Primitive) (rest : List (Frame Primitive))
    (outer : Mode) : stackAllowed (frame :: rest) outer ↔
      fits (frameOutput frame) (expected rest outer) ∧ stackAllowed rest outer := Iff.rfl

def controlAllowed (control : Control Primitive) (mode : Mode) : Prop :=
  match control with
  | .eval _ _ | .value _ | .recursive _ _ _ _ => admitsValue mode
  | .pattern _ _ _ | .rows _ _ _ _ => fits .pattern mode
  | .matched _ => admitsBindings mode
  | .mismatch => admitsMismatch mode
  | .clauses _ _ _ => fits .clauses mode
  | .raised _ => True

def configAllowed (config : Config Primitive) (outer : Mode) : Prop :=
  stackAllowed config.stack outer ∧ controlAllowed config.control (expected config.stack outer)

def resultAllowed (result : Result Primitive) (mode : Mode) : Prop :=
  match result with
  | .value _ => admitsValue mode
  | .matched _ => admitsBindings mode
  | .mismatch => admitsMismatch mode
  | .raised _ | .stuck _ => True

def nextAllowed (result : Answer Primitive ⊕ Config Primitive) (outer : Mode) : Prop :=
  match result with
  | .inl answer => resultAllowed answer.result outer
  | .inr next => configAllowed next outer

attribute [local simp] admitsValue admitsBindings admitsMismatch fits frameInput frameOutput
  controlAllowed configAllowed resultAllowed nextAllowed proceed finish

private theorem eval_allowed (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (expression : Expr Primitive) (stack : List (Frame Primitive))
    (outer : Mode) (valid : configAllowed ⟨memory, .eval environment expression, stack⟩ outer) :
    nextAllowed (step parameters ⟨memory, .eval environment expression, stack⟩) outer := by
  cases expression <;>
    simp only [step, transition]
  all_goals
    repeat' first
      | (fail_if_no_progress simp_all)
      | split at *

private theorem value_allowed (parameters : Parameters Primitive) (memory : Memory Primitive)
    (value : Value Primitive) (stack : List (Frame Primitive)) (outer : Mode)
    (valid : configAllowed ⟨memory, .value value, stack⟩ outer) :
    nextAllowed (step parameters ⟨memory, .value value, stack⟩) outer := by
  cases stack with
  | nil => exact valid.2
  | cons frame rest =>
      cases frame <;>
        simp only [step, transition]
      all_goals
        repeat' first
          | (fail_if_no_progress simp_all)
          | split at *

private theorem raised_allowed (parameters : Parameters Primitive) (memory : Memory Primitive)
    (packet : Value Primitive) (stack : List (Frame Primitive)) (outer : Mode)
    (valid : configAllowed ⟨memory, .raised packet, stack⟩ outer) :
    nextAllowed (step parameters ⟨memory, .raised packet, stack⟩) outer := by
  cases stack with
  | nil => trivial
  | cons frame rest =>
      cases frame <;>
        simp_all [step, transition]

private theorem pattern_allowed (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (pattern : Pattern) (value : Value Primitive)
    (stack : List (Frame Primitive)) (outer : Mode)
    (valid : configAllowed ⟨memory, .pattern environment pattern value, stack⟩ outer) :
    nextAllowed (step parameters ⟨memory, .pattern environment pattern value, stack⟩) outer := by
  cases pattern <;>
    simp only [step, transition]
  all_goals
    repeat' first
      | (fail_if_no_progress simp_all)
      | split at *

private theorem matched_allowed (parameters : Parameters Primitive) (memory : Memory Primitive)
    (bindings : Env Primitive) (stack : List (Frame Primitive)) (outer : Mode)
    (valid : configAllowed ⟨memory, .matched bindings, stack⟩ outer) :
    nextAllowed (step parameters ⟨memory, .matched bindings, stack⟩) outer := by
  cases stack with
  | nil => exact valid.2
  | cons frame rest =>
      cases frame <;>
        simp_all [step, transition]

private theorem mismatch_allowed (parameters : Parameters Primitive) (memory : Memory Primitive)
    (stack : List (Frame Primitive)) (outer : Mode)
    (valid : configAllowed ⟨memory, .mismatch, stack⟩ outer) :
    nextAllowed (step parameters ⟨memory, .mismatch, stack⟩) outer := by
  cases stack with
  | nil => exact valid.2
  | cons frame rest =>
      cases frame <;>
        simp_all [step, transition]

private theorem clauses_allowed (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (alternatives : List (Pattern × Expr Primitive))
    (value : Value Primitive) (stack : List (Frame Primitive)) (outer : Mode)
    (valid : configAllowed ⟨memory, .clauses environment alternatives value, stack⟩ outer) :
    nextAllowed (step parameters ⟨memory, .clauses environment alternatives value, stack⟩) outer := by
  cases alternatives <;>
    simp_all [step, transition]

private theorem rows_allowed (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (patterns : List (Nat × Pattern))
    (fields : List (Nat × Value Primitive)) (bindings : Env Primitive)
    (stack : List (Frame Primitive)) (outer : Mode)
    (valid : configAllowed ⟨memory, .rows environment patterns fields bindings, stack⟩ outer) :
    nextAllowed (step parameters ⟨memory, .rows environment patterns fields bindings, stack⟩) outer := by
  cases patterns <;>
    simp only [step, transition]
  all_goals
    repeat' first
      | (fail_if_no_progress simp_all)
      | split at *

private theorem recursive_allowed (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (bindings : List (Nat × Expr Primitive))
    (created : Env Primitive) (body : Expr Primitive) (stack : List (Frame Primitive)) (outer : Mode)
    (valid : configAllowed ⟨memory, .recursive environment bindings created body, stack⟩ outer) :
    nextAllowed (step parameters ⟨memory, .recursive environment bindings created body, stack⟩) outer := by
  cases bindings <;>
    simp only [step, transition]
  all_goals
    repeat' first
      | (fail_if_no_progress simp_all)
      | split at *

theorem step_allowed (parameters : Parameters Primitive) (config : Config Primitive)
    (outer : Mode) (valid : configAllowed config outer) :
    nextAllowed (step parameters config) outer := by
  rcases config with ⟨memory, control, stack⟩
  cases control with
  | eval environment expression => exact eval_allowed parameters memory environment expression stack outer valid
  | value value => exact value_allowed parameters memory value stack outer valid
  | raised packet => exact raised_allowed parameters memory packet stack outer valid
  | pattern environment pattern value =>
      exact pattern_allowed parameters memory environment pattern value stack outer valid
  | matched bindings => exact matched_allowed parameters memory bindings stack outer valid
  | mismatch => exact mismatch_allowed parameters memory stack outer valid
  | clauses environment alternatives value =>
      exact clauses_allowed parameters memory environment alternatives value stack outer valid
  | rows environment patterns fields bindings =>
      exact rows_allowed parameters memory environment patterns fields bindings stack outer valid
  | recursive environment bindings created body =>
      exact recursive_allowed parameters memory environment bindings created body stack outer valid

theorem evaluates_allowed {parameters : Parameters Primitive} {config : Config Primitive}
    {answer : Answer Primitive} {steps : Nat}
    (evaluation : Progress.Evaluates (step parameters) config answer steps)
    (outer : Mode) (valid : configAllowed config outer) : resultAllowed answer.result outer := by
  induction evaluation with
  | done finished => simpa only [finished, nextAllowed] using step_allowed parameters _ outer valid
  | next moved _ ih =>
      apply ih
      simpa only [moved, nextAllowed] using step_allowed parameters _ outer valid

theorem expression_result {parameters : Parameters Primitive} {memory : Memory Primitive}
    {environment : Env Primitive} {expression : Expr Primitive} {answer : Answer Primitive}
    {steps : Nat}
    (evaluation : Progress.Evaluates (step parameters) (start memory environment expression)
      answer steps) : resultAllowed answer.result .expression :=
  evaluates_allowed evaluation .expression ⟨trivial, trivial⟩

theorem pattern_result {parameters : Parameters Primitive} {memory : Memory Primitive}
    {environment : Env Primitive} {pattern : Pattern} {value : Value Primitive}
    {answer : Answer Primitive} {steps : Nat}
    (evaluation : Progress.Evaluates (step parameters)
      (startPattern memory environment pattern value) answer steps) :
    resultAllowed answer.result .pattern :=
  evaluates_allowed evaluation .pattern ⟨trivial, ⟨trivial, trivial⟩⟩

end Suspensions.Core.Return
