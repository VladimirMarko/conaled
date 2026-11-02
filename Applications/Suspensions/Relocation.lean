import Applications.Suspensions.Renaming
import Mathlib.Tactic.FailIfNoProgress

/-!
# Execution with one private allocation

The address injection fixes the old heap and leaves a hole for one private
cell. Primitive equivariance is an explicit additional law. The source machine
and its operations are unchanged. Related executions retain old/new aliases,
reference effects, exception names and recursive captures.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Relocation
open Machine Renaming

variable {Primitive : Type}

def fault (rename : Nat → Nat) : Fault → Fault
  | .missingAddress address => .missingAddress (rename address)
  | other => other

def primitiveResult (rename : Nat → Nat) : PrimitiveResult Primitive → PrimitiveResult Primitive
  | .value v => .value (value rename v)
  | .raised packet => .raised (value rename packet)
  | .stuck reason => .stuck (fault rename reason)

/-- An operation law, independent of its implementation or typing signature. -/
def Equivariant (parameters : Parameters Primitive) (rename : Nat → Nat) : Prop :=
  ∀ operation v, parameters.primitive operation (value rename v) =
    primitiveResult rename (parameters.primitive operation v)

def result (rename : Nat → Nat) : Result Primitive → Result Primitive
  | .value v => .value (value rename v)
  | .raised packet => .raised (value rename packet)
  | .matched bindings => .matched (environment rename bindings)
  | .mismatch => .mismatch
  | .stuck reason => .stuck (fault rename reason)

def control (rename : Nat → Nat) : Control Primitive → Control Primitive
  | .eval env expression => .eval (environment rename env) expression
  | .value v => .value (value rename v)
  | .raised packet => .raised (value rename packet)
  | .pattern env pattern v => .pattern (environment rename env) pattern (value rename v)
  | .matched bindings => .matched (environment rename bindings)
  | .mismatch => .mismatch
  | .clauses env alternatives v => .clauses (environment rename env) alternatives (value rename v)
  | .rows env patterns fields bindings =>
      .rows (environment rename env) patterns (environment rename fields) (environment rename bindings)
  | .recursive env bindings created body =>
      .recursive (environment rename env) bindings (environment rename created) body

def frame (rename : Nat → Nat) : Frame Primitive → Frame Primitive
  | .constructor tag => .constructor tag
  | .record env label remaining done =>
      .record (environment rename env) label remaining (environment rename done)
  | .function env argument => .function (environment rename env) argument
  | .argument function => .argument (value rename function)
  | .bindValue env pattern body => .bindValue (environment rename env) pattern body
  | .bindMatch env body => .bindMatch (environment rename env) body
  | .branch env yes no => .branch (environment rename env) yes no
  | .reference => .reference
  | .read => .read
  | .assignReference env expression => .assignReference (environment rename env) expression
  | .assignValue reference => .assignValue (value rename reference)
  | .raise => .raise
  | .handler env alternatives => .handler (environment rename env) alternatives
  | .handlerResult original => .handlerResult (value rename original)
  | .applicationResult => .applicationResult
  | .clause env body remaining v => .clause (environment rename env) body remaining (value rename v)
  | .memoize address env inner => .memoize (rename address) (environment rename env) inner
  | .row env remaining fields earlier =>
      .row (environment rename env) remaining (environment rename fields) (environment rename earlier)
  | .layered name v => .layered name (value rename v)
  | .recursive env name remaining created body =>
      .recursive (environment rename env) name remaining (environment rename created) body

def event (rename : Nat → Nat) : Event → Event
  | .core => .core
  | .allocate address => .allocate (rename address)
  | .body address => .body (rename address)
  | .hit address => .hit (rename address)
  | .cacheWrite address => .cacheWrite (rename address)
  | .referenceRead address => .referenceRead (rename address)
  | .referenceWrite address => .referenceWrite (rename address)
  | .freshException name => .freshException name

/-- The fixed private address precedes all future allocations on the left. -/
def StatesRelated (frontier : Nat) (before after : Memory Primitive) : Prop :=
  MemoryRel (shift frontier) before after ∧ frontier ≤ before.next

def AnswersRelated (frontier : Nat) (before after : Answer Primitive) : Prop :=
  StatesRelated frontier before.memory after.memory ∧
    after.result = result (shift frontier) before.result

def ConfigsRelated (frontier : Nat) (before after : Config Primitive) : Prop :=
  StatesRelated frontier before.memory after.memory ∧
    after.control = control (shift frontier) before.control ∧
      after.stack = before.stack.map (frame (shift frontier))

def OutcomesRelated (frontier : Nat) :
    (Answer Primitive ⊕ Config Primitive) → (Answer Primitive ⊕ Config Primitive) → Prop
  | .inl before, .inl after => AnswersRelated frontier before after
  | .inr before, .inr after => ConfigsRelated frontier before after
  | _, _ => False

def TransitionsRelated (frontier : Nat)
    (before after : (Answer Primitive ⊕ Config Primitive) × Event) : Prop :=
  OutcomesRelated frontier before.1 after.1 ∧ after.2 = event (shift frontier) before.2

theorem StatesRelated.memoize {frontier : Nat} {before after : Memory Primitive}
    (related : StatesRelated frontier before after) (address : Nat) (v : Value Primitive) :
    StatesRelated frontier (Suspensions.memoize before address v)
      (Suspensions.memoize after (shift frontier address) (value (shift frontier) v)) :=
  ⟨related.1.memoize (shift_injective frontier) address v, related.2⟩

theorem StatesRelated.allocate {frontier : Nat} {before after : Memory Primitive}
    (related : StatesRelated frontier before after)
    (entry : Cell (Expr Primitive) (Env Primitive) (Value Primitive)) :
    StatesRelated frontier (Suspensions.allocate before entry).1
      (Suspensions.allocate after (cell (shift frontier) entry)).1 :=
  ⟨related.1.allocate (shift_injective frontier) (shift_successor related.2) entry,
    Nat.le_trans related.2 (Nat.le_add_right _ _)⟩

theorem StatesRelated.delay {frontier : Nat} {before after : Memory Primitive}
    (related : StatesRelated frontier before after) (body : Expr Primitive) (captured : Env Primitive) :
    StatesRelated frontier (Suspensions.delay before body captured).1
      (Suspensions.delay after body (environment (shift frontier) captured)).1 :=
  related.allocate (.thunk body captured)

theorem StatesRelated.srec {frontier : Nat} {before after : Memory Primitive}
    (related : StatesRelated frontier before after) (targets : Finset Nat) (additions : Env Primitive) :
    StatesRelated frontier
      (Suspensions.srec before targets (fun captured => Env.extend captured additions))
      (Suspensions.srec after (targets.image (shift frontier))
        (fun captured => Env.extend captured (environment (shift frontier) additions))) :=
  ⟨related.1.srec (shift_injective frontier) targets additions, related.2⟩

theorem StatesRelated.exception {frontier : Nat} {before after : Memory Primitive}
    (related : StatesRelated frontier before after) (name : Nat) :
    StatesRelated frontier { before with exceptionNames := insert name before.exceptionNames }
      { after with exceptionNames := insert name after.exceptionNames } :=
  ⟨related.1.exception name, related.2⟩

attribute [local simp] TransitionsRelated OutcomesRelated AnswersRelated ConfigsRelated
  fault primitiveResult result control frame event cell proceed finish
  StatesRelated.memoize StatesRelated.allocate StatesRelated.delay StatesRelated.srec
  StatesRelated.exception

private theorem eval_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (env : Env Primitive) (expression : Expr Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .eval env expression, stack⟩)
      (transition parameters
        ⟨after, .eval (environment (shift frontier) env) expression, stack.map (frame (shift frontier))⟩) := by
  have frontierEq := related.1.frontier
  have namesEq := related.1.exceptionNames
  have lookups := related.1.lookup
  have exceptionUpdate := related.exception (freshExceptionName before)
  cases expression <;> simp only [transition]
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all [freshExceptionName])
      | split at *

private theorem argument_related (parameters : Parameters Primitive) (frontier : Nat)
    (equivariant : Equivariant parameters (shift frontier))
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (functionValue v : Value Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .value v, .argument functionValue :: stack⟩)
      (transition parameters
        ⟨after, .value (value (shift frontier) v),
          .argument (value (shift frontier) functionValue) :: stack.map (frame (shift frontier))⟩) := by
  cases functionValue with
  | primitive operation =>
      simp only [transition, value_primitive]
      rw [equivariant operation v]
      cases parameters.primitive operation v <;> simp [related]
  | _ =>
      simp only [transition]
      repeat' first
        | (fail_if_no_progress subst_vars)
        | (fail_if_no_progress simp_all)
        | split at *

private theorem branch_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (v : Value Primitive) (env : Env Primitive) (yes no : Expr Primitive)
    (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .value v, .branch env yes no :: stack⟩)
      (transition parameters
        ⟨after, .value (value (shift frontier) v),
          .branch (environment (shift frontier) env) yes no :: stack.map (frame (shift frontier))⟩) := by
  cases v <;> simp only [transition]
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all)
      | split at *

private theorem read_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (v : Value Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .value v, .read :: stack⟩)
      (transition parameters
        ⟨after, .value (value (shift frontier) v), .read :: stack.map (frame (shift frontier))⟩) := by
  have lookups := related.1.lookup
  cases v <;> simp only [transition]
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all)
      | split at *

private theorem assignment_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (target v : Value Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .value v, .assignValue target :: stack⟩)
      (transition parameters
        ⟨after, .value (value (shift frontier) v),
          .assignValue (value (shift frontier) target) :: stack.map (frame (shift frontier))⟩) := by
  have lookups := related.1.lookup
  cases target <;> simp only [transition]
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all)
      | split at *

private theorem raising_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (v : Value Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .value v, .raise :: stack⟩)
      (transition parameters
        ⟨after, .value (value (shift frontier) v), .raise :: stack.map (frame (shift frontier))⟩) := by
  cases v <;> simp [transition, related]

private theorem value_related (parameters : Parameters Primitive) (frontier : Nat)
    (equivariant : Equivariant parameters (shift frontier))
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (v : Value Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .value v, stack⟩)
      (transition parameters
        ⟨after, .value (value (shift frontier) v), stack.map (frame (shift frontier))⟩) := by
  have frontierEq := related.1.frontier
  cases stack with
  | nil => simp [transition, related]
  | cons head rest =>
      cases head with
      | argument functionValue =>
          exact argument_related parameters frontier equivariant before after related functionValue v rest
      | branch env yes no => exact branch_related parameters frontier before after related v env yes no rest
      | read => exact read_related parameters frontier before after related v rest
      | assignValue target => exact assignment_related parameters frontier before after related target v rest
      | raise => exact raising_related parameters frontier before after related v rest
      | reference =>
          have allocated := related.allocate (.value v)
          simp only [cell_value] at allocated
          simp [transition, allocated, frontierEq]
      | _ =>
          simp only [transition, List.map_cons, frame]
          repeat' first
            | (fail_if_no_progress subst_vars)
            | (fail_if_no_progress simp_all)
            | split at *

private theorem raised_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (packet : Value Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .raised packet, stack⟩)
      (transition parameters
        ⟨after, .raised (value (shift frontier) packet), stack.map (frame (shift frontier))⟩) := by
  cases stack with
  | nil => simp [transition, related]
  | cons head rest => cases head <;> simp [transition, related]

private theorem atom_pattern_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (env : Env Primitive) (atom : Atom) (v : Value Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .pattern env (.atom atom) v, stack⟩)
      (transition parameters ⟨after, .pattern (environment (shift frontier) env) (.atom atom)
        (value (shift frontier) v), stack.map (frame (shift frontier))⟩) := by
  cases v <;> simp only [transition]
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all)
      | split at *

private theorem constructor_pattern_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (env : Env Primitive) (tag : Nat) (argument : Option Pattern)
    (v : Value Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .pattern env (.constructor tag argument) v, stack⟩)
      (transition parameters ⟨after,
        .pattern (environment (shift frontier) env) (.constructor tag argument)
        (value (shift frontier) v), stack.map (frame (shift frontier))⟩) := by
  cases v <;> simp only [transition]
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all)
      | split at *

private theorem exception_pattern_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (env : Env Primitive) (name : Nat) (argument : Option Pattern)
    (v : Value Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .pattern env (.exception name argument) v, stack⟩)
      (transition parameters ⟨after,
        .pattern (environment (shift frontier) env) (.exception name argument)
        (value (shift frontier) v), stack.map (frame (shift frontier))⟩) := by
  cases found : env.lookup name with
  | none => simp [transition, found, related]
  | some binding =>
      cases binding with
      | exception tag payload =>
          cases payload with
          | some payload => simp [transition, found, related]
          | none =>
              cases v <;> simp only [transition]
              all_goals
                repeat' first
                  | (fail_if_no_progress subst_vars)
                  | (fail_if_no_progress simp_all)
                  | split at *
      | _ => simp [transition, found, related]

private theorem record_pattern_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (env : Env Primitive) (patterns : List (Nat × Pattern))
    (v : Value Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .pattern env (.record patterns) v, stack⟩)
      (transition parameters ⟨after, .pattern (environment (shift frontier) env) (.record patterns)
        (value (shift frontier) v), stack.map (frame (shift frontier))⟩) := by
  cases v with
  | record fields =>
      cases fields with
      | nil =>
          cases patterns with
          | nil => simp [transition, related]
          | cons first remaining =>
              rcases first with ⟨label, inner⟩
              simp [transition, related]
      | cons first remaining =>
          rcases first with ⟨label, entry⟩
          cases patterns with
          | nil => simp [transition, related]
          | cons first remaining =>
              rcases first with ⟨label, inner⟩
              simp [transition, related]
  | _ => simp [transition, related]

private theorem reference_pattern_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (env : Env Primitive) (inner : Pattern) (v : Value Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .pattern env (.reference inner) v, stack⟩)
      (transition parameters ⟨after, .pattern (environment (shift frontier) env) (.reference inner)
        (value (shift frontier) v), stack.map (frame (shift frontier))⟩) := by
  have lookups := related.1.lookup
  cases v <;> simp only [transition]
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all)
      | split at *

private theorem suspended_pattern_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (env : Env Primitive) (inner : Pattern) (v : Value Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .pattern env (.suspended inner) v, stack⟩)
      (transition parameters ⟨after, .pattern (environment (shift frontier) env) (.suspended inner)
        (value (shift frontier) v), stack.map (frame (shift frontier))⟩) := by
  have lookups := related.1.lookup
  cases v <;> simp only [transition]
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all)
      | split at *

private theorem pattern_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (env : Env Primitive) (pattern : Pattern) (v : Value Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .pattern env pattern v, stack⟩)
      (transition parameters ⟨after, .pattern (environment (shift frontier) env) pattern
        (value (shift frontier) v), stack.map (frame (shift frontier))⟩) := by
  cases pattern with
  | atom atom => exact atom_pattern_related parameters frontier before after related env atom v stack
  | constructor tag argument =>
      exact constructor_pattern_related parameters frontier before after related env tag argument v stack
  | exception name argument =>
      exact exception_pattern_related parameters frontier before after related env name argument v stack
  | record patterns =>
      exact record_pattern_related parameters frontier before after related env patterns v stack
  | reference inner =>
      exact reference_pattern_related parameters frontier before after related env inner v stack
  | suspended inner =>
      exact suspended_pattern_related parameters frontier before after related env inner v stack
  | _ => simp [transition, related]

private theorem matched_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (bindings : Env Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .matched bindings, stack⟩)
      (transition parameters
        ⟨after, .matched (environment (shift frontier) bindings), stack.map (frame (shift frontier))⟩) := by
  cases stack with
  | nil => simp [transition, related]
  | cons head rest => cases head <;> simp [transition, related]

private theorem mismatch_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .mismatch, stack⟩)
      (transition parameters ⟨after, .mismatch, stack.map (frame (shift frontier))⟩) := by
  cases stack with
  | nil => simp [transition, related]
  | cons head rest => cases head <;> simp [transition, related]

private theorem clauses_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (env : Env Primitive) (alternatives : List (Pattern × Expr Primitive))
    (v : Value Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .clauses env alternatives v, stack⟩)
      (transition parameters ⟨after, .clauses (environment (shift frontier) env) alternatives
        (value (shift frontier) v), stack.map (frame (shift frontier))⟩) := by
  cases alternatives <;> simp [transition, related]

private theorem rows_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (env : Env Primitive) (patterns : List (Nat × Pattern)) (fields bindings : Env Primitive)
    (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .rows env patterns fields bindings, stack⟩)
      (transition parameters ⟨after, .rows (environment (shift frontier) env) patterns
        (environment (shift frontier) fields) (environment (shift frontier) bindings),
        stack.map (frame (shift frontier))⟩) := by
  cases patterns <;> simp only [transition]
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all)
      | split at *

private theorem recursive_related (parameters : Parameters Primitive) (frontier : Nat)
    (before after : Memory Primitive) (related : StatesRelated frontier before after)
    (env : Env Primitive) (bindings : List (Nat × Expr Primitive)) (created : Env Primitive)
    (body : Expr Primitive) (stack : List (Frame Primitive)) :
    TransitionsRelated frontier
      (transition parameters ⟨before, .recursive env bindings created body, stack⟩)
      (transition parameters ⟨after, .recursive (environment (shift frontier) env) bindings
        (environment (shift frontier) created) body, stack.map (frame (shift frontier))⟩) := by
  cases bindings with
  | nil =>
      have closing := related.srec (addressRange (Env.rec created)) (Env.rec created)
      simp only [addressRange_rec, environment_rec] at closing
      simp [transition, closing]
  | cons head rest =>
      simp only [transition]
      repeat' first
        | (fail_if_no_progress subst_vars)
        | (fail_if_no_progress simp_all)
        | split at *

theorem transition_related {parameters : Parameters Primitive} {frontier : Nat}
    (equivariant : Equivariant parameters (shift frontier))
    {before after : Config Primitive} (related : ConfigsRelated frontier before after) :
    TransitionsRelated frontier (transition parameters before) (transition parameters after) := by
  rcases before with ⟨before, input, stack⟩
  rcases after with ⟨after, output, otherStack⟩
  rcases related with ⟨memories, controls, stackEq⟩
  dsimp only at controls stackEq
  subst output
  subst otherStack
  cases input with
  | eval env expression => exact eval_related parameters frontier before after memories env expression stack
  | value v => exact value_related parameters frontier equivariant before after memories v stack
  | raised packet => exact raised_related parameters frontier before after memories packet stack
  | pattern env pattern v => exact pattern_related parameters frontier before after memories env pattern v stack
  | matched bindings => exact matched_related parameters frontier before after memories bindings stack
  | mismatch => exact mismatch_related parameters frontier before after memories stack
  | clauses env alternatives v => exact clauses_related parameters frontier before after memories env alternatives v stack
  | rows env patterns fields bindings =>
      exact rows_related parameters frontier before after memories env patterns fields bindings stack
  | recursive env bindings created body =>
      exact recursive_related parameters frontier before after memories env bindings created body stack

theorem step_related {parameters : Parameters Primitive} {frontier : Nat}
    (equivariant : Equivariant parameters (shift frontier))
    {before after : Config Primitive} (related : ConfigsRelated frontier before after) :
    OutcomesRelated frontier (step parameters before) (step parameters after) :=
  (transition_related equivariant related).1

theorem evaluates_forward {parameters : Parameters Primitive} {frontier : Nat}
    (equivariant : Equivariant parameters (shift frontier))
    {before : Config Primitive} {answer : Answer Primitive} {count : Nat}
    (execution : Progress.Evaluates (step parameters) before answer count)
    {after : Config Primitive} (related : ConfigsRelated frontier before after) :
    ∃ output, Progress.Evaluates (step parameters) after output count ∧
      AnswersRelated frontier answer output := by
  induction execution generalizing after with
  | done finished =>
      have preserved := step_related equivariant related
      rw [finished] at preserved
      cases moved : step parameters after with
      | inl output => exact ⟨output, .done moved, by simpa only [moved, OutcomesRelated] using preserved⟩
      | inr next => simp only [moved, OutcomesRelated] at preserved
  | next moved rest ih =>
      have preserved := step_related equivariant related
      rw [moved] at preserved
      cases following : step parameters after with
      | inl output => simp only [following, OutcomesRelated] at preserved
      | inr next =>
          obtain ⟨output, execution, final⟩ := ih (by simpa only [following, OutcomesRelated] using preserved)
          exact ⟨output, .next following execution, final⟩

theorem evaluates_backward {parameters : Parameters Primitive} {frontier : Nat}
    (equivariant : Equivariant parameters (shift frontier))
    {after : Config Primitive} {answer : Answer Primitive} {count : Nat}
    (execution : Progress.Evaluates (step parameters) after answer count)
    {before : Config Primitive} (related : ConfigsRelated frontier before after) :
    ∃ output, Progress.Evaluates (step parameters) before output count ∧
      AnswersRelated frontier output answer := by
  induction execution generalizing before with
  | done finished =>
      have preserved := step_related equivariant related
      rw [finished] at preserved
      cases moved : step parameters before with
      | inl output => exact ⟨output, .done moved, by simpa only [moved, OutcomesRelated] using preserved⟩
      | inr next => simp only [moved, OutcomesRelated] at preserved
  | next moved rest ih =>
      have preserved := step_related equivariant related
      rw [moved] at preserved
      cases following : step parameters before with
      | inl output => simp only [following, OutcomesRelated] at preserved
      | inr next =>
          obtain ⟨output, execution, final⟩ := ih (by simpa only [following, OutcomesRelated] using preserved)
          exact ⟨output, .next following execution, final⟩

end Suspensions.Core.Relocation
