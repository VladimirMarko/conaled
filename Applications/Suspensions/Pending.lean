import Applications.Suspensions.BodyEvent
import Mathlib.Tactic.FailIfNoProgress

/-!
# Pending memoization addresses in actual transitions

Only a suspension-body entry can add a pending memoize address. Other raw
transitions retain a sublist of the pending addresses; exceptional unwinding
may remove an address without writing its cache. No purity or uniqueness is
assumed here, and distinct frames may contain the same address.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Machine
variable {Primitive : Type}

def Frame.memoizeAddress : Frame Primitive → Option Nat
  | .memoize address _ _ => some address
  | _ => none

def pendingAddresses (stack : List (Frame Primitive)) : List Nat :=
  stack.filterMap Frame.memoizeAddress

@[simp] theorem pendingAddresses_nil : pendingAddresses ([] : List (Frame Primitive)) = [] := rfl

@[simp] theorem pendingAddresses_memoize (address : Nat) (environment : Env Primitive)
    (inner : Pattern) (stack : List (Frame Primitive)) :
    pendingAddresses (.memoize address environment inner :: stack) =
      address :: pendingAddresses stack := rfl

theorem pendingAddresses_mem_iff (address : Nat) (stack : List (Frame Primitive)) :
    address ∈ pendingAddresses stack ↔
      ∃ environment inner, .memoize address environment inner ∈ stack := by
  change address ∈ List.filterMap Frame.memoizeAddress stack ↔ _
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨frame, present, pointed⟩
    cases frame <;> simp only [Frame.memoizeAddress, Option.some.injEq, reduceCtorEq] at pointed
    subst address
    exact ⟨_, _, present⟩
  · rintro ⟨environment, inner, present⟩
    exact ⟨.memoize address environment inner, present, rfl⟩

/-- A completed answer has no further continuation. An unfinished transition
either removes pending occurrences or pushes its actual body-event address. -/
def PendingTransition (before : List Nat) (event : Event) :
    Answer Primitive ⊕ Config Primitive → Prop
  | .inl _ => True
  | .inr next => (pendingAddresses next.stack).Sublist before ∨
      ∃ address, event = .body address ∧ pendingAddresses next.stack = address :: before

private theorem eval_pending (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (expression : Expr Primitive) (stack : List (Frame Primitive)) :
    PendingTransition (pendingAddresses stack)
      (transition parameters ⟨memory, .eval environment expression, stack⟩).2
      (step parameters ⟨memory, .eval environment expression, stack⟩) := by
  cases expression <;> simp only [step, transition, proceed, finish, PendingTransition]
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all [pendingAddresses, List.filterMap_cons, Frame.memoizeAddress])
      | split at *

private theorem value_pending (parameters : Parameters Primitive) (memory : Memory Primitive)
    (value : Value Primitive) (stack : List (Frame Primitive)) :
    PendingTransition (pendingAddresses stack)
      (transition parameters ⟨memory, .value value, stack⟩).2
      (step parameters ⟨memory, .value value, stack⟩) := by
  cases stack with
  | nil => trivial
  | cons frame rest =>
      cases frame <;> simp only [step, transition, proceed, finish, PendingTransition]
      all_goals
        repeat' first
          | (fail_if_no_progress subst_vars)
          | (fail_if_no_progress simp_all [pendingAddresses, List.filterMap_cons, Frame.memoizeAddress])
          | split at *

private theorem raised_pending (parameters : Parameters Primitive) (memory : Memory Primitive)
    (packet : Value Primitive) (stack : List (Frame Primitive)) :
    PendingTransition (pendingAddresses stack)
      (transition parameters ⟨memory, .raised packet, stack⟩).2
      (step parameters ⟨memory, .raised packet, stack⟩) := by
  cases stack with
  | nil => trivial
  | cons frame rest =>
      cases frame <;> simp [step, transition, proceed, PendingTransition,
        pendingAddresses, List.filterMap_cons, Frame.memoizeAddress]

private theorem pattern_pending (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (pattern : Pattern) (value : Value Primitive)
    (stack : List (Frame Primitive)) :
    PendingTransition (pendingAddresses stack)
      (transition parameters ⟨memory, .pattern environment pattern value, stack⟩).2
      (step parameters ⟨memory, .pattern environment pattern value, stack⟩) := by
  cases pattern <;> simp only [step, transition, proceed, finish, PendingTransition]
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all [pendingAddresses, List.filterMap_cons, Frame.memoizeAddress])
      | split at *

private theorem matched_pending (parameters : Parameters Primitive) (memory : Memory Primitive)
    (bindings : Env Primitive) (stack : List (Frame Primitive)) :
    PendingTransition (pendingAddresses stack)
      (transition parameters ⟨memory, .matched bindings, stack⟩).2
      (step parameters ⟨memory, .matched bindings, stack⟩) := by
  cases stack with
  | nil => trivial
  | cons frame rest =>
      cases frame <;> simp [step, transition, proceed, finish, PendingTransition,
        pendingAddresses, List.filterMap_cons, Frame.memoizeAddress]

private theorem mismatch_pending (parameters : Parameters Primitive) (memory : Memory Primitive)
    (stack : List (Frame Primitive)) :
    PendingTransition (pendingAddresses stack)
      (transition parameters ⟨memory, .mismatch, stack⟩).2
      (step parameters ⟨memory, .mismatch, stack⟩) := by
  cases stack with
  | nil => trivial
  | cons frame rest =>
      cases frame <;> simp [step, transition, proceed, finish, PendingTransition,
        pendingAddresses, List.filterMap_cons, Frame.memoizeAddress]

private theorem clauses_pending (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (clauses : List (Pattern × Expr Primitive)) (value : Value Primitive)
    (stack : List (Frame Primitive)) :
    PendingTransition (pendingAddresses stack)
      (transition parameters ⟨memory, .clauses environment clauses value, stack⟩).2
      (step parameters ⟨memory, .clauses environment clauses value, stack⟩) := by
  cases clauses with
  | nil => exact Or.inl (.refl _)
  | cons clause rest =>
      cases clause
      exact Or.inl (.refl _)

private theorem rows_pending (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (patterns : List (Nat × Pattern)) (fields bindings : Env Primitive)
    (stack : List (Frame Primitive)) :
    PendingTransition (pendingAddresses stack)
      (transition parameters ⟨memory, .rows environment patterns fields bindings, stack⟩).2
      (step parameters ⟨memory, .rows environment patterns fields bindings, stack⟩) := by
  cases patterns with
  | nil => exact Or.inl (.refl _)
  | cons row rest =>
      cases row
      simp only [step, transition, proceed, finish, PendingTransition]
      repeat' first
        | (fail_if_no_progress subst_vars)
        | (fail_if_no_progress simp_all [pendingAddresses, List.filterMap_cons, Frame.memoizeAddress])
        | split at *

private theorem recursive_pending (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (bindings : List (Nat × Expr Primitive)) (created : Env Primitive)
    (body : Expr Primitive) (stack : List (Frame Primitive)) :
    PendingTransition (pendingAddresses stack)
      (transition parameters ⟨memory, .recursive environment bindings created body, stack⟩).2
      (step parameters ⟨memory, .recursive environment bindings created body, stack⟩) := by
  cases bindings with
  | nil => exact Or.inl (.refl _)
  | cons binding rest =>
      cases binding
      simp only [step, transition, proceed, finish, PendingTransition]
      repeat' first
        | (fail_if_no_progress subst_vars)
        | (fail_if_no_progress simp_all [pendingAddresses, List.filterMap_cons, Frame.memoizeAddress])
        | split at *

theorem pending_transition (parameters : Parameters Primitive) (config : Config Primitive) :
    PendingTransition (pendingAddresses config.stack) (transition parameters config).2
      (step parameters config) := by
  rcases config with ⟨memory, control, stack⟩
  cases control with
  | eval environment expression => exact eval_pending parameters memory environment expression stack
  | value value => exact value_pending parameters memory value stack
  | raised packet => exact raised_pending parameters memory packet stack
  | pattern environment pattern value => exact pattern_pending parameters memory environment pattern value stack
  | matched bindings => exact matched_pending parameters memory bindings stack
  | mismatch => exact mismatch_pending parameters memory stack
  | clauses environment clauses value => exact clauses_pending parameters memory environment clauses value stack
  | rows environment patterns fields bindings =>
      exact rows_pending parameters memory environment patterns fields bindings stack
  | recursive environment bindings created body =>
      exact recursive_pending parameters memory environment bindings created body stack

/-- Conditional raw preservation. Pure finite sources will discharge the
fresh-entry premise using their proved nonreentry theorem. -/
theorem step_pending_nodup {parameters : Parameters Primitive} {config next : Config Primitive}
    (distinct : (pendingAddresses config.stack).Nodup)
    (fresh : ∀ address, (transition parameters config).2 = .body address →
      address ∉ pendingAddresses config.stack)
    (moved : step parameters config = .inr next) :
    (pendingAddresses next.stack).Nodup := by
  have shape := pending_transition parameters config
  rw [moved] at shape
  rcases shape with smaller | ⟨address, event, added⟩
  · exact distinct.sublist smaller
  · rw [added]
    exact List.nodup_cons.mpr ⟨fresh address event, distinct⟩

end Suspensions.Core.Machine
