import Applications.Suspensions.Machine
import Mathlib.Logic.Function.Iterate

/-!
# Bounded observation of the existing suspension machine

An unfinished observation retains the entire residual configuration, including
memory. Finished answers are absorbing solely to make bounded observation a
total iterator. The budget is not the amount of body work: completion is
related to the actual finite transition count in `Progress.Evaluates`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Prefix
open Machine

variable {Primitive : Type}

def advance (parameters : Parameters Primitive) :
    Answer Primitive ⊕ Config Primitive → Answer Primitive ⊕ Config Primitive
  | .inl answer => .inl answer
  | .inr config => Machine.step parameters config

def observe (parameters : Parameters Primitive) (budget : Nat) (config : Config Primitive) :
    Answer Primitive ⊕ Config Primitive :=
  (advance parameters)^[budget] (.inr config)

@[simp] theorem iterate_answer (parameters : Parameters Primitive) (budget : Nat)
    (answer : Answer Primitive) :
    (advance parameters)^[budget] (.inl answer) = .inl answer := by
  induction budget with
  | zero => rfl
  | succ budget ih =>
    rw [Function.iterate_succ_apply]
    exact ih

@[simp] theorem observe_zero (parameters : Parameters Primitive) (config : Config Primitive) :
    observe parameters 0 config = .inr config := rfl

theorem observe_succ (parameters : Parameters Primitive) (budget : Nat)
    (config : Config Primitive) :
    observe parameters (budget + 1) config =
      (advance parameters)^[budget] (Machine.step parameters config) := by
  simp only [observe, Function.iterate_succ_apply, advance]

/-- Finished observations retain their reached state under a larger budget. -/
theorem stays_finished (parameters : Parameters Primitive) (budget extra : Nat)
    (config : Config Primitive) (answer : Answer Primitive)
    (finished : observe parameters budget config = .inl answer) :
    observe parameters (budget + extra) config = .inl answer := by
  unfold observe at finished ⊢
  rw [Nat.add_comm budget extra, Function.iterate_add_apply, finished, iterate_answer]

/-- The budget bounds an actual evaluation; absorbing suffix iterations do
not increase its transition count. No source validity or termination premise
is hidden in this characterization. -/
theorem finished_iff (parameters : Parameters Primitive) (budget : Nat)
    (config : Config Primitive) (answer : Answer Primitive) :
    observe parameters budget config = .inl answer ↔
      ∃ steps, steps ≤ budget ∧ Progress.Evaluates (Machine.step parameters) config answer steps := by
  induction budget generalizing config with
  | zero =>
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨steps, bound, evaluation⟩
      cases evaluation <;> omega
  | succ budget ih =>
    cases moved : Machine.step parameters config with
    | inl result =>
      rw [observe_succ, moved, iterate_answer]
      constructor
      · intro same
        have values : result = answer := Sum.inl.inj same
        subst result
        exact ⟨1, by omega, .done moved⟩
      · rintro ⟨steps, _bound, evaluation⟩
        cases evaluation with
        | done stopped => exact moved.symm.trans stopped
        | next first _ => simp [moved] at first
    | inr next =>
      rw [observe_succ, moved]
      change observe parameters budget next = .inl answer ↔ _
      constructor
      · intro finished
        obtain ⟨steps, bound, evaluation⟩ := (ih next).mp finished
        exact ⟨steps + 1, Nat.succ_le_succ bound, .next moved evaluation⟩
      · rintro ⟨steps, bound, evaluation⟩
        cases evaluation with
        | done stopped => simp [moved] at stopped
        | next first tail =>
          have same := Sum.inr.inj (moved.symm.trans first)
          cases same
          exact (ih _).mpr ⟨_, by omega, tail⟩

/-- The existing finite evaluator supplies the same answer and actual count. -/
theorem finished_iff_search (parameters : Parameters Primitive) (budget : Nat)
    (config : Config Primitive) (answer : Answer Primitive) :
    observe parameters budget config = .inl answer ↔
      ∃ steps, steps ≤ budget ∧
        Progress.search (Machine.step parameters) budget config = some (answer, steps) := by
  constructor
  · intro finished
    obtain ⟨steps, bound, evaluation⟩ := (finished_iff parameters budget config answer).mp finished
    exact ⟨steps, bound, Progress.search_complete evaluation bound⟩
  · rintro ⟨steps, bound, found⟩
    exact (finished_iff parameters budget config answer).mpr
      ⟨steps, bound, Progress.search_sound found⟩

/-- Creation has returned a value control after allocation, with its memory
available even though the enclosing machine answer has not yet been returned. -/
theorem delay_prefix (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (body : Expr Primitive) :
    observe parameters 1 (Machine.start memory environment (.delay body)) =
      let created := Suspensions.delay memory body environment
      .inr ⟨created.1, .value (.address created.2), []⟩ := rfl

/-- Returning a newly allocated suspension does not evaluate its stored body. -/
theorem delay_answer (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (body : Expr Primitive) :
    observe parameters 2 (Machine.start memory environment (.delay body)) =
      let created := Suspensions.delay memory body environment
      .inl ⟨created.1, .value (.address created.2)⟩ := rfl

end Suspensions.Core.Prefix
