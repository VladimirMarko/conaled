import Applications.Suspensions.Prefix
import Applications.Resources.Workload
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Actual transition resources and relational observations

The existing resource executor sequences suspension transitions. Its free
additive monoid records events in execution order. Once an answer is delivered,
additional observation budget changes neither the answer nor its event list.
The raw result retains a residual configuration on unknown; its completion
projection agrees with the existing finite evaluator, including the actual
transition count. Relational observation uses the existing indexed adapters.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Observation
open Machine

variable {Primitive : Type}

def measuredAdvance (parameters : Parameters Primitive) (_ : Unit) :
    Answer Primitive ⊕ Config Primitive →
      Resources.Measured (Answer Primitive ⊕ Config Primitive) (FreeAddMonoid Event)
  | .inl answer => Resources.pure (.inl answer)
  | .inr config => Resources.reweight FreeAddMonoid.ofList (measuredStep parameters config)

theorem measuredAdvance_value (parameters : Parameters Primitive)
    (state : Answer Primitive ⊕ Config Primitive) :
    (measuredAdvance parameters () state).1 = Prefix.advance parameters state := by
  cases state <;> rfl

theorem measuredAdvance_running (parameters : Parameters Primitive) (config : Config Primitive) :
    measuredAdvance parameters () (.inr config) =
      ((transition parameters config).1, FreeAddMonoid.of (transition parameters config).2) := rfl

def workload (parameters : Parameters Primitive) (budget : Nat)
    (state : Answer Primitive ⊕ Config Primitive) :
    Resources.Measured (Answer Primitive ⊕ Config Primitive) (FreeAddMonoid Event) :=
  Resources.run (measuredAdvance parameters) (List.replicate budget ()) state

def observe (parameters : Parameters Primitive) (budget : Nat) (config : Config Primitive) :
    Resources.Measured (Answer Primitive ⊕ Config Primitive) (FreeAddMonoid Event) :=
  workload parameters budget (.inr config)

theorem workload_zero (parameters : Parameters Primitive)
    (state : Answer Primitive ⊕ Config Primitive) : workload parameters 0 state = (state, 0) := rfl

theorem workload_succ (parameters : Parameters Primitive) (budget : Nat)
    (state : Answer Primitive ⊕ Config Primitive) :
    workload parameters (budget + 1) state =
      Resources.bind (measuredAdvance parameters () state) (workload parameters budget) := by
  simp only [workload, List.replicate_succ, Resources.run]

/-- Already finished states consume no further events. -/
theorem workload_finished (parameters : Parameters Primitive) (budget : Nat)
    (answer : Answer Primitive) :
    workload parameters budget (.inl answer) = (.inl answer, 0) := by
  induction budget with
  | zero => rfl
  | succ budget ih =>
      rw [workload_succ]
      simpa only [measuredAdvance, Resources.pure_bind] using ih

theorem workload_append (parameters : Parameters Primitive) (first second : Nat)
    (state : Answer Primitive ⊕ Config Primitive) :
    workload parameters (first + second) state =
      Resources.bind (workload parameters first state) (workload parameters second) := by
  simp only [workload, List.replicate_add, Resources.run_append]

theorem workload_erases (parameters : Parameters Primitive) (budget : Nat)
    (state : Answer Primitive ⊕ Config Primitive) :
    (workload parameters budget state).1 = (Prefix.advance parameters)^[budget] state := by
  induction budget generalizing state with
  | zero => rfl
  | succ budget ih =>
      simp only [workload_succ, Resources.bind_value, ih,
        Function.iterate_succ_apply, measuredAdvance_value]

theorem observe_erases (parameters : Parameters Primitive) (budget : Nat)
    (config : Config Primitive) :
    (observe parameters budget config).1 = Prefix.observe parameters budget config :=
  workload_erases parameters budget (.inr config)

def completion
    (result : Resources.Measured (Answer Primitive ⊕ Config Primitive) (FreeAddMonoid Event)) :
    Option (Answer Primitive × Nat) :=
  match result.1 with
  | .inl answer => some (answer, (FreeAddMonoid.toList result.2).length)
  | .inr _ => none

theorem completion_cons (event : Event)
    (result : Resources.Measured (Answer Primitive ⊕ Config Primitive) (FreeAddMonoid Event)) :
    completion (result.1, FreeAddMonoid.of event + result.2) =
      (completion result).map (fun (answer, steps) => (answer, steps + 1)) := by
  rcases result with ⟨state, events⟩
  cases state <;> simp [completion]

/-- The trace length is the existing evaluator's actual transition count.
An absorbing suffix of unused budget contributes no events. -/
theorem completion_eq_search (parameters : Parameters Primitive) (budget : Nat)
    (config : Config Primitive) :
    completion (observe parameters budget config) =
      Progress.search (step parameters) budget config := by
  induction budget generalizing config with
  | zero => rfl
  | succ budget ih =>
      rw [observe, workload_succ, measuredAdvance_running]
      rcases moved : transition parameters config with ⟨choice, event⟩
      cases choice with
      | inl answer =>
          have finished : step parameters config = .inl answer := by simp [step, moved]
          simp [Resources.bind, workload_finished, completion, Progress.search, finished]
      | inr next =>
          have continued : step parameters config = .inr next := by simp [step, moved]
          change completion ((workload parameters budget (.inr next)).1,
              FreeAddMonoid.of event + (workload parameters budget (.inr next)).2) = _
          rw [completion_cons]
          change (completion (observe parameters budget next)).map
            (fun (answer, steps) => (answer, steps + 1)) = _
          rw [ih, Progress.search, continued]

theorem completed_sound {parameters : Parameters Primitive} {budget : Nat}
    {config : Config Primitive} {answer : Answer Primitive} {events : FreeAddMonoid Event}
    (finished : observe parameters budget config = (.inl answer, events)) :
    Progress.Evaluates (step parameters) config answer (FreeAddMonoid.toList events).length := by
  apply Progress.search_sound (fuel := budget)
  rw [← completion_eq_search, finished]
  rfl

theorem completed_count_le {parameters : Parameters Primitive} {budget : Nat}
    {config : Config Primitive} {answer : Answer Primitive} {events : FreeAddMonoid Event}
    (finished : observe parameters budget config = (.inl answer, events)) :
    (FreeAddMonoid.toList events).length ≤ budget := by
  have prefixFinished : Prefix.observe parameters budget config = .inl answer :=
    (observe_erases parameters budget config).symm.trans (congrArg Prod.fst finished)
  obtain ⟨steps, bound, evaluation⟩ :=
    (Prefix.finished_iff parameters budget config answer).mp prefixFinished
  have same := (completed_sound finished).unique evaluation
  rw [same.2]
  exact bound

/-- Select charges only after recording the actual ordered transition events. -/
theorem workload_reweight (parameters : Parameters Primitive) (budget : Nat)
    (state : Answer Primitive ⊕ Config Primitive) (weight : Event → Nat) :
    Resources.reweight (FreeAddMonoid.lift weight) (workload parameters budget state) =
      Resources.run (fun instruction state => Resources.reweight (FreeAddMonoid.lift weight)
        (measuredAdvance parameters instruction state)) (List.replicate budget ()) state :=
  Resources.reweight_run (FreeAddMonoid.lift weight) (measuredAdvance parameters)
    (List.replicate budget ()) state

def completionSquare (parameters : Parameters Primitive) (budget : Nat) :
    Relational.RelSquare (Optimization.inputRep (Config Primitive))
      (Optimization.membershipRep (I := Config Primitive)
        (id : Option (Answer Primitive × Nat) → Option (Answer Primitive × Nat))) where
  impl config := (config, completion (observe parameters budget config))
  spec config := (config, Progress.admissible (step parameters) config)
  preserves := by
    rintro config _ rfl
    refine ⟨rfl, ?_⟩
    intro answer steps found
    exact Progress.search_sound ((completion_eq_search parameters budget config).symm.trans found)

/-- Compose an ordinary result/effect view while retaining the original input
and actual count. The view is explicit; no memory or resource equality is
inferred from equal returned values. -/
def observedSquare {Q : Type} (parameters : Parameters Primitive) (budget : Nat)
    (view : Answer Primitive → Q) :
    Relational.RelSquare (Optimization.inputRep (Config Primitive))
      (Optimization.membershipRep (I := Config Primitive)
        (id : Option (Q × Nat) → Option (Q × Nat))) :=
  Relational.compose
    (Optimization.observationSquare (fun result : Option (Answer Primitive × Nat) =>
      result.map (fun (answer, steps) => (view answer, steps))))
    (completionSquare parameters budget)

end Suspensions.Core.Observation
