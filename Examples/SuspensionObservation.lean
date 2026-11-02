import Applications.Suspensions.Observation

/-!
# Budget, actual events and retained unknown state

Creation of a delayed literal allocates once and then returns its address.
Neither transition evaluates the body. Additional budget after those two
transitions contributes no work. The selected result view below is composed
through the public indexed relational adapter.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionObservation
open Suspensions.Core Suspensions.Core.Machine Suspensions.Core.Observation

def parameters : Parameters Unit := ⟨fun _ _ => .stuck .primitive, 0, 1⟩

def initial : Memory Unit := Suspensions.empty

def body : Expr Unit := .atom (.integer 7)

def created : Memory Unit := (Suspensions.delay initial body []).1

def config : Config Unit := start initial [] (.delay body)

def answer : Answer Unit := ⟨created, .value (.address 0)⟩

theorem no_budget : observe parameters 0 config = (.inr config, 0) := rfl

theorem one_transition_retains_allocated_memory :
    observe parameters 1 config =
      (.inr ⟨created, .value (.address 0), []⟩, FreeAddMonoid.of (.allocate 0)) := rfl

theorem two_transitions_finish :
    observe parameters 2 config =
      (.inl answer, FreeAddMonoid.ofList [.allocate 0, .core]) := rfl

theorem extra_budget_is_uncharged :
    observe parameters 9 config =
      (.inl answer, FreeAddMonoid.ofList [.allocate 0, .core]) := rfl

theorem stored_body_is_unevaluated :
    answer.memory.memory 0 = some (.thunk body []) ∧ answer.memory.next = 1 := by
  exact ⟨rfl, rfl⟩

theorem actual_count : Progress.Evaluates (step parameters) config answer 2 :=
  completed_sound extra_budget_is_uncharged

theorem completion_agrees : Progress.search (step parameters) 9 config = some (answer, 2) := by
  rw [← completion_eq_search, extra_budget_is_uncharged]
  rfl

theorem result_view :
    ((observedSquare parameters 9 Answer.result).impl config).2 =
      some (.value (.address 0), 2) := rfl

end Examples.SuspensionObservation
