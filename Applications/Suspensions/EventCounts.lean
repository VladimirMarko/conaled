import Applications.Suspensions.Observation
import Batteries.Data.List.Count

/-!
# Selected counts of actual suspension events

The count is an ordinary additive observation of the existing ordered event
trace. Its successor and completion laws refer to the same measured workload;
they introduce neither another evaluator nor a runtime cost for an event.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Observation
open Machine

/-- Count occurrences of a selected event in the actual ordered trace. -/
def eventCount (selected : Event) : FreeAddMonoid Event →+ Nat where
  toFun events := (FreeAddMonoid.toList events).count selected
  map_zero' := rfl
  map_add' first second := by
    simp only [FreeAddMonoid.toList_add, List.count_append]

theorem eventCount_eq_count (selected : Event) (events : FreeAddMonoid Event) :
    eventCount selected events = (FreeAddMonoid.toList events).count selected := rfl

@[simp] theorem eventCount_of (selected event : Event) :
    eventCount selected (FreeAddMonoid.of event) = if event = selected then 1 else 0 := by
  change ([event] : List Event).count selected = _
  exact List.count_singleton' selected event

/-- The count is the existing resource reweighting by the selected indicator. -/
theorem eventCount_eq_lift (selected : Event) :
    eventCount selected = FreeAddMonoid.lift (fun event => if event = selected then 1 else 0) := by
  apply FreeAddMonoid.hom_eq
  intro event
  rw [eventCount_of, FreeAddMonoid.lift_eval_of]

variable {Primitive : Type}

@[simp] theorem eventCount_workload_finished (parameters : Parameters Primitive)
    (budget : Nat) (selected : Event) (answer : Answer Primitive) :
    eventCount selected (workload parameters budget (.inl answer)).2 = 0 := by
  rw [workload_finished]
  exact map_zero _

@[simp] theorem eventCount_observe_zero (parameters : Parameters Primitive)
    (config : Config Primitive) (selected : Event) :
    eventCount selected (observe parameters 0 config).2 = 0 := rfl

/-- Count the event of the actual first transition and then its actual suffix. -/
theorem eventCount_observe_succ (parameters : Parameters Primitive) (budget : Nat)
    (selected : Event) (config : Config Primitive) :
    eventCount selected (observe parameters (budget + 1) config).2 =
      eventCount selected (FreeAddMonoid.of (transition parameters config).2) +
        eventCount selected (workload parameters budget (step parameters config)).2 := by
  rw [observe, workload_succ, measuredAdvance_running]
  change eventCount selected
    (FreeAddMonoid.of (transition parameters config).2 +
      (workload parameters budget (step parameters config)).2) = _
  exact map_add _ _ _

/-- Concatenated budgets compose at the actual intermediate machine state. -/
theorem eventCount_workload_append (parameters : Parameters Primitive) (first second : Nat)
    (state : Answer Primitive ⊕ Config Primitive) (selected : Event) :
    eventCount selected (workload parameters (first + second) state).2 =
      eventCount selected (workload parameters first state).2 +
        eventCount selected (workload parameters second (workload parameters first state).1).2 := by
  rw [workload_append]
  change eventCount selected
      ((workload parameters first state).2 +
        (workload parameters second (workload parameters first state).1).2) = _
  exact map_add _ _ _

/-- Increasing the budget appends actual events or an empty finished suffix. -/
theorem eventCount_observe_mono (parameters : Parameters Primitive) (config : Config Primitive)
    {first second : Nat} (bound : first ≤ second) (selected : Event) :
    eventCount selected (observe parameters first config).2 ≤
      eventCount selected (observe parameters second config).2 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bound
  change eventCount selected (workload parameters first (.inr config)).2 ≤
    eventCount selected (workload parameters (first + extra) (.inr config)).2
  rw [workload_append]
  change eventCount selected (workload parameters first (.inr config)).2 ≤
    eventCount selected
      ((workload parameters first (.inr config)).2 +
        (workload parameters extra (workload parameters first (.inr config)).1).2)
  rw [map_add]
  exact Nat.le_add_right _ _

/-- An absorbing finished suffix changes neither the trace nor its count. -/
theorem eventCount_observe_after_finished {parameters : Parameters Primitive}
    {config : Config Primitive} {answer : Answer Primitive} {budget : Nat}
    (finished : Prefix.observe parameters budget config = .inl answer)
    (extra : Nat) (selected : Event) :
    eventCount selected (observe parameters (budget + extra) config).2 =
      eventCount selected (observe parameters budget config).2 := by
  have erased : (workload parameters budget (.inr config)).1 = .inl answer :=
    (observe_erases parameters budget config).trans finished
  rw [observe, workload_append]
  change eventCount selected
      ((workload parameters budget (.inr config)).2 +
        (workload parameters extra (workload parameters budget (.inr config)).1).2) = _
  rw [erased, workload_finished]
  simp only [observe, add_zero]

/-- A completed zero count is zero at every budget: earlier counts are no
larger, and later finished suffixes add no events. -/
theorem eventCount_observe_zero_of_finished {parameters : Parameters Primitive}
    {config : Config Primitive} {answer : Answer Primitive} {completed : Nat}
    (finished : Prefix.observe parameters completed config = .inl answer)
    (selected : Event) (zero : eventCount selected (observe parameters completed config).2 = 0)
    (budget : Nat) : eventCount selected (observe parameters budget config).2 = 0 := by
  by_cases before : budget ≤ completed
  · exact Nat.eq_zero_of_le_zero
      ((eventCount_observe_mono parameters config before selected).trans (Nat.le_of_eq zero))
  · have after : completed ≤ budget := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le after
    rw [eventCount_observe_after_finished finished extra selected]
    exact zero

end Suspensions.Core.Observation
