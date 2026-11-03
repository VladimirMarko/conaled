import Applications.Suspensions.EventCounts
import Examples.SuspensionObservation

/-!
# Selecting and composing actual event counts

The existing delayed-literal program allocates an address and returns it in
two transitions, without entering the body. These examples select distinct
observations of that same run and use the generic composition/absorption laws.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionEventCounts
open Suspensions.Core Suspensions.Core.Machine Suspensions.Core.Observation
open SuspensionObservation

/-- Allocation and body entry are different events in the same actual trace. -/
theorem unforced_counts :
    eventCount (.allocate 0) (observe parameters 2 config).2 = 1 ∧
      eventCount (.body 0) (observe parameters 2 config).2 = 0 := by
  rw [two_transitions_finish]
  decide

private theorem finished : Prefix.observe parameters 2 config = .inl answer :=
  (Prefix.finished_iff parameters 2 config answer).mpr ⟨2, Nat.le_refl _, actual_count⟩

/-- This is a universal budget consequence of the finite source observation,
not a computation at one chosen larger budget. -/
theorem unforced_body_zero (budget : Nat) :
    eventCount (.body 0) (observe parameters budget config).2 = 0 :=
  eventCount_observe_zero_of_finished finished (.body 0) unforced_counts.2 budget

/-- The second segment starts from the actual allocated-memory continuation. -/
theorem actual_split_count :
    eventCount (.allocate 0) (observe parameters 2 config).2 =
      eventCount (.allocate 0) (observe parameters 1 config).2 +
        eventCount (.allocate 0) (workload parameters 1 (observe parameters 1 config).1).2 :=
  eventCount_workload_append parameters 1 1 (.inr config) (.allocate 0)

/-- Its two summands count the first allocation and the later delivery. -/
theorem split_expected_counts :
    eventCount (.allocate 0) (observe parameters 1 config).2 = 1 ∧
      eventCount (.allocate 0) (workload parameters 1 (observe parameters 1 config).1).2 = 0 := by
  exact ⟨rfl, rfl⟩

/-- Selecting the event is ordinary additive reweighting of the same workload. -/
theorem selected_allocation_reweight :
    Resources.reweight (eventCount (.allocate 0)) (workload parameters 2 (.inr config)) =
      Resources.run (fun instruction state => Resources.reweight (eventCount (.allocate 0))
        (measuredAdvance parameters instruction state)) (List.replicate 2 ()) (.inr config) := by
  rw [eventCount_eq_lift]
  exact workload_reweight parameters 2 (.inr config)
    (fun event => if event = .allocate 0 then 1 else 0)

end Examples.SuspensionEventCounts
