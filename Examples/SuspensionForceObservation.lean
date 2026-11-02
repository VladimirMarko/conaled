import Applications.Suspensions.ForceObservation
import Examples.SuspensionRelocation

/-!
# Force/delay preserves the reference observations

The execution theorem is applied to the independently computed direct body.
It yields the differently numbered returned reference and both observable heap
effects, while retaining the extra twelve explicit forcing transitions.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionForceObservation
open Suspensions Suspensions.Core Suspensions.Core.Machine
open Suspensions.Core.Renaming Suspensions.Core.Relocation Suspensions.Core.ForceObservation
open Examples.SuspensionRelocation

theorem initial_bounded : Bounded initial := allocate_bounded bounded_empty _

theorem initial_fixed : FixedCells (shift initial.next) initial := by
  intro address entry found
  by_cases atZero : address = 0
  · subst address
    change some (.value (integer 5)) = some entry at found
    cases found
    rfl
  · simp [initial, Suspensions.allocate, Suspensions.empty, Durability.put, atZero] at found

theorem reference_effects_after_force :
    ∃ memory, Progress.Evaluates (step parameters) (start initial bindings (force (.delay body)))
      ⟨memory, .value (.address 2)⟩ 25 ∧
      memory.memory 0 = some (.value (integer 7)) ∧
      memory.memory 2 = some (.value (integer 9)) ∧ memory.next = 3 := by
  obtain ⟨memory, execution, related⟩ := value_observed
    (primitives_equivariant 1) initial_bounded initial_fixed rfl direct_execution
  exact ⟨memory, execution, related.1.lookup 0, related.1.lookup 1, related.1.frontier⟩

end Examples.SuspensionForceObservation
