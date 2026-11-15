import Applications.Resources.Persistent.Realization
import Examples.SuspensionPureCacheCounts

/-!
# Source boundaries for a debit observation

The source examples below reuse actual finite suspension observations. A
successful repeated force has one body entry, while a handled exception has
two body entries and no successful cache write. Assigning the whole body to
one address-valued debit therefore needs an additional work correspondence.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.PersistentSourceBoundary

open Resources Resources.Persistent
open Suspensions

private def parameters := Examples.SuspensionPureCachedClosure.rawParameters

private def repeatedStart : Core.Machine.Config Empty :=
  Core.Machine.start empty [] Examples.SuspensionPureCacheCounts.Repeated.program

private def retryStart : Core.Machine.Config Empty :=
  Core.Machine.start empty [(3, .exception 17 none)]
    Examples.SuspensionPureCacheCounts.Exceptions.program

private def oneAddress (_ : Bool) : Finset Nat := {0}
private def noUnshared (_ : Bool) : Nat := 0

/-- The explicit abstract interpreter charges the shared address once. -/
private theorem address_charge :
    (run (realizeStep noUnshared oneAddress) [false, true] ∅).2 = 1 := by
  rw [realize_run_cost]
  decide

/-- A checked successful source case agrees on its body-entry observation.
Other transition events and body work are outside this one observation. -/
theorem successful_body_entry_observation :
    let events := FreeAddMonoid.toList
      (Core.Observation.observe parameters 21 repeatedStart).2
    events.count (.body 0) =
        (run (realizeStep noUnshared oneAddress) [false, true] ∅).2 ∧
      events.count (.cacheWrite 0) = 1 ∧ events.count (.hit 0) = 1 := by
  have source := Examples.SuspensionPureCacheCounts.Repeated.one_write_then_hit
  rw [address_charge]
  exact source

/-- Successful-write bounds cannot erase the body's actual retry observation. -/
theorem retry_exceeds_address_charge :
    let events := FreeAddMonoid.toList
      (Core.Observation.observe parameters 50 retryStart).2
    events.count (.body 0) = 2 ∧ events.count (.cacheWrite 0) = 0 ∧
      (run (realizeStep noUnshared oneAddress) [false, true] ∅).2 <
        events.count (.body 0) := by
  have source := Examples.SuspensionPureCacheCounts.Exceptions.two_attempts_without_write
  refine ⟨source.1, source.2.1, ?_⟩
  rw [address_charge]
  have body : (FreeAddMonoid.toList
      (Core.Observation.observe parameters 50 retryStart).2).count (.body 0) = 2 := source.1
  rw [body]
  decide

end Examples.PersistentSourceBoundary
