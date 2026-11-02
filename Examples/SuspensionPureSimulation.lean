import Applications.Suspensions.Pure.Simulation
import Examples.SuspensionPureHistory

/-!
# A represented state immediately before and after actual body reentry

The same raw address occurs in two pending memoize frames after the step. Both
states satisfy the representation/history invariant. The raw transition is the
original unrestricted machine transition, and the pure transition is its actual
body entry. Their finite-completion obstruction is established separately by
the history theorem, not by excluding this represented intermediate state.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureSimulation
open Suspensions Suspensions.Pure Suspensions.Pure.Representation Suspensions.Pure.Simulation
open Examples.SuspensionPureMachine Examples.SuspensionPureRecurrence
open Examples.SuspensionPureMemory Examples.SuspensionPureHistory

theorem cycle_capture : EnvRep cycleWorld rawEnvironment cycleEnvironment :=
  cycle_template_represented.unroll

theorem cycle_address : ValueRep cycleWorld (.address 0) cycleMeaning.value := .address rfl

theorem pending_frames_related : FramesRep cycleWorld rawPending purePending :=
  .cons (.clause _ _ cycle_capture cycle_address)
    (.cons .applicationResult (.cons .applicationResult (.cons (.memoize _ rfl cycle_capture) .nil)))

def rawBefore : Core.Machine.Config Empty :=
  ⟨cycleMemory, .pattern rawEnvironment (.suspended (.variable 0)) (.address 0), rawPending⟩

def pureBefore : Machine.Config Empty := ⟨beforeEntry, purePending⟩

theorem before_related : ConfigRep parameters cycleWorld rawBefore pureBefore :=
  ⟨cycle_memory_represented, .pattern _ cycle_capture cycle_address,
    pending_frames_related, pending_cycle_history⟩

def rawAfter : Core.Machine.Config Empty :=
  ⟨cycleMemory, .eval rawEnvironment cycleBody,
    .memoize 0 rawEnvironment (.variable 0) :: rawPending⟩

def pureAfter : Machine.Config Empty :=
  ⟨.eval cycleEnvironment cycleBody, .force cycleEnvironment (.variable 0) :: purePending⟩

theorem raw_actual_entry (rawParameters : Core.Machine.Parameters Empty) :
    Core.Machine.transition rawParameters rawBefore = (.inr rawAfter, .body 0) := rfl

theorem pure_actual_entry :
    Machine.transition parameters pureBefore =
      (.inr pureAfter, .body cycleBody [] (some cycleGroup)) := rfl

theorem after_related : ConfigRep parameters cycleWorld rawAfter pureAfter :=
  ⟨cycle_memory_represented, .eval _ cycle_capture,
    .cons (.memoize _ rfl cycle_capture) pending_frames_related,
    duplicate_pending_occurrences_allowed⟩

theorem represented_reentry_has_no_finite_pure_continuation :
    ConfigRep parameters cycleWorld rawAfter pureAfter ∧
      ¬Progress.Terminates (Machine.step parameters) pureAfter :=
  ⟨after_related, duplicate_prefix_still_cannot_finish⟩

end Examples.SuspensionPureSimulation
