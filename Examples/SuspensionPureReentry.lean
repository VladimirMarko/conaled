import Applications.Suspensions.Pure.Reentry
import Examples.SuspensionPureSimulation

/-!
# The represented cyclic configuration has no finite pure continuation

The existing example supplies the raw/pure representation and the old active
memoize occurrence at index 3. Its actual next raw and pure transitions are
retained. The new public ConfigRep theorem excludes completion of the current
pure configuration; no raw nontermination statement is made here.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureReentry
open Suspensions Suspensions.Pure Suspensions.Pure.Simulation
open Examples.SuspensionPureMachine Examples.SuspensionPureMemory
open Examples.SuspensionPureHistory Examples.SuspensionPureSimulation

theorem active_cycle_no_finite_pure_result :
    ¬Progress.Terminates (Machine.step parameters) pureBefore :=
  before_related.active_force_pure_not_terminates (index := 3) rfl rfl

/-- The obstruction is connected to a satisfiable represented configuration
and the original actual entry transitions, not to a no-reentry premise. -/
theorem obstruction_at_actual_reentry (rawParameters : Core.Machine.Parameters Empty) :
    ConfigRep parameters cycleWorld rawBefore pureBefore ∧
    rawBefore.stack[3]? = some (.memoize 0 rawEnvironment (.variable 0)) ∧
    Core.Machine.transition rawParameters rawBefore = (.inr rawAfter, .body 0) ∧
    Machine.transition parameters pureBefore =
      (.inr pureAfter, .body cycleBody [] (some cycleGroup)) ∧
    ¬Progress.Terminates (Machine.step parameters) pureBefore :=
  ⟨before_related, rfl, raw_actual_entry rawParameters, pure_actual_entry,
    active_cycle_no_finite_pure_result⟩

/-- This includes every result constructor and every finite transition count. -/
theorem cycle_has_no_finite_pure_answer (answer : Machine.Result Empty) (steps : Nat) :
    ¬Progress.Evaluates (Machine.step parameters) pureBefore answer steps :=
  fun evaluation => active_cycle_no_finite_pure_result ⟨answer, steps, evaluation⟩

end Examples.SuspensionPureReentry
