import Applications.Suspensions.Pure.History
import Examples.SuspensionPureMemory

/-!
# Completing a past prefix and retaining duplicate active occurrences

The literal's one executed transition supplies the cache witness only when
its value is delivered. The recursive example retains a fourteen-transition
prefix immediately before reentry. Taking its next actual pure step proves
nontermination through the per-occurrence history theorem, while the history
invariant itself still admits both occurrences of the same raw address.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureHistory
open Suspensions Suspensions.Pure Suspensions.Pure.Representation
open Suspensions.Pure.Memory Suspensions.Pure.History Suspensions.Pure.Recurrence
open Examples.SuspensionPureMachine Examples.SuspensionPureRecurrence Examples.SuspensionPureMemory

theorem literal_past_prefix :
    BodyHistory parameters literalWorld 0 (.value (.atom (.integer 7))) [] :=
  ⟨literalMeaning, 1, rfl, Reaches.one rfl⟩

/-- The finite evaluation is obtained from the past prefix by the public
completion theorem, then supplied to the actual memoize-preservation law. -/
theorem literal_cache_from_history : StateRep parameters literalWorld cachedMemory := by
  obtain ⟨steps, completed⟩ := literal_past_prefix.completed (meaning := literalMeaning) rfl
  exact literal_allocated.2.1.memoize rfl (.atom (.integer 7)) completed

def rawEnvironment : Core.Env Empty := Core.Env.rec cycleTemplate

def rawPending : List (Core.Machine.Frame Empty) :=
  [.clause rawEnvironment (.variable 0) [] (.address 0),
   .applicationResult, .applicationResult,
   .memoize 0 rawEnvironment (.variable 0)]

def purePending : List (Machine.Frame Empty) :=
  recurringCaller.tail ++ [.force cycleEnvironment (.variable 0)]

def beforeEntry : Machine.Control Empty :=
  .pattern cycleEnvironment (.suspended (.variable 0)) cycleMeaning.value

/-- The unique old memoize occurrence is at index3. Its actual isolated body
prefix has14 transitions; the still-pending outer force is outside that body. -/
theorem pending_cycle_history :
    ActiveHistories parameters cycleWorld rawPending beforeEntry purePending := by
  intro index address environment inner found
  cases index with
  | zero => cases found
  | succ index =>
      cases index with
      | zero => cases found
      | succ index =>
          cases index with
          | zero => cases found
          | succ index =>
              cases index with
              | zero =>
                  have same : (Core.Machine.Frame.memoize 0 rawEnvironment (.variable 0)) =
                      .memoize address environment inner := Option.some.inj found
                  cases same
                  exact ⟨cycleMeaning, 14, rfl, rfl⟩
              | succ index => simp [rawPending] at found

theorem pending_reentry_precludes_finite_body :
    ¬Progress.Terminates (Machine.step parameters)
      (Machine.start cycleMeaning.environment cycleMeaning.body) :=
  pending_cycle_history.reentry_not_terminates (index := 3) rfl rfl

/-- The invariant does not hide a distinct-active-address premise. Both
occurrences are represented after taking the actual next body-entry step. -/
theorem duplicate_pending_occurrences_allowed :
    ActiveHistories parameters cycleWorld
      (.memoize 0 rawEnvironment (.variable 0) :: rawPending)
      (.eval cycleMeaning.environment cycleMeaning.body)
      (.force cycleEnvironment (.variable 0) :: purePending) := by
  apply pending_cycle_history.push (steps := 1)
  · intro address environment inner same
    cases same
    exact ⟨cycleMeaning, 0, rfl, rfl⟩
  · intro tail
    exact Reaches.one rfl

theorem duplicate_prefix_still_cannot_finish :
    ¬Progress.Terminates (Machine.step parameters)
      ⟨.eval cycleMeaning.environment cycleMeaning.body,
        .force cycleEnvironment (.variable 0) :: purePending⟩ :=
  Machine.not_terminates_append pending_reentry_precludes_finite_body _

end Examples.SuspensionPureHistory
