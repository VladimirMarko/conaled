import Applications.Suspensions.TraceObservation
import Examples.SuspensionPending

/-!
# Prior trace preservation and the first successful force

The existing first-force configuration takes five actual transitions:
body entry, literal evaluation, cache write, wildcard match and delivery.
The supplied two-event prior log is preserved, while the resource observer
records exactly those five new events in order. The prior log is arbitrary
input to the list instrument; no execution producing it is assumed.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionTraceObservation
open Suspensions.Core Suspensions.Core.Machine
open Examples.SuspensionPending

def priorEvents : List Event := [.referenceWrite 9, .hit 4]

def forceEvents : List Event := [.body 0, .core, .cacheWrite 0, .core, .core]

def forceAnswer : Answer Unit :=
  ⟨Suspensions.memoize memory 0 (.atom (.integer 7)), .matched []⟩

/-- The list instrument observes the actual five-transition machine run,
including its cache write, with a distinguishable nonempty prior log. -/
theorem first_force_trace :
    Progress.Evaluates (tracedStep parameters) (firstForce, priorEvents)
      (forceAnswer, priorEvents ++ forceEvents) 5 :=
  .next rfl (.next rfl (.next rfl (.next rfl (.done rfl))))

/-- Consume the general instrument-agreement theorem rather than compute
the resource observation again. The full memory-bearing answer agrees. -/
theorem first_force_observe_preserves_prior :
    (Suspensions.Core.Observation.observe parameters 5 firstForce).1 = .inl forceAnswer ∧
      priorEvents ++ FreeAddMonoid.toList
        (Suspensions.Core.Observation.observe parameters 5 firstForce).2 =
          priorEvents ++ forceEvents :=
  Suspensions.Core.Observation.traced_evaluates_observe first_force_trace

/-- Cancellation of the supplied two-event prefix exposes exactly the
new body/core/write/core/core order; prior events are not charged again. -/
theorem first_force_observe_order :
    (Suspensions.Core.Observation.observe parameters 5 firstForce).1 = .inl forceAnswer ∧
      FreeAddMonoid.toList
        (Suspensions.Core.Observation.observe parameters 5 firstForce).2 = forceEvents := by
  obtain ⟨finished, recorded⟩ := first_force_observe_preserves_prior
  exact ⟨finished, (List.cons.inj (List.cons.inj recorded).2).2⟩

end Examples.SuspensionTraceObservation
