import Applications.Suspensions.BodyRealization
import Examples.SuspensionPureBodyCounts

/-!
# Actual source observations connected to shared body debits

The public source body-count theorems establish nonrepetition for every budget
in three successful programs. Their independently expected completed body lists
are [0], [0, 1] and [0]. The unchanged debit interpreter therefore charges 1, 2
and 1. The finite pure external-handler retry retains [0, 0]: two entries, one
distinct identity and one shared-debit charge, with no writes and no hits.

These are body-entry observations, not total execution-work claims.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionBodyRealization
open Suspensions Suspensions.Core.Observation Resources.Persistent

namespace Repeated

/-- The event component of the existing repeated-force source execution. -/
abbrev events (budget : Nat) : FreeAddMonoid Core.Machine.Event :=
  (observe SuspensionPureBodyCounts.rawParameters budget
    (Core.Machine.start Suspensions.empty [] SuspensionPureBodyCounts.Repeated.program)).2

/-- This applies the public source count bound, which already discharges
freshness and proves the separate no-unwind premise. -/
theorem all_nodup (budget : Nat) : (bodyAddresses (events budget)).Nodup := by
  apply (bodyAddresses_nodup_iff _).mpr
  intro address
  simpa only [bodyEntries_eq_count] using
    SuspensionPureBodyCounts.Repeated.all_counts address budget

theorem all_budgets (budget : Nat) :
    (Resources.run (realizeStep (fun _ => 0) bodyDebits)
      (FreeAddMonoid.toList (events budget)) ∅).2 = totalBodyEntries (events budget) :=
  body_realization_cost_of_nodup (all_nodup budget)

/-- One first force enters address zero; the second force is a hit. -/
theorem body_addresses : bodyAddresses (events 21) = [0] := rfl

theorem completed_charge :
    (Resources.run (realizeStep (fun _ => 0) bodyDebits)
      (FreeAddMonoid.toList (events 21)) ∅).2 = 1 := by
  simpa only [totalBodyEntries_eq_length, body_addresses, List.length_cons, List.length_nil]
    using all_budgets 21

end Repeated

namespace Distinct

abbrev events (budget : Nat) : FreeAddMonoid Core.Machine.Event :=
  (observe SuspensionPureBodyCounts.rawParameters budget
    (Core.Machine.start Suspensions.empty [] SuspensionPureBodyCounts.Distinct.program)).2

theorem all_budgets (budget : Nat) :
    (Resources.run (realizeStep (fun _ => 0) bodyDebits)
      (FreeAddMonoid.toList (events budget)) ∅).2 = totalBodyEntries (events budget) :=
  body_realization_cost_of_counts
    (fun address => SuspensionPureBodyCounts.Distinct.all_budgets address budget)

/-- Actual allocation identity survives the projection despite equal code. -/
theorem body_addresses : bodyAddresses (events 34) = [0, 1] := rfl

theorem identical_thunks_distinct_charge :
    (∃ config, Core.Prefix.observe SuspensionPureBodyCounts.rawParameters 6
      (Core.Machine.start Suspensions.empty [] SuspensionPureBodyCounts.Distinct.program) =
        .inr config ∧
      config.memory.memory 0 = some (.thunk (.atom (.integer 7)) []) ∧
      config.memory.memory 1 = some (.thunk (.atom (.integer 7)) []) ∧
      config.memory.next = 2) ∧
    bodyAddresses (events 34) = [0, 1] ∧
    (Resources.run (realizeStep (fun _ => 0) bodyDebits)
      (FreeAddMonoid.toList (events 34)) ∅).2 = 2 := by
  refine ⟨SuspensionPureBodyCounts.Distinct.identical_thunks_separate_entries.1,
    body_addresses, ?_⟩
  simpa only [totalBodyEntries_eq_length, body_addresses, List.length_cons, List.length_nil]
    using all_budgets 34

end Distinct

namespace InternalHandler

abbrev events (budget : Nat) : FreeAddMonoid Core.Machine.Event :=
  (observe SuspensionPureBodyCounts.rawParameters budget
    (Core.Machine.start Suspensions.empty SuspensionPureBodyCounts.InternalHandler.rawCapture
      SuspensionPureBodyCounts.InternalHandler.program)).2

/-- The source theorem permits the body's own handler to catch its exception;
its no-unwind premise forbids abandoning the memoize frame, not raising. -/
theorem all_budgets (budget : Nat) :
    (Resources.run (realizeStep (fun _ => 0) bodyDebits)
      (FreeAddMonoid.toList (events budget)) ∅).2 = totalBodyEntries (events budget) :=
  body_realization_cost_of_counts
    (fun address => SuspensionPureBodyCounts.InternalHandler.all_budgets address budget)

theorem body_addresses : bodyAddresses (events 30) = [0] := rfl

theorem completed_charge :
    (Resources.run (realizeStep (fun _ => 0) bodyDebits)
      (FreeAddMonoid.toList (events 30)) ∅).2 = 1 := by
  simpa only [totalBodyEntries_eq_length, body_addresses, List.length_cons, List.length_nil]
    using all_budgets 30

end InternalHandler

namespace ExternalHandler

abbrev events (budget : Nat) : FreeAddMonoid Core.Machine.Event :=
  (observe SuspensionPureBodyCounts.rawParameters budget
    (Core.Machine.start Suspensions.empty SuspensionPureBodyCounts.ExternalHandler.rawCapture
      SuspensionPureBodyCounts.ExternalHandler.program)).2

/-- The original fifty-step execution abandons and retries the same address. -/
theorem body_addresses : bodyAddresses (events 50) = [0, 0] := rfl

/-- The actual two-entry observation contradicts the necessary count
consequence of Nodup. Successful-write uniqueness cannot repair this premise. -/
theorem not_nodup : ¬ (bodyAddresses (events 50)).Nodup := by
  intro unique
  have bound := (bodyAddresses_nodup_iff (events 50)).mp unique 0
  have actual : bodyEntries 0 (events 50) = 2 :=
    SuspensionPureBodyCounts.ExternalHandler.two_attempts_without_write.1
  rw [actual] at bound
  omega

/-- Occurrences differ from support and debit charge in the unchanged source
counterexample. Its body/write/hit counts remain exactly two/zero/zero. -/
theorem retry_separates_occurrences_and_support :
    totalBodyEntries (events 50) = 2 ∧
    (bodyAddresses (events 50)).toFinset.card = 1 ∧
    (Resources.run (realizeStep (fun _ => 0) bodyDebits)
      (FreeAddMonoid.toList (events 50)) ∅).2 = 1 ∧
    (FreeAddMonoid.toList (events 50)).count (.body 0) = 2 ∧
    (FreeAddMonoid.toList (events 50)).count (.cacheWrite 0) = 0 ∧
    (FreeAddMonoid.toList (events 50)).count (.hit 0) = 0 := by
  refine ⟨?_, ?_, ?_, SuspensionPureBodyCounts.ExternalHandler.two_attempts_without_write⟩
  · rw [totalBodyEntries_eq_length, body_addresses]
  · simp [body_addresses]
  · simpa [body_addresses] using body_realization_cost (events 50)

/-- Finite pure normal return does not discharge the missing no-unwind premise. -/
theorem no_unwind_fails :
    ¬ Core.Machine.NoMemoizeUnwind SuspensionPureBodyCounts.rawParameters
      (Core.Machine.start Suspensions.empty SuspensionPureBodyCounts.ExternalHandler.rawCapture
        SuspensionPureBodyCounts.ExternalHandler.program) 0 :=
  SuspensionPureBodyCounts.ExternalHandler.no_unwind_fails

end ExternalHandler

end Examples.SuspensionBodyRealization
