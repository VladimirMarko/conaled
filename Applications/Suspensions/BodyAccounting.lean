import Applications.Suspensions.CacheAccounting
import Applications.Suspensions.EventCounts
import Applications.Suspensions.PendingRetention

/-!
# Conditional counting of actual suspension-body entries

FreshEntries excludes entering an address while its earlier body is pending.
NoMemoizeUnwind separately excludes abandoning that address's pending body by
exceptional unwinding. Bounded memory preserves a value cell after a successful
return. Together these facts prevent a second body-entry event at that address.

The bound covers every finite observation budget, including unfinished and
faulting runs. It is a count of entries, not a bound on work performed inside
each body. Pure finite normal return does not imply NoMemoizeUnwind.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Machine
variable {Primitive : Type}

/-- No actual unfinished prefix abandons the selected memoize frame while
propagating an exception. Other addresses and locally caught exceptions remain
unrestricted. -/
def NoMemoizeUnwind (parameters : Parameters Primitive) (config : Config Primitive)
    (address : Nat) : Prop :=
  ∀ budget next, Prefix.observe parameters budget config = .inr next →
    ¬ UnwindsMemoize address next

theorem NoMemoizeUnwind.current {parameters : Parameters Primitive}
    {config : Config Primitive} {address : Nat}
    (safe : NoMemoizeUnwind parameters config address) : ¬ UnwindsMemoize address config :=
  safe 0 config rfl

theorem NoMemoizeUnwind.after_step {parameters : Parameters Primitive}
    {config next : Config Primitive} {address : Nat}
    (safe : NoMemoizeUnwind parameters config address)
    (moved : step parameters config = .inr next) : NoMemoizeUnwind parameters next address := by
  intro budget later reached
  apply safe (budget + 1) later
  rw [Prefix.observe_succ, moved]
  exact reached

/-- A finite actual completion reduces this prefix property to the preceding
unfinished observations. Larger budgets are absorbing, not additional runs. -/
theorem NoMemoizeUnwind.of_finished {parameters : Parameters Primitive}
    {config : Config Primitive} {answer : Answer Primitive} {count address : Nat}
    (finished : Prefix.observe parameters count config = .inl answer)
    (safe : ∀ index, index < count → ∀ next,
      Prefix.observe parameters index config = .inr next → ¬ UnwindsMemoize address next) :
    NoMemoizeUnwind parameters config address := by
  intro index next reached
  by_cases before : index < count
  · exact safe index before next reached
  · have after : count ≤ index := Nat.le_of_not_gt before
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le after
    have ended := Prefix.stays_finished parameters count extra config answer finished
    rw [ended] at reached
    cases reached

/-- Either a retained value cell or an older pending frame precludes this
body event when the actual entry is fresh. No pending multiplicity is assumed. -/
theorem PendingOrValue.no_body {parameters : Parameters Primitive}
    {config : Config Primitive} {address : Nat}
    (present : PendingOrValue address config) (fresh : FreshEntries parameters config) :
    (transition parameters config).2 ≠ .body address := by
  intro event
  rcases present with cached | pending
  · exact hasValue_no_body cached event
  · exact fresh.current address event pending

end Suspensions.Core.Machine

namespace Suspensions.Core.Observation
open Machine
variable {Primitive : Type}

/-- The actual ordered body-entry count at one physical address. -/
def bodyEntries (address : Nat) : FreeAddMonoid Event →+ Nat := eventCount (.body address)

theorem bodyEntries_eq_count (address : Nat) (events : FreeAddMonoid Event) :
    bodyEntries address events = (FreeAddMonoid.toList events).count (.body address) := rfl

/-- The older successful-write observation is the corresponding selected-event
projection; its original implementation and public results are unchanged. -/
theorem cacheWrites_eq_eventCount (address : Nat) :
    cacheWrites address = eventCount (.cacheWrite address) := rfl

/-- Once an address has a pending body or value cell, the two distinct prefix
conditions prevent any later body entry there. Finished answers need no stack. -/
theorem bodyEntries_observe_zero_of_pending_or_value {parameters : Parameters Primitive}
    {config : Config Primitive} {address : Nat}
    (valid : ConfigBounded config) (fresh : FreshEntries parameters config)
    (noUnwind : NoMemoizeUnwind parameters config address)
    (present : PendingOrValue address config) (budget : Nat) :
    bodyEntries address (observe parameters budget config).2 = 0 := by
  change eventCount (.body address) (observe parameters budget config).2 = 0
  induction budget generalizing config with
  | zero => rfl
  | succ budget ih =>
      rw [eventCount_observe_succ, eventCount_of,
        ite_eq_right (present.no_body fresh), zero_add]
      cases moved : step parameters config with
      | inl answer => exact eventCount_workload_finished parameters budget (.body address) answer
      | inr next =>
          have bounded := step_bounded (parameters := parameters) valid
          have kept := step_pending_or_value (parameters := parameters) valid.1 present noUnwind.current
          rw [moved] at bounded kept
          exact ih bounded (fresh.after_step moved) (noUnwind.after_step moved) kept

/-- A first actual entry establishes a pending frame. Its future zero count
gives at most one entry for every budget. No initial Nodup or termination
premise is used by this raw conditional theorem. -/
theorem bodyEntries_observe_le_one {parameters : Parameters Primitive}
    {config : Config Primitive} {address : Nat}
    (valid : ConfigBounded config) (fresh : FreshEntries parameters config)
    (noUnwind : NoMemoizeUnwind parameters config address) (budget : Nat) :
    bodyEntries address (observe parameters budget config).2 ≤ 1 := by
  change eventCount (.body address) (observe parameters budget config).2 ≤ 1
  induction budget generalizing config with
  | zero => exact Nat.zero_le 1
  | succ budget ih =>
      rw [eventCount_observe_succ]
      by_cases event : (transition parameters config).2 = .body address
      · obtain ⟨next, moved, pending⟩ := body_entry_pending event
        have bounded := step_bounded (parameters := parameters) valid
        rw [moved] at bounded
        rw [eventCount_of, ite_eq_left event, moved]
        change 1 + bodyEntries address (observe parameters budget next).2 ≤ 1
        rw [bodyEntries_observe_zero_of_pending_or_value bounded
          (fresh.after_step moved) (noUnwind.after_step moved) (Or.inr pending) budget, add_zero]
      · rw [eventCount_of, ite_eq_right event, zero_add]
        cases moved : step parameters config with
        | inl answer =>
            rw [eventCount_workload_finished]
            exact Nat.zero_le 1
        | inr next =>
            have bounded := step_bounded (parameters := parameters) valid
            rw [moved] at bounded
            exact ih bounded (fresh.after_step moved) (noUnwind.after_step moved)

end Suspensions.Core.Observation
