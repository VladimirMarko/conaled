import Applications.Suspensions.CacheWrite
import Applications.Suspensions.Observation
import Batteries.Data.List.Count

/-!
# Conditional raw accounting of successful cache writes

FreshEntries is a property of actual unfinished observations: each body-entry
address is absent from the current pending-write stack. It is not a purity or
termination assumption, and it does not itself assert a write-count bound.

The count is an additive observation of the existing ordered transition trace.
Bounded memory, initially distinct pending addresses, and fresh body entries
imply at most one successful cache write at any address, for every observation
budget. Finished states contribute no additional events. The pure source
application must discharge the raw hypotheses separately.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Machine
variable {Primitive : Type}

/-- Every actual body entry starts without an older pending write to its
address. Only unfinished states of the existing observer are quantified. -/
def FreshEntries (parameters : Parameters Primitive) (config : Config Primitive) : Prop :=
  ∀ budget next, Prefix.observe parameters budget config = .inr next →
    ∀ address, (transition parameters next).2 = .body address →
      address ∉ pendingAddresses next.stack

theorem FreshEntries.current {parameters : Parameters Primitive} {config : Config Primitive}
    (fresh : FreshEntries parameters config) :
    ∀ address, (transition parameters config).2 = .body address →
      address ∉ pendingAddresses config.stack :=
  fresh 0 config rfl

/-- An actual next transition shifts every later prefix by one step. -/
theorem FreshEntries.after_step {parameters : Parameters Primitive} {config next : Config Primitive}
    (fresh : FreshEntries parameters config) (moved : step parameters config = .inr next) :
    FreshEntries parameters next := by
  intro budget later reached address event
  apply fresh (budget + 1) later _ address event
  rw [Prefix.observe_succ, moved]
  exact reached

/-- Distinctness follows along actual prefixes from fresh pushes and removal
of pending occurrences. Bounded memory is not needed for this stack fact. -/
theorem FreshEntries.observe_pending_nodup {parameters : Parameters Primitive}
    {config next : Config Primitive} {budget : Nat}
    (fresh : FreshEntries parameters config) (distinct : (pendingAddresses config.stack).Nodup)
    (reached : Prefix.observe parameters budget config = .inr next) :
    (pendingAddresses next.stack).Nodup := by
  induction budget generalizing config with
  | zero =>
      have same : config = next := Sum.inr.inj reached
      simpa only [same] using distinct
  | succ budget ih =>
      cases moved : step parameters config with
      | inl answer =>
          rw [Prefix.observe_succ, moved, Prefix.iterate_answer] at reached
          cases reached
      | inr later =>
          rw [Prefix.observe_succ, moved] at reached
          exact ih (fresh.after_step moved)
            (step_pending_nodup distinct fresh.current moved) reached

end Suspensions.Core.Machine

namespace Suspensions.Core.Observation
open Machine
variable {Primitive : Type}

/-- Count actual successful writes to one physical address in the existing
free additive event trace. Equal bodies at different addresses stay distinct. -/
def cacheWrites (address : Nat) : FreeAddMonoid Event →+ Nat where
  toFun events := (FreeAddMonoid.toList events).count (.cacheWrite address)
  map_zero' := rfl
  map_add' first second := by
    simp only [FreeAddMonoid.toList_add, List.count_append]

theorem cacheWrites_eq_count (address : Nat) (events : FreeAddMonoid Event) :
    cacheWrites address events = (FreeAddMonoid.toList events).count (.cacheWrite address) := rfl

@[simp] theorem cacheWrites_of (address : Nat) (event : Event) :
    cacheWrites address (FreeAddMonoid.of event) =
      if event = .cacheWrite address then 1 else 0 := by
  change ([event] : List Event).count (.cacheWrite address) = _
  exact List.count_singleton' (.cacheWrite address) event

/-- This ordinary trace count is also the resource framework's additive
reweighting by the indicator of the selected event. -/
theorem cacheWrites_eq_lift (address : Nat) :
    cacheWrites address =
      FreeAddMonoid.lift (fun event => if event = .cacheWrite address then 1 else 0) := by
  apply FreeAddMonoid.hom_eq
  intro event
  rw [cacheWrites_of, FreeAddMonoid.lift_eval_of]

@[simp] theorem cacheWrites_workload_finished (parameters : Parameters Primitive)
    (budget address : Nat) (answer : Answer Primitive) :
    cacheWrites address (workload parameters budget (.inl answer)).2 = 0 := by
  rw [workload_finished]
  exact map_zero _

@[simp] theorem cacheWrites_observe_zero (parameters : Parameters Primitive)
    (config : Config Primitive) (address : Nat) :
    cacheWrites address (observe parameters 0 config).2 = 0 := rfl

/-- One actual transition contributes its event, then the existing workload
continues from that transition's result. Answers are absorbing. -/
theorem cacheWrites_observe_succ (parameters : Parameters Primitive) (budget address : Nat)
    (config : Config Primitive) :
    cacheWrites address (observe parameters (budget + 1) config).2 =
      cacheWrites address (FreeAddMonoid.of (transition parameters config).2) +
        cacheWrites address (workload parameters budget (step parameters config)).2 := by
  rw [observe, workload_succ, measuredAdvance_running]
  change cacheWrites address
    (FreeAddMonoid.of (transition parameters config).2 +
      (workload parameters budget (step parameters config)).2) = _
  exact map_add _ _ _

/-- Finished suffixes change neither the recorded events nor their count. -/
theorem cacheWrites_observe_after_finished {parameters : Parameters Primitive}
    {config : Config Primitive} {answer : Answer Primitive} {budget : Nat}
    (finished : Prefix.observe parameters budget config = .inl answer) (extra address : Nat) :
    cacheWrites address (observe parameters (budget + extra) config).2 =
      cacheWrites address (observe parameters budget config).2 := by
  have erased : (workload parameters budget (.inr config)).1 = .inl answer :=
    (observe_erases parameters budget config).trans finished
  rw [observe, workload_append]
  change cacheWrites address
      ((workload parameters budget (.inr config)).2 +
        (workload parameters extra (workload parameters budget (.inr config)).1).2) = _
  rw [erased, workload_finished]
  simp only [observe, add_zero]

/-- Increasing the observation budget appends actual events or an empty
finished suffix. Counting the selected event can therefore only increase. -/
theorem cacheWrites_observe_mono (parameters : Parameters Primitive) (config : Config Primitive)
    {first second : Nat} (bound : first ≤ second) (address : Nat) :
    cacheWrites address (observe parameters first config).2 ≤
      cacheWrites address (observe parameters second config).2 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bound
  change cacheWrites address (workload parameters first (.inr config)).2 ≤
    cacheWrites address (workload parameters (first + extra) (.inr config)).2
  rw [workload_append]
  change cacheWrites address (workload parameters first (.inr config)).2 ≤
    cacheWrites address
      ((workload parameters first (.inr config)).2 +
        (workload parameters extra (workload parameters first (.inr config)).1).2)
  rw [map_add]
  exact Nat.le_add_right _ _

/-- An actual completed zero-write observation supplies zero at every budget:
earlier prefixes have no more events, and later suffixes are absorbing. -/
theorem cacheWrites_observe_zero_of_finished {parameters : Parameters Primitive}
    {config : Config Primitive} {answer : Answer Primitive} {completed address : Nat}
    (finished : Prefix.observe parameters completed config = .inl answer)
    (zero : cacheWrites address (observe parameters completed config).2 = 0) (budget : Nat) :
    cacheWrites address (observe parameters budget config).2 = 0 := by
  by_cases before : budget ≤ completed
  · apply Nat.eq_zero_of_le_zero
    exact (cacheWrites_observe_mono parameters config before address).trans (Nat.le_of_eq zero)
  · have after : completed ≤ budget := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le after
    rw [cacheWrites_observe_after_finished finished extra address]
    exact zero

/-- Once a value cell has no pending frame at its address, every future
budget has zero successful writes there. Payload constancy is not asserted. -/
theorem cacheWrites_observe_settled {parameters : Parameters Primitive} {config : Config Primitive}
    {address : Nat} (valid : ConfigBounded config) (settled : Settled address config) (budget : Nat) :
    cacheWrites address (observe parameters budget config).2 = 0 := by
  induction budget generalizing config with
  | zero => rfl
  | succ budget ih =>
      rw [cacheWrites_observe_succ, cacheWrites_of,
        ite_eq_right settled.no_cacheWrite, zero_add]
      cases moved : step parameters config with
      | inl answer => exact cacheWrites_workload_finished parameters budget address answer
      | inr next =>
          have bounded := step_bounded (parameters := parameters) valid
          have kept := step_settled (parameters := parameters) valid.1 settled
          rw [moved] at bounded kept
          exact ih bounded kept

/-- Conditional raw bound on the actual trace. Its hypotheses do not assume
purity, finite completion, a body-entry count, or the desired write bound. -/
theorem cacheWrites_observe_le_one {parameters : Parameters Primitive} {config : Config Primitive}
    (valid : ConfigBounded config) (distinct : (pendingAddresses config.stack).Nodup)
    (fresh : FreshEntries parameters config) (address budget : Nat) :
    cacheWrites address (observe parameters budget config).2 ≤ 1 := by
  induction budget generalizing config with
  | zero => exact Nat.zero_le 1
  | succ budget ih =>
      rw [cacheWrites_observe_succ]
      by_cases event : (transition parameters config).2 = .cacheWrite address
      · obtain ⟨next, moved, settled⟩ := cacheWrite_settles distinct event
        have bounded := step_bounded (parameters := parameters) valid
        rw [moved] at bounded
        rw [cacheWrites_of, ite_eq_left event, moved]
        change 1 + cacheWrites address (observe parameters budget next).2 ≤ 1
        rw [cacheWrites_observe_settled bounded settled budget, add_zero]
      · rw [cacheWrites_of, ite_eq_right event, zero_add]
        cases moved : step parameters config with
        | inl answer =>
            rw [cacheWrites_workload_finished]
            exact Nat.zero_le 1
        | inr next =>
            have bounded := step_bounded (parameters := parameters) valid
            rw [moved] at bounded
            exact ih bounded (step_pending_nodup distinct fresh.current moved)
              (fresh.after_step moved)

end Suspensions.Core.Observation
