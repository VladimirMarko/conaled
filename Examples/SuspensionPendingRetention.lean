import Applications.Suspensions.PendingRetention
import Applications.Suspensions.CacheAccounting
import Examples.SuspensionPending

/-!
# Retention, return and exceptional loss of an actual pending frame

The existing literal suspension supplies a first body entry before any cache
write. An ordinary constructor frame above its memoize frame preserves the
pending address. Returning through memoize writes 7; raising through that same
frame removes it while leaving the thunk unforced. Raw reentry and duplicate
frames remain separate from exceptional unwind.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPendingRetention
open Suspensions.Core Suspensions.Core.Machine
open Examples.SuspensionPending

private theorem literal_bounded : Suspensions.Bounded memory :=
  Suspensions.delay_bounded Suspensions.bounded_empty body []

private theorem unforced_is_not_value : ¬ HasValue memory 0 := by
  rintro ⟨value, stored⟩
  have thunk : memory.memory 0 = some (.thunk body []) := rfl
  rw [thunk] at stored
  cases stored

/-- The public body-origin law connects the actual first transition to its
pending frame. The same transition has not written a cache value. -/
theorem first_entry_establishes_pending :
    0 ∈ pendingAddresses firstEntered.stack ∧
    (transition parameters firstForce).2 = .body 0 ∧
    (transition parameters firstForce).2 ≠ .cacheWrite 0 := by
  have event : (transition parameters firstForce).2 = .body 0 := rfl
  obtain ⟨next, moved, pending⟩ := body_entry_pending event
  have same : next = firstEntered := Sum.inr.inj (moved.symm.trans first_body_step)
  subst next
  exact ⟨pending, event, by intro written; cases written⟩

/-- One observed transition is an unfinished body entry, not a completed
evaluation or a cache write. The original thunk cell is still present. -/
theorem first_prefix_before_cache :
    (Suspensions.Core.Observation.observe parameters 1 firstForce).1 = .inr firstEntered ∧
    FreeAddMonoid.toList (Suspensions.Core.Observation.observe parameters 1 firstForce).2 =
      [.body 0] ∧
    PendingOrValue 0 firstEntered ∧ ¬ HasValue firstEntered.memory 0 := by
  exact ⟨rfl, rfl, Or.inr first_entry_establishes_pending.1, unforced_is_not_value⟩

private def wrapped : Config Unit :=
  ⟨memory, .value (.atom (.integer 7)), [.constructor 9, .memoize 0 [] .wildcard]⟩

private def afterConstructor : Config Unit :=
  ⟨memory, .value (.constructor 9 (some (.atom (.integer 7)))), [.memoize 0 [] .wildcard]⟩

/-- The ordinary top frame disappears, but the deeper memoize frame is retained.
The new public classification rules out its other two alternatives here. -/
theorem ordinary_prefix_retains_pending :
    step parameters wrapped = .inr afterConstructor ∧
    0 ∈ pendingAddresses afterConstructor.stack := by
  have moved : step parameters wrapped = .inr afterConstructor := rfl
  have pending : 0 ∈ pendingAddresses wrapped.stack := by
    simp [wrapped, pendingAddresses, Frame.memoizeAddress]
  have noUnwind : ¬ UnwindsMemoize 0 wrapped := by simp [UnwindsMemoize, wrapped]
  refine ⟨moved, ?_⟩
  rcases pending_mem_after_step pending moved with retained | written | unwound
  · exact retained
  · cases written
  · exact False.elim (noUnwind unwound)

private def returning : Config Unit :=
  ⟨memory, .value (.atom (.integer 7)), [.memoize 0 [] .wildcard]⟩

private def afterWrite : Config Unit :=
  ⟨Suspensions.memoize memory 0 (.atom (.integer 7)),
    .pattern [] .wildcard (.atom (.integer 7)), []⟩

/-- Removing this pending frame under value control is the actual successful
write alternative. The same step changes pending protection to a value cell. -/
theorem normal_return_writes_and_preserves :
    step parameters returning = .inr afterWrite ∧
    (transition parameters returning).2 = .cacheWrite 0 ∧
    pendingAddresses afterWrite.stack = [] ∧ HasValue afterWrite.memory 0 := by
  have moved : step parameters returning = .inr afterWrite := rfl
  have pending : 0 ∈ pendingAddresses returning.stack := by simp [returning]
  have noUnwind : ¬ UnwindsMemoize 0 returning := by simp [UnwindsMemoize, returning]
  have write : (transition parameters returning).2 = .cacheWrite 0 := by
    rcases pending_mem_after_step pending moved with retained | written | unwound
    · exact False.elim (List.not_mem_nil retained)
    · exact written
    · exact False.elim (noUnwind unwound)
  have kept := step_pending_or_value (parameters := parameters) literal_bounded
    (Or.inr pending : PendingOrValue 0 returning) noUnwind
  rw [moved] at kept
  have value : HasValue afterWrite.memory 0 := by
    rcases kept with present | retained
    · exact present
    · exact False.elim (List.not_mem_nil retained)
  exact ⟨moved, write, rfl, value⟩

private def unwinding : Config Unit :=
  ⟨memory, .raised (.exception 42 none), [.memoize 0 [] .wildcard]⟩

private def afterUnwind : Config Unit := ⟨memory, .raised (.exception 42 none), []⟩

/-- Raised control discards the frame without writing its thunk. The exact
unwind alternative is obtained from the public classification, and the
pending-or-value conclusion would be false without excluding this case. -/
theorem exceptional_unwind_loses_protection :
    step parameters unwinding = .inr afterUnwind ∧
    UnwindsMemoize 0 unwinding ∧
    (transition parameters unwinding).2 = .core ∧
    pendingAddresses afterUnwind.stack = [] ∧ ¬ PendingOrValue 0 afterUnwind := by
  have moved : step parameters unwinding = .inr afterUnwind := rfl
  have pending : 0 ∈ pendingAddresses unwinding.stack := by simp [unwinding]
  have unwound : UnwindsMemoize 0 unwinding := by
    rcases pending_mem_after_step pending moved with retained | written | unwound
    · exact False.elim (List.not_mem_nil retained)
    · cases written
    · exact unwound
  refine ⟨moved, unwound, rfl, rfl, ?_⟩
  rintro (value | retained)
  · exact unforced_is_not_value value
  · exact List.not_mem_nil retained

/-- An actual active-address entry is a freshness failure, although no raised
control or exceptional unwind occurs. It is not the retry failure mode above. -/
theorem active_entry_fails_freshness :
    ¬ FreshEntries parameters reenter ∧ ¬ UnwindsMemoize 0 reenter := by
  constructor
  · intro fresh
    exact fresh.current 0 rfl (by simp [reenter])
  · simp [UnwindsMemoize, reenter]

private def duplicateReturn : Config Unit :=
  ⟨memory, .value (.atom (.integer 7)),
    [.memoize 0 [] .wildcard, .memoize 0 [] (.variable 4)]⟩

/-- The initial configuration here already has two occurrences. The new
preservation law requires membership, not a distinctness assumption. -/
theorem duplicate_pending_is_allowed :
    ¬ (pendingAddresses reentered.stack).Nodup ∧
    step parameters reentered = .inr duplicateReturn ∧
    PendingOrValue 0 duplicateReturn := by
  have moved : step parameters reentered = .inr duplicateReturn := rfl
  have pending : 0 ∈ pendingAddresses reentered.stack := by simp [reentered]
  have noUnwind : ¬ UnwindsMemoize 0 reentered := by simp [UnwindsMemoize, reentered]
  have kept := step_pending_or_value (parameters := parameters) literal_bounded
    (Or.inr pending : PendingOrValue 0 reentered) noUnwind
  rw [moved] at kept
  exact ⟨raw_reentry_duplicates_address.2, moved, kept⟩

end Examples.SuspensionPendingRetention
