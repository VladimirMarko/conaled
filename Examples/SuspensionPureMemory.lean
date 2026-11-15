import Applications.Suspensions.Pure.Memory
import Examples.SuspensionPureRecurrence

/-!
# Unforced cycles and justified cache contents

A literal delay is valid before its body runs and remains valid after the
actual memoize operation once its two-transition pure evaluation is supplied.
An additional allocation preserves that certificate. A cyclic function/delay
group is also a valid unforced memory, but the proved recurring pure body
prevents any cached value from acquiring a certificate for that meaning.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPureMemory
open Suspensions Suspensions.Pure Suspensions.Pure.Representation Suspensions.Pure.Memory
open Examples.SuspensionPureMachine Examples.SuspensionPureRecurrence

def literalMeaning : Meaning Empty := ⟨integer 7, [], none⟩

def literalWorld : World Empty := Durability.put (fun _ => none) 0 literalMeaning

def literalMemory : Core.Machine.Memory Empty :=
  (Suspensions.delay Suspensions.empty (integer 7) []).1

theorem literal_allocated :
    Durability.Extends (fun _ => none) literalWorld ∧
      StateRep parameters literalWorld literalMemory ∧
      ValueRep literalWorld (.address 0) literalMeaning.value :=
  (StateRep.empty parameters).delay .nil (integer 7)

theorem literal_body :
    Progress.Evaluates (Machine.step parameters)
      (Machine.start literalMeaning.environment literalMeaning.body)
      (.value (.atom (.integer 7))) 2 := .next rfl (.done rfl)

def cachedMemory : Core.Machine.Memory Empty :=
  Suspensions.memoize literalMemory 0 (.atom (.integer 7))

theorem literal_cached : StateRep parameters literalWorld cachedMemory :=
  literal_allocated.2.1.memoize rfl (.atom (.integer 7)) literal_body

theorem cached_entry_justified :
    CellRep parameters literalWorld literalMeaning (.value (.atom (.integer 7))) :=
  literal_cached.lookup (address := 0) rfl rfl

theorem later_allocation_retains_certificate :
    let laterWorld := Durability.put literalWorld 1 (⟨integer 8, [], none⟩ : Meaning Empty)
    StateRep parameters laterWorld (Suspensions.delay cachedMemory (integer 8) []).1 ∧
      CellRep parameters laterWorld literalMeaning (.value (.atom (.integer 7))) := by
  have later := literal_cached.delay .nil (integer 8)
  exact ⟨later.2.1, cached_entry_justified.mono later.1⟩

def cycleTemplate : Core.Env Empty :=
  [(2, .address 0), (1, .closure cycleClauses [] [])]

def cycleMeaning : Meaning Empty := ⟨cycleBody, [], some cycleGroup⟩

def cycleWorld : World Empty := Durability.put (fun _ => none) 0 cycleMeaning

def cycleMemory : Core.Machine.Memory Empty :=
  (Suspensions.delay Suspensions.empty cycleBody (Core.Env.rec cycleTemplate)).1

theorem cycle_template_represented : GroupRep cycleWorld cycleTemplate cycleGroup :=
  .delay rfl (.function .nil (.nil _))

/-- Validity of the pending thunk does not require the impossible body result. -/
theorem cycle_memory_represented : StateRep parameters cycleWorld cycleMemory := by
  refine ⟨Suspensions.delay_bounded Suspensions.bounded_empty _ _, ?_⟩
  intro address meaning found
  by_cases same : address = 0
  · subst address
    have equal : cycleMeaning = meaning := by simpa [cycleWorld, Durability.put] using found
    subst meaning
    refine ⟨_, Suspensions.delay_captures Suspensions.empty cycleBody
      (Core.Env.rec cycleTemplate), .thunk ?_⟩
    exact cycle_template_represented.unroll
  · simp [cycleWorld, Durability.put, same] at found

theorem cyclic_body_cannot_justify_any_cache (value : Core.Value Empty) :
    ¬CellRep parameters cycleWorld cycleMeaning (.value value) :=
  CellRep.no_cache_of_not_terminates cycle_body_has_no_finite_result value

end Examples.SuspensionPureMemory
