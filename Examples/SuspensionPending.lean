import Applications.Suspensions.Pending

/-!
# Body entry and pending-write occurrences

An actual first body entry produces one pending address. Reentry into the
same raw thunk can produce two occurrences, even when their caller patterns
differ. The raw transition lemma therefore does not itself promise uniqueness.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionPending
open Suspensions.Core Suspensions.Core.Machine

def parameters : Parameters Unit := ⟨fun _ _ => .stuck .primitive, 0, 1⟩
def body : Expr Unit := .atom (.integer 7)
def memory : Memory Unit := (Suspensions.delay Suspensions.empty body []).1
def firstForce : Config Unit := ⟨memory, .pattern [] (.suspended .wildcard) (.address 0), []⟩
def firstEntered : Config Unit := ⟨memory, .eval [] body, [.memoize 0 [] .wildcard]⟩

theorem first_body_step : step parameters firstForce = .inr firstEntered := rfl

theorem first_body_is_unique : (pendingAddresses firstEntered.stack).Nodup := by
  apply step_pending_nodup (config := firstForce) (parameters := parameters)
  · exact List.nodup_nil
  · intro address _
    exact List.not_mem_nil
  · exact first_body_step

theorem first_body_address : pendingAddresses firstEntered.stack = [0] := rfl

def reenter : Config Unit :=
  ⟨memory, .pattern [] (.suspended .wildcard) (.address 0), [.memoize 0 [] (.variable 4)]⟩
def reentered : Config Unit :=
  ⟨memory, .eval [] body, [.memoize 0 [] .wildcard, .memoize 0 [] (.variable 4)]⟩

theorem raw_reentry_step : step parameters reenter = .inr reentered := rfl

/-- The public provenance result permits this actual push; it does not erase
the earlier occurrence merely because both frames refer to address0. -/
theorem raw_reentry_has_body_provenance :
    PendingTransition (pendingAddresses reenter.stack) (.body 0) (.inr reentered) := by
  have actual := pending_transition parameters reenter
  rw [raw_reentry_step] at actual
  exact actual

theorem raw_reentry_duplicates_address :
    pendingAddresses reentered.stack = [0, 0] ∧
      ¬(pendingAddresses reentered.stack).Nodup := by
  constructor
  · rfl
  · decide

end Examples.SuspensionPending
