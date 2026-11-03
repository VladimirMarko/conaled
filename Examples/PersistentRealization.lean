import Applications.Resources.Persistent.Realization
import Mathlib.Algebra.Group.Nat.Defs

/-!
# Shared-work observations through the existing measured executor

Two operations realize the same debit. With one unit of unshared work each,
their complete charge is three. A pre-realized debit removes only the shared
unit. Composition retains the support produced by the first run.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.PersistentRealization

open Resources Resources.Persistent

private def work (_ : Bool) : Finset Nat := {7}
private def unshared (_ : Bool) : Nat := 1

/-- Public accounting, rather than summing the two realization cardinalities. -/
theorem shared_once :
    (run (realizeStep unshared work) [false, true] ∅).2 = 3 := by
  rw [realize_run_cost]
  decide

theorem final_support :
    (run (realizeStep unshared work) [false, true] ∅).1 = {7} := by
  rw [realize_run_state]
  decide

/-- Initial cached support and unshared costs have distinct effects. -/
theorem already_realized :
    (run (realizeStep unshared work) [false, true] {7}).2 = 2 := by
  have balance := realize_run_identity unshared work [false, true] {7}
  have initial : ({7} : Finset Nat).card = 1 := by decide
  have charges : ([false, true].map unshared).sum = 2 := by decide
  have final : (({7} : Finset Nat) ∪ realizationSupport work [false, true]).card = 1 := by
    decide
  rw [initial, charges, final] at balance
  omega

/-- Public executor composition carries the shared state across the boundary. -/
theorem sequential_charge :
    bind (run (realizeStep unshared work) [false] ∅)
      (run (realizeStep unshared work) [true]) = ({7}, 3) := by
  rw [← run_append (realizeStep unshared work) [false] [true] ∅]
  apply Prod.ext
  · exact final_support
  · exact shared_once

/-- Counting both observations additively would charge the shared unit twice. -/
theorem unique_support_not_additive :
    (work false).card + (work true).card = 2 ∧
      (realizationSupport work [false, true]).card = 1 := by
  constructor <;> decide

/-- Repeated operation labels retain their unshared list multiplicity. -/
theorem repeated_label_keeps_unshared :
    (run (realizeStep unshared work) [false, false] ∅).2 = 3 ∧
      (run (realizeStep unshared work) [false] ∅).2 = 2 := by
  constructor <;> rw [realize_run_cost] <;> decide

private def shift : Nat ↪ Nat :=
  ⟨fun n => n + 10, by intro a b h; exact Nat.add_right_cancel h⟩

/-- Injective renaming changes the debit name while preserving this run's charge. -/
theorem renamed_shared_run :
    run (realizeStep unshared (fun v => (work v).map shift)) [false, true] ∅ = ({17}, 3) := by
  have mapped := realize_run_map shift unshared work [false, true] ∅
  have image : ({7} : Finset Nat).map shift = {17} := by
    rw [Finset.map_singleton]
    rfl
  simpa only [Finset.map_empty, final_support, shared_once, image] using mapped

end Examples.PersistentRealization
