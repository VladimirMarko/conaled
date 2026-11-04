import Applications.Resources.ListCalls
import Applications.Resources.ListReversal

/-! Checked Appendix B.1 clients, with independently calculated callback and
traversal counts. The examples use the public value/count results rather than
depending on recursive proof construction.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ListCalls
open Resources.ListCalls
universe u v

theorem duplicate_map :
    mapRun (fun x : Nat => (x + 10, x)) [2, 2, 3] = ([12, 12, 13], 11) := by
  rw [mapRun_exact]
  rfl

theorem discarded_last :
    filterRun (fun x : Nat => (decide (x ≤ 2), x)) [2, 2, 3] = ([2, 2], 11) := by
  rw [filterRun_exact]
  rfl

theorem discarded_head :
    filterRun (fun x : Nat => (decide (x ≤ 2), x)) [3, 2, 2] = ([2, 2], 11) := by
  rw [filterRun_exact]
  rfl

theorem zero_and_unit_callbacks :
    (mapRun (fun x : Nat => (x + 10, 0)) [2, 2, 3]).2 = 4 ∧
    (mapRun (fun x : Nat => (x + 10, 1)) [2, 2, 3]).2 = 7 := by
  constructor
  · exact mapRun_cost_of_constant _ _ 0 (by intros; rfl)
  · exact mapRun_cost_of_constant _ _ 1 (by intros; rfl)

theorem discarded_values_still_pay :
    (filterRun (fun _ : Nat => (false, 1)) [2, 2, 3]).2 = 7 :=
  filterRun_cost_of_constant _ _ 1 (by intros; rfl)

/-- This composes measured callbacks, map, and length across arbitrary payload
universes. Length is charged after observing the actual mapped output.
-/
theorem map_then_length {α : Type u} {β : Type v}
    (f : α → Resources.Measured β Nat) (xs : List α) :
    Resources.bind (mapRun f xs) Resources.SymmetricCosts.lengthRun =
      (xs.length, (xs.map (fun x => (f x).2)).sum + 2 * xs.length + 2) := by
  simp only [Resources.bind, Resources.SymmetricCosts.lengthRun_exact,
    mapRun_value, mapRun_cost, List.length_map]
  congr 1
  omega

theorem composed_callback_count :
    Resources.bind (mapRun (fun x : Nat => (x + 10, x)) [2, 2, 3])
      Resources.SymmetricCosts.lengthRun = (3, 15) := by
  rw [map_then_length]
  rfl

/-- Append counts the left list, including its final empty invocation; the
right list's length is irrelevant to this operation's traversal count.
-/
theorem append_then_length {α : Type u} (xs ys : List α) :
    Resources.bind (Resources.ListReversal.appendRun xs ys)
      Resources.SymmetricCosts.lengthRun =
      (xs.length + ys.length, 2 * xs.length + ys.length + 2) := by
  simp only [Resources.bind, Resources.ListReversal.appendRun_exact,
    Resources.SymmetricCosts.lengthRun_exact, List.length_append]
  congr 1
  omega

theorem valid_lookup : lookupRun [4, 4, 9] 2 = (some 9, 3) := by
  simpa using lookupRun_valid [4, 4, 9] 2 (by decide)

/-- Invalid-input counts are properties of the declared optional extension. -/
theorem first_invalid_lookup : lookupRun [4, 4, 9] 3 = (none, 4) := by
  apply Prod.ext
  · rw [lookupRun_value]
    rfl
  · rw [lookupRun_cost]
    rfl

theorem farther_invalid_lookup : lookupRun [4, 4, 9] 20 = (none, 4) := by
  apply Prod.ext
  · rw [lookupRun_value]
    rfl
  · rw [lookupRun_cost]
    rfl

theorem empty_payload_lookup : lookupRun ([] : List Empty) 20 = (none, 1) :=
  lookupRun_nil 20

theorem take_drop_values :
    takeRun 2 [1, 2, 3] = ([1, 2], 3) ∧
    dropRun 2 [1, 2, 3] = ([3], 3) := by
  constructor
  · rw [takeRun_exact]
    rfl
  · rw [dropRun_exact]
    rfl

theorem separate_vs_fused :
    Resources.bind (takeRun 2 [1, 2, 3]) (fun taken =>
      Resources.bind (dropRun 2 [1, 2, 3]) (fun dropped => Resources.pure (taken, dropped))) =
        (([1, 2], [3]), 6) ∧
    Resources.SymmetricCosts.splitRun 2 [1, 2, 3] = (([1, 2], [3]), 3) := by
  constructor
  · rw [take_drop_separate, Resources.SymmetricCosts.splitRun_value,
      Resources.SymmetricCosts.splitRun_work]
    rfl
  · apply Prod.ext
    · exact Resources.SymmetricCosts.splitRun_value 2 [1, 2, 3]
    · exact Resources.SymmetricCosts.splitRun_work 2 [1, 2, 3]

theorem zero_and_overlarge :
    takeRun 0 [1, 2, 3] = ([], 1) ∧ dropRun 0 [1, 2, 3] = ([1, 2, 3], 1) ∧
    takeRun 20 [1, 2, 3] = ([1, 2, 3], 4) ∧ dropRun 20 [1, 2, 3] = ([], 4) := by
  simp [takeRun_exact, dropRun_exact]

theorem empty_payload_split (k : Nat) :
    takeRun k ([] : List Empty) = ([], 1) ∧
    dropRun k ([] : List Empty) = ([], 1) :=
  ⟨takeRun_nil k, dropRun_nil k⟩

end Examples.ListCalls
