import Applications.Search.OrderedMap.Basic

/-! Finite-map clients exercise overwrite, absence, arbitrary payloads and
composition through the public observation laws. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.OrderedMap
open Search.OrderedMap

private def changes : List (Nat × Option Nat) :=
  [(2, some 7), (1, none), (2, some 9)]

private def snapshot : Tree Nat (Option Nat) :=
  bindAll (trees Nat (Option Nat)) changes (trees Nat (Option Nat)).empty

/-- Later binding of the same key replaces the earlier payload. -/
theorem overwritten : (trees Nat (Option Nat)).lookup 2 snapshot = some (some 9) := by
  have h := (trees_laws (κ := Nat) (ν := Option Nat)).lookup_bindAll
    changes (trees Nat (Option Nat)).empty 2
  rw [(trees_laws (κ := Nat) (ν := Option Nat)).empty] at h
  simpa [snapshot, changes, writeAll, write] using h

/-- Stored `none` is a successful lookup, distinct from missing-key failure. -/
theorem present_none : (trees Nat (Option Nat)).lookup 1 snapshot = some none := by
  have h := (trees_laws (κ := Nat) (ν := Option Nat)).lookup_bindAll
    changes (trees Nat (Option Nat)).empty 1
  rw [(trees_laws (κ := Nat) (ν := Option Nat)).empty] at h
  simpa [snapshot, changes, writeAll, write] using h

theorem absent : (trees Nat (Option Nat)).lookup 3 snapshot = none := by
  have h := (trees_laws (κ := Nat) (ν := Option Nat)).lookup_bindAll
    changes (trees Nat (Option Nat)).empty 3
  rw [(trees_laws (κ := Nat) (ν := Option Nat)).empty] at h
  simpa [snapshot, changes, writeAll, write] using h

/-- Function payloads require no equality or ordering instance. -/
theorem function_payload :
    ((trees Nat (Nat → Nat)).lookup 4
      ((trees Nat (Nat → Nat)).bind 4 (fun n => n + 3)
        (trees Nat (Nat → Nat)).empty)).map (fun f => f 7) = some 10 := by
  have laws := trees_laws (κ := Nat) (ν := Nat → Nat)
  rw [laws.lookup, laws.bind]
  rfl

/-- Composing two public bind squares exposes the update order in meaning. -/
theorem composed_overwrite (old : Tree Nat Nat) :
    decode ((Squares.compose
      ((trees_laws (κ := Nat) (ν := Nat)).bindSquare 2 11)
      ((trees_laws (κ := Nat) (ν := Nat)).bindSquare 2 7)).impl old) 2 = some 11 := by
  have h := congrFun ((Squares.compose
    ((trees_laws (κ := Nat) (ν := Nat)).bindSquare 2 11)
    ((trees_laws (κ := Nat) (ν := Nat)).bindSquare 2 7)).commutes old) 2
  exact h.trans (by rfl)

/-- Both immutable values remain observable after a later binding. This is a
value-level persistence instance, not a physical pointer-identity assertion. -/
theorem retained_observations :
    (trees Nat (Option Nat)).lookup 2 snapshot = some (some 9) ∧
    (trees Nat (Option Nat)).lookup 2
      ((trees Nat (Option Nat)).bind 2 (some 12) snapshot) = some (some 12) := by
  refine ⟨overwritten, ?_⟩
  have laws := trees_laws (κ := Nat) (ν := Option Nat)
  rw [laws.lookup, laws.bind]
  rfl

theorem finite_snapshot :
    ∃ keys : List Nat, ∀ query value,
      (trees Nat (Option Nat)).lookup query snapshot = some value → query ∈ keys :=
  trees_finite_domain snapshot

end Examples.OrderedMap
