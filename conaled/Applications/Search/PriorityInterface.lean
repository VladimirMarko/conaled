import Applications.Search.LeftistQueue

/-!
# Priority-frontier interface for the source heuristic searches

The occurrence contract for deletion is exact. Insertion may replace an existing
value at the same key by a lower-priority value, as the source PSQ does. This
interface permits both the literal leftist queue and the keyed queue; its laws do
not assign a logarithmic price to a list implementation.
-/
set_option autoImplicit false
set_option warningAsError true
namespace Search.PriorityInterface
universe u v w z
variable {α : Type u} {κ : Type v} {π : Type w}

/-- Executable operations, independently of their observation and laws. -/
structure Operations (α : Type u) (π : Type w) where
  Carrier : Type z
  empty : Carrier
  add : List (α × π) → Carrier → Carrier
  remove : Carrier → Option ((α × π) × Carrier)

/-- Laws relate the supplied operations to occurrence observations and validity.
They permit keyed replacement; they do not equate arbitrary queue tie choices. -/
structure Laws [LE π] (key : α → κ) (ops : Operations.{u,w,z} α π)
    (entries : ops.Carrier → List (α × π)) (Valid : ops.Carrier → Prop) : Prop where
  empty_entries : entries ops.empty = []
  empty_valid : Valid ops.empty
  add_valid : ∀ xs q, Valid q → Valid (ops.add xs q)
  add_origin : ∀ xs q e, e ∈ entries (ops.add xs q) → e ∈ xs ++ entries q
  add_covers : ∀ xs q e, e ∈ xs ++ entries q →
    ∃ e' ∈ entries (ops.add xs q), key e'.1 = key e.1 ∧ e'.2 ≤ e.2
  add_length : ∀ xs q, (entries (ops.add xs q)).length ≤ xs.length + (entries q).length
  remove_none : ∀ q, ops.remove q = none ↔ entries q = []
  remove_spec : ∀ q e r, Valid q → ops.remove q = some (e,r) →
    Valid r ∧ (entries q).Perm (e :: entries r) ∧
      (∀ a ∈ entries q, e.2 ≤ a.2)

/-- An ordinary queue implementation together with its selected observation. -/
structure Queue (α : Type u) (κ : Type v) (π : Type w) [LE π]
    (key : α → κ) extends Operations.{u,w,z} α π where
  entries : Carrier → List (α × π)
  Valid : Carrier → Prop
  lawful : Laws key toOperations entries Valid

abbrev Queue.empty_entries [LE π] {key : α → κ} (Q : Queue.{u,v,w,z} α κ π key) := Q.lawful.empty_entries
abbrev Queue.empty_valid [LE π] {key : α → κ} (Q : Queue.{u,v,w,z} α κ π key) := Q.lawful.empty_valid
abbrev Queue.add_valid [LE π] {key : α → κ} (Q : Queue.{u,v,w,z} α κ π key) := Q.lawful.add_valid
abbrev Queue.add_origin [LE π] {key : α → κ} (Q : Queue.{u,v,w,z} α κ π key) := Q.lawful.add_origin
abbrev Queue.add_covers [LE π] {key : α → κ} (Q : Queue.{u,v,w,z} α κ π key) := Q.lawful.add_covers
abbrev Queue.add_length [LE π] {key : α → κ} (Q : Queue.{u,v,w,z} α κ π key) := Q.lawful.add_length
abbrev Queue.remove_none [LE π] {key : α → κ} (Q : Queue.{u,v,w,z} α κ π key) := Q.lawful.remove_none
abbrev Queue.remove_spec [LE π] {key : α → κ} (Q : Queue.{u,v,w,z} α κ π key) := Q.lawful.remove_spec

section Leftist
variable [LE π] [DecidableLE π] [Std.IsLinearPreorder π]
open Search.LeftistQueue

def leftist (key : α → κ) : Queue α κ π key where
  Carrier := PQ α π
  entries := Search.LeftistQueue.entries
  empty := emptyQ
  add := addListQ
  remove := deleteQ
  Valid := Search.LeftistQueue.Valid
  lawful := {
    empty_entries := rfl
    empty_valid := emptyQ_valid
    add_valid := addListQ_valid
    add_origin := fun xs q e he => (addListQ_entries xs q).mem_iff.mp he
    add_covers := fun xs q e he =>
      ⟨e, (addListQ_entries xs q).mem_iff.mpr he, rfl, Std.le_refl _⟩
    add_length := fun xs q => by
      have h := (addListQ_entries xs q).length_eq
      simpa using Nat.le_of_eq h
    remove_none := fun q => by
      rw [deleteQ_none_iff]
      cases q <;> simp [entries]
    remove_spec := fun q e r hq hd =>
      let h := deleteQ_spec q e r hq hd
      ⟨h.1,h.2.1,h.2.2.1⟩
  }
end Leftist
end Search.PriorityInterface
