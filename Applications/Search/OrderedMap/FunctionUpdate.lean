import Applications.Search.OrderedMap.Observations

/-!
# Function updates and the partial-map write operation

The VFA Maps update tests the written key against the query. The standard
function update tests the query against the written key; the equations below
relate those exact branches. Partial-map algebra then reuses function update
at `Option` values. Keys and payloads have independent universes, and payloads
need neither equality, ordering nor a distinguished default.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap

universe u v
variable {κ : Type u} {ν : Type v}

/-- The source orientation of the equality test, for an arbitrary key type. -/
theorem update_apply_written [DecidableEq κ] (m : κ → ν) (key : κ) (value : ν)
    (query : κ) :
    Function.update m key value query = if key = query then value else m query := by
  simp only [Function.update_apply, eq_comm]

/-- Nat's Boolean equality supplies the source's exact function-valued branch. -/
theorem update_nat_source (m : Nat → ν) (key : Nat) (value : ν) :
    Function.update m key value = fun query =>
      if key == query then value else m query := by
  funext query
  rw [update_apply_written]
  simp only [beq_iff_eq]

/-- Later writes to the same key replace the previous payload. -/
theorem write_shadow [DecidableEq κ] (m : Meaning κ ν) (key : κ)
    (first last : ν) : write key last (write key first m) = write key last m := by
  simp only [write_eq_update, Function.update_idem]

/-- A partial write is unchanged precisely when that payload was already bound.
An absent key is not interchangeable with a stored default. -/
theorem write_eq_self_iff [DecidableEq κ] (m : Meaning κ ν) (key : κ) (value : ν) :
    write key value m = m ↔ m key = some value := by
  rw [write_eq_update, Function.update_eq_self_iff]
  exact eq_comm

theorem write_same [DecidableEq κ] (m : Meaning κ ν) (key : κ) (value : ν)
    (bound : m key = some value) : write key value m = m :=
  (write_eq_self_iff m key value).mpr bound

/-- Distinct-key writes commute as complete optional-valued functions. -/
theorem write_comm [DecidableEq κ] (m : Meaning κ ν) (first second : κ)
    (a b : ν) (different : first ≠ second) :
    write second b (write first a m) = write first a (write second b m) := by
  simp only [write_eq_update]
  exact Function.update_comm different (some a) (some b) m

end Search.OrderedMap
