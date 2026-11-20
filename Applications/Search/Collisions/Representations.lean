import Applications.Search.Collisions.Basic
import Applications.Search.PositiveTrie.Models
import Applications.Numerals.PositiveKeys
import Mathlib.Data.Num.ZNum

/-!
# The source collision programs and their common meaning

The recurrences retain the source's counter carriers and operand order. Natural
and signed function tables use the accepted `Function.update`; the positive
program uses the actual trie. These are value and observation theorems. Unary
costs, signed binary costs, and trie traversal costs require separate models.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Search.Collisions

namespace VerySlow

/-- Source Nat-key program, preserving its `c + 1` branch. -/
def loop : List Nat → Nat → (Nat → Bool) → Nat
  | [], c, _ => c
  | key :: xs, c, table =>
      if table key then loop xs (c + 1) table
      else loop xs c (Function.update table key true)

def collisions (xs : List Nat) : Nat := loop xs 0 (fun _ => false)

/-- Exact source recursion realizes the common table client at every initial
counter and function, without a finite-support premise. -/
theorem loop_common (xs : List Nat) (c : Nat) (table : Nat → Bool) :
    loop xs c table = Search.Collisions.loop (TotalTable.functions false) xs c table := by
  induction xs generalizing c table with
  | nil => rfl
  | cons key xs ih =>
      cases h : table key <;>
        simp [loop, Search.Collisions.loop_cons, TotalTable.functions, h, ih]

theorem collisions_correct (xs : List Nat) : collisions xs = count xs := by
  rw [collisions, loop_common]
  exact Search.Collisions.collisions_correct (TotalTable.functions_laws false) xs

end VerySlow

namespace RatherSlow

universe u

/-- Source signed-key total functions remain unrestricted functions. -/
abbrev TotalMap (ν : Type u) := ZNum → ν

def empty {ν : Type u} (default : ν) : TotalMap ν := fun _ => default

/-- The constructor-derived `DecidableEq ZNum` is the executable equality
decision; integer conversion is an observation, not the implementation. -/
def eqb (written query : ZNum) : Bool := decide (written = query)

theorem eqb_int (written query : ZNum) :
    eqb written query = decide ((written : Int) = (query : Int)) := by
  simp only [eqb, ZNum.to_int_inj]

def update {ν : Type u} (table : TotalMap ν) (key : ZNum) (value : ν) : TotalMap ν :=
  Function.update table key value

/-- Preserve the source written-key/query orientation and arbitrary payload. -/
theorem update_apply {ν : Type u} (table : TotalMap ν) (key query : ZNum) (value : ν) :
    update table key value query = if eqb key query then value else table query := by
  by_cases h : key = query
  · subst query
    simp [update, eqb]
  · simp [update, eqb, h, Ne.symm h]

/-- Source signed keys and signed counter, including arbitrary negative starts. -/
def loop : List ZNum → ZNum → TotalMap Bool → ZNum
  | [], c, _ => c
  | key :: xs, c, table =>
      if table key then loop xs (c + 1) table
      else loop xs c (update table key true)

def collisions (xs : List ZNum) : ZNum := loop xs 0 (empty false)

/-- The starting signed counter is retained as an Int offset. No restriction
on the starting function, its support, or the sign of the counter is imposed. -/
theorem loop_common (xs : List ZNum) (c : ZNum) (table : TotalMap Bool) :
    (loop xs c table : Int) = (c : Int) +
      (Search.Collisions.loop (TotalTable.functions false) xs 0 table : Int) := by
  induction xs generalizing c table with
  | nil => simp [loop]
  | cons key xs ih =>
      cases h : table key
      · simpa [loop, Search.Collisions.loop_cons, TotalTable.functions, h, update] using
          ih c (update table key true)
      · have one_start : Search.Collisions.loop (TotalTable.functions false) xs 1 table =
            1 + Search.Collisions.loop (TotalTable.functions false) xs 0 table := by
          simpa using Search.Collisions.loop_add (TotalTable.functions false) xs 1 0 table
        simp only [loop, h, ↓reduceIte, Search.Collisions.loop_cons, TotalTable.functions]
        change (loop xs (c + 1) table : Int) = (c : Int) +
          (Search.Collisions.loop (TotalTable.functions false) xs 1 table : Int)
        rw [ih, one_start]
        simp [add_assoc]

theorem collisions_correct (xs : List ZNum) : (collisions xs : Int) = (count xs : Int) := by
  rw [collisions, loop_common]
  change (0 : Int) + (Search.Collisions.collisions (TotalTable.functions false) xs : Int) = _
  rw [Search.Collisions.collisions_correct (TotalTable.functions_laws false)]
  exact zero_add _

/-- Signed-key interpretation preserves repetitions, including negative keys. -/
theorem collisions_int_keys (xs : List ZNum) :
    (collisions xs : Int) = (count (xs.map (fun key : ZNum => (key : Int))) : Int) := by
  rw [collisions_correct, count_map (fun key : ZNum => (key : Int))]
  intro x y h
  exact ZNum.to_int_inj.mp h

/-- Numeric counter bounds hold for every initial function, including functions
without a finite seen-key witness. -/
theorem loop_bounds (xs : List ZNum) (c : ZNum) (table : TotalMap Bool) :
    (c : Int) ≤ (loop xs c table : Int) ∧
      (loop xs c table : Int) ≤ (c : Int) + xs.length := by
  rw [loop_common]
  have bounds := Search.Collisions.loop_bounds (TotalTable.functions false) xs 0 table
  simp only [Nat.zero_add] at bounds
  exact ⟨by omega, by omega⟩

/-- Every zero-start processed prefix has a nonnegative signed counter. This is
a value invariant needed before later counter-cost accounting. -/
theorem zero_start_nonnegative (xs : List ZNum) (table : TotalMap Bool) :
    0 ≤ (loop xs 0 table : Int) := by
  simpa only [ZNum.cast_zero] using (loop_bounds xs 0 table).1

end RatherSlow

namespace FastEnough

/-- Source positive-key trie program, preserving its `1 + c` branch. -/
def loop : List PosNum → Nat → PositiveTrie.Table Bool → Nat
  | [], c, _ => c
  | key :: xs, c, table =>
      if PositiveTrie.lookup key table then loop xs (1 + c) table
      else loop xs c (PositiveTrie.insert key true table)

def collisions (xs : List PosNum) : Nat := loop xs 0 (PositiveTrie.empty false)

/-- The exact source operand orientation agrees in value with the common
client; this equation does not identify unary addition costs. -/
theorem loop_common (xs : List PosNum) (c : Nat) (table : PositiveTrie.Table Bool) :
    loop xs c table = Search.Collisions.loop (PositiveTrie.ops false) xs c table := by
  induction xs generalizing c table with
  | nil => rfl
  | cons key xs ih =>
      cases h : PositiveTrie.lookup key table <;>
        simp [loop, Search.Collisions.loop_cons, PositiveTrie.ops, h, ih, Nat.add_comm]

theorem collisions_correct (xs : List PosNum) : collisions xs = count xs := by
  rw [collisions, loop_common]
  exact Search.Collisions.collisions_correct (PositiveTrie.laws false) xs

/-- Same-key total-function interpretation for every raw initial table,
including tables whose stored default is true. -/
theorem loop_observe (xs : List PosNum) (c : Nat) (table : PositiveTrie.Table Bool) :
    loop xs c table = Search.Collisions.loop (TotalTable.functions false) xs c
      (fun key => PositiveTrie.lookup key table) := by
  rw [loop_common]
  exact Search.Collisions.loop_agrees (PositiveTrie.laws false)
    (TotalTable.functions_laws false) xs c trivial trivial rfl

/-- The source shifted Nat abstraction transports an arbitrary initial trie,
not only the empty-table collision result. -/
theorem loop_abstract (xs : List PosNum) (c : Nat) (table : PositiveTrie.Table Bool) :
    loop xs c table = VerySlow.loop (xs.map Numerals.PositiveKeys.decode) c
      (PositiveTrie.abstract table) := by
  rw [loop_common, VerySlow.loop_common]
  apply Search.Collisions.loop_reindex (PositiveTrie.laws false)
    (TotalTable.functions_laws false) Numerals.PositiveKeys.decode
    Numerals.PositiveKeys.decode_injective xs c trivial trivial
  intro key
  exact PositiveTrie.lookup_decode key table

/-- Unshifted numeric observation preserves the source positive labels. -/
theorem collisions_numeric (xs : List PosNum) :
    collisions xs = VerySlow.collisions (xs.map Numerals.PositiveKeys.numeric) := by
  rw [collisions_correct, VerySlow.collisions_correct,
    count_map _ Numerals.PositiveKeys.numeric_injective]

/-- Shifted natural keys preserve duplicates, but subtract one from each
positive numeric label. This is distinct from `collisions_numeric`. -/
theorem collisions_decode (xs : List PosNum) :
    collisions xs = VerySlow.collisions (xs.map Numerals.PositiveKeys.decode) := by
  rw [collisions_correct, VerySlow.collisions_correct,
    count_map _ Numerals.PositiveKeys.decode_injective]

/-- Encoding a Nat list raises the positive numeric labels by one; it still
preserves the number of repeated occurrences. -/
theorem collisions_encode (xs : List Nat) :
    collisions (xs.map Numerals.PositiveKeys.encode) = VerySlow.collisions xs := by
  rw [collisions_correct, VerySlow.collisions_correct,
    count_map _ Numerals.PositiveKeys.encode_injective]

end FastEnough

end Search.Collisions
