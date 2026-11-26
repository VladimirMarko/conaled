import Applications.Search.PositiveTrie.Basic
import Applications.Numerals.PositiveKeys
import Applications.Trees.BasicObservations
import SquareKit.WordCoalgebra
import Mathlib.Data.Set.Finite.Basic

/-!
# Natural-key and finite-word observations of positive tries

The natural observation uses the established shifted positive-key bijection.
The existing total-table laws transport writes to function updates and the
existing Squares package composes their correspondence. None of these
observations identifies raw trees or reconstructs explicit write histories.

Word behavior consumes low bits first, omitting the terminal positive one.
Nil is absorbing for this semantic run. This agrees with lookup values, not
with lookup costs. Finiteness below concerns subtrees of one fixed input only.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Search.PositiveTrie

universe u

variable {ν : Type u}

def abstract (table : Table ν) (key : Nat) : ν :=
  lookup (Numerals.PositiveKeys.encode key) table

def Abs (table : Table ν) (meaning : Nat → ν) : Prop := abstract table = meaning

theorem abstract_empty (default : ν) : abstract (empty default) = fun _ => default := by
  funext key
  exact lookup_empty default _

theorem lookup_decode (key : PosNum) (table : Table ν) :
    lookup key table = abstract table (Numerals.PositiveKeys.decode key) := by
  unfold abstract
  rw [Numerals.PositiveKeys.encode_decode]

/-- The existing total-table law supplies the positive-key observation equation. -/
theorem observe_insert (default : ν) (key : PosNum) (value : ν) (table : Table ν) :
    TotalTable.observe (ops default) (insert key value table) =
      Function.update (TotalTable.observe (ops default) table) key value :=
  (laws default).observe_set key value trivial

theorem abstract_insert (key : PosNum) (value : ν) (table : Table ν) :
    abstract (insert key value table) =
      Function.update (abstract table) (Numerals.PositiveKeys.decode key) value := by
  change TotalTable.observe (ops table.1) (insert key value table) ∘
      Numerals.PositiveKeys.encode = _
  rw [observe_insert]
  have transport := Function.update_comp_eq_of_injective
    (TotalTable.observe (ops table.1) table) Numerals.PositiveKeys.encode_injective
    (Numerals.PositiveKeys.decode key) value
  have observed : TotalTable.observe (ops table.1) table ∘ Numerals.PositiveKeys.encode =
      abstract table := rfl
  rw [observed, Numerals.PositiveKeys.encode_decode] at transport
  exact transport

theorem empty_relate (default : ν) : Abs (empty default) (fun _ => default) :=
  abstract_empty default

theorem lookup_relate (key : PosNum) (table : Table ν) (meaning : Nat → ν)
    (_valid : IsTrie table) (related : Abs table meaning) :
    lookup key table = meaning (Numerals.PositiveKeys.decode key) := by
  rw [lookup_decode, related]

theorem insert_relate (key : PosNum) (value : ν) (table : Table ν) (meaning : Nat → ν)
    (_valid : IsTrie table) (related : Abs table meaning) :
    Abs (insert key value table)
      (Function.update meaning (Numerals.PositiveKeys.decode key) value) := by
  change abstract (insert key value table) = _
  rw [abstract_insert, related]

/-- Chronological histories reuse the existing executor and observation theorem. -/
theorem observe_setAll (default : ν) (writes : List (PosNum × ν)) (table : Table ν) :
    TotalTable.observe (ops default) (TotalTable.setAll (ops default) writes table) =
      writes.foldl (fun old binding => Function.update old binding.1 binding.2)
        (TotalTable.observe (ops default) table) :=
  (laws default).observe_setAll writes trivial

theorem abstract_insert_shadow (key : PosNum) (first second : ν) (table : Table ν) :
    abstract (insert key second (insert key first table)) =
      abstract (insert key second table) := by
  rw [abstract_insert, abstract_insert, abstract_insert, Function.update_idem]

theorem abstract_insert_self (key : PosNum) (table : Table ν) :
    abstract (insert key (lookup key table) table) = abstract table := by
  rw [abstract_insert, lookup_decode, Function.update_eq_self]

theorem abstract_insert_comm (first second : PosNum) (firstValue secondValue : ν)
    (table : Table ν) (different : first ≠ second) :
    abstract (insert second secondValue (insert first firstValue table)) =
      abstract (insert first firstValue (insert second secondValue table)) := by
  simp only [abstract_insert]
  exact Function.update_comm (Numerals.PositiveKeys.decode_injective.ne different)
    firstValue secondValue (abstract table)

def representation (ν : Type u) : Squares.Rep.{u} where
  R := Table ν
  S := Nat → ν
  decode := abstract

def emptySquare (default : ν) : Squares.Square Squares.terminal (representation ν) where
  impl := fun _ => empty default
  spec := fun _ _ => default
  commutes := fun _ => abstract_empty default

def insertSquare (key : PosNum) (value : ν) :
    Squares.Square (representation ν) (representation ν) where
  impl := insert key value
  spec := fun meaning => Function.update meaning (Numerals.PositiveKeys.decode key) value
  commutes := abstract_insert key value

def lookupSquare (key : PosNum) :
    Squares.Square (representation ν) ⟨ν, ν, id⟩ where
  impl := lookup key
  spec := fun meaning => meaning (Numerals.PositiveKeys.decode key)
  commutes := lookup_decode key

/-- Low bits come first; positive one stops at the current root. -/
def word : PosNum → List Bool
  | .one => []
  | .bit0 key => false :: word key
  | .bit1 key => true :: word key

/-- Existing child projections already make nil absorbing. -/
def next (tree : BinaryTree ν) (bit : Bool) : BinaryTree ν :=
  if bit then tree.right else tree.left

def coalgebra (default : ν) : SquareKit.WordCoalgebra.Coalgebra Bool ν (BinaryTree ν) :=
  fun tree => (look default .one tree, next tree)

theorem run_leaf (default : ν) (bits : List Bool) :
    SquareKit.WordCoalgebra.run (coalgebra default) .nil bits = default := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      cases bit <;> exact ih

theorem run_word (default : ν) (key : PosNum) (tree : BinaryTree ν) :
    SquareKit.WordCoalgebra.run (coalgebra default) tree (word key) =
      look default key tree := by
  induction key generalizing tree with
  | one => rfl
  | bit0 key ih =>
      cases tree with
      | nil => rw [run_leaf, look_leaf]
      | node value left right => exact ih left
  | bit1 key ih =>
      cases tree with
      | nil => rw [run_leaf, look_leaf]
      | node value left right => exact ih right

/-- A sufficiently deep existing snapshot has the same observation. Its
depth-indexed carrier is not the table representation. -/
theorem lookup_unfold_word (default : ν) (key : PosNum) (tree : BinaryTree ν)
    (depth : Nat) (enough : (word key).length ≤ depth) :
    (SquareKit.WordCoalgebra.unfold (coalgebra default) tree depth).lookup (word key) =
      some (look default key tree) := by
  rw [SquareKit.WordCoalgebra.lookup_unfold _ _ _ _ enough, run_word]

private theorem finite_subtrees (tree : BinaryTree ν) : (Trees.subtrees tree).Finite := by
  induction tree with
  | nil =>
      rw [Trees.subtrees_nil]
      exact Set.finite_singleton _
  | node value left right leftIH rightIH =>
      rw [Trees.subtrees_node]
      exact ((Set.finite_singleton _).union leftIH).union rightIH

theorem next_mem_subtrees (root state : BinaryTree ν) (bit : Bool)
    (inside : state ∈ Trees.subtrees root) : next state bit ∈ Trees.subtrees root := by
  apply Trees.Subtree.trans (t := state) ?_ inside
  cases state with
  | nil =>
      cases bit <;> exact Trees.Subtree.refl .nil
  | node value left right =>
      cases bit
      · exact Trees.Subtree.left value (Trees.Subtree.refl left)
      · exact Trees.Subtree.right value (Trees.Subtree.refl right)

theorem foldl_mem_subtrees (root state : BinaryTree ν) (bits : List Bool)
    (inside : state ∈ Trees.subtrees root) : bits.foldl next state ∈ Trees.subtrees root := by
  induction bits generalizing state with
  | nil => exact inside
  | cons bit bits ih => exact ih (next state bit) (next_mem_subtrees root state bit inside)

/-- Only states reachable from this fixed finite tree are claimed finite. -/
theorem reachable_finite (tree : BinaryTree ν) :
    (Set.range (fun bits : List Bool => bits.foldl next tree)).Finite := by
  apply (finite_subtrees tree).subset
  rintro state ⟨bits, rfl⟩
  exact foldl_mem_subtrees tree tree bits (Trees.self_mem_subtrees tree)

end Search.PositiveTrie
