import Applications.Search.OrderedMap.TotalTable
import Mathlib.Data.Tree.Get

/-!
# Positive-key tries with an explicit default

The source trie's carrier is a default paired with the existing raw
`BinaryTree`. Lookup is exactly `BinaryTree.getOrElse`; insertion follows the
positive key, filling missing intermediate nodes with the same default.
All raw trees satisfy the total-table laws. No payload equality or ordering
assumption is needed, and a raw table retains its own default across writes.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Search.PositiveTrie

universe u

/-- The default is part of the raw table, independently of its tree shape. -/
abbrev Table (ν : Type u) := ν × BinaryTree ν

variable {ν : Type u}

def empty (default : ν) : Table ν := (default, .nil)

/-- Reuse the existing positive-key tree lookup, forgetting only absence. -/
def look (default : ν) (key : PosNum) (tree : BinaryTree ν) : ν :=
  BinaryTree.getOrElse key tree default

def lookup (key : PosNum) (table : Table ν) : ν :=
  look table.1 key table.2

theorem look_leaf (default : ν) (key : PosNum) : look default key .nil = default := by
  cases key <;> rfl

theorem look_one_node (default value : ν) (left right : BinaryTree ν) :
    look default .one (.node value left right) = value := rfl

theorem look_bit0_node (default value : ν) (key : PosNum) (left right : BinaryTree ν) :
    look default (.bit0 key) (.node value left right) = look default key left := rfl

theorem look_bit1_node (default value : ν) (key : PosNum) (left right : BinaryTree ν) :
    look default (.bit1 key) (.node value left right) = look default key right := rfl

/-- Source insertion's six cases recurse on the key, including below a leaf. -/
def ins (default : ν) : PosNum → ν → BinaryTree ν → BinaryTree ν
  | .one, value, .nil => .node value .nil .nil
  | .bit0 key, value, .nil => .node default (ins default key value .nil) .nil
  | .bit1 key, value, .nil => .node default .nil (ins default key value .nil)
  | .one, value, .node _ left right => .node value left right
  | .bit0 key, value, .node old left right => .node old (ins default key value left) right
  | .bit1 key, value, .node old left right => .node old left (ins default key value right)

theorem ins_one_leaf (default value : ν) :
    ins default .one value .nil = .node value .nil .nil := rfl

theorem ins_bit0_leaf (default value : ν) (key : PosNum) :
    ins default (.bit0 key) value .nil = .node default (ins default key value .nil) .nil := rfl

theorem ins_bit1_leaf (default value : ν) (key : PosNum) :
    ins default (.bit1 key) value .nil = .node default .nil (ins default key value .nil) := rfl

theorem ins_one_node (default value old : ν) (left right : BinaryTree ν) :
    ins default .one value (.node old left right) = .node value left right := rfl

theorem ins_bit0_node (default value old : ν) (key : PosNum) (left right : BinaryTree ν) :
    ins default (.bit0 key) value (.node old left right) =
      .node old (ins default key value left) right := rfl

theorem ins_bit1_node (default value old : ν) (key : PosNum) (left right : BinaryTree ν) :
    ins default (.bit1 key) value (.node old left right) =
      .node old left (ins default key value right) := rfl

def insert (key : PosNum) (value : ν) (table : Table ν) : Table ν :=
  (table.1, ins table.1 key value table.2)

theorem insert_default (key : PosNum) (value : ν) (table : Table ν) :
    (insert key value table).1 = table.1 := rfl

theorem lookup_empty (default : ν) (key : PosNum) : lookup key (empty default) = default :=
  look_leaf default key

theorem look_ins_same (default : ν) (key : PosNum) (value : ν) (tree : BinaryTree ν) :
    look default key (ins default key value tree) = value := by
  induction key generalizing tree with
  | one => cases tree <;> rfl
  | bit0 key ih =>
      cases tree with
      | nil => exact ih .nil
      | node old left right => exact ih left
  | bit1 key ih =>
      cases tree with
      | nil => exact ih .nil
      | node old left right => exact ih right

/-- Lookup and fillers share a default. The claim holds on every raw tree. -/
theorem look_ins_other (default : ν) (key query : PosNum) (value : ν)
    (tree : BinaryTree ν) (different : query ≠ key) :
    look default query (ins default key value tree) = look default query tree := by
  induction key generalizing query tree with
  | one =>
      cases query with
      | one => exact (different rfl).elim
      | bit0 query => cases tree <;> simp only [ins, look_bit0_node, look_leaf]
      | bit1 query => cases tree <;> simp only [ins, look_bit1_node, look_leaf]
  | bit0 key ih =>
      cases query with
      | one => cases tree <;> rfl
      | bit0 query =>
          have h : query ≠ key := fun same => different (congrArg PosNum.bit0 same)
          cases tree with
          | nil => simpa only [ins, look_bit0_node, look_leaf] using ih query .nil h
          | node old left right => exact ih query left h
      | bit1 query => cases tree <;> simp only [ins, look_bit1_node, look_leaf]
  | bit1 key ih =>
      cases query with
      | one => cases tree <;> rfl
      | bit0 query => cases tree <;> simp only [ins, look_bit0_node, look_leaf]
      | bit1 query =>
          have h : query ≠ key := fun same => different (congrArg PosNum.bit1 same)
          cases tree with
          | nil => simpa only [ins, look_bit1_node, look_leaf] using ih query .nil h
          | node old left right => exact ih query right h

theorem lookup_insert_same (key : PosNum) (value : ν) (table : Table ν) :
    lookup key (insert key value table) = value :=
  look_ins_same table.1 key value table.2

theorem lookup_insert_other (key query : PosNum) (value : ν) (table : Table ν)
    (different : query ≠ key) :
    lookup query (insert key value table) = lookup query table :=
  look_ins_other table.1 key query value table.2 different

/-- The source invariant is deliberately trivial for this representation. -/
def IsTrie (_table : Table ν) : Prop := True

theorem empty_isTrie (default : ν) : IsTrie (empty default) := trivial

theorem insert_isTrie (key : PosNum) (value : ν) (table : Table ν)
    (_valid : IsTrie table) : IsTrie (insert key value table) := trivial

def ops (default : ν) : TotalTable.Ops PosNum ν (Table ν) where
  empty := empty default
  get := lookup
  set := insert

/-- Every raw table is valid, including tables with a different stored default. -/
theorem laws (default : ν) : TotalTable.Laws (ops default) default (fun _ => True) where
  empty_valid := trivial
  set_valid _ _ _ _ := trivial
  get_empty := lookup_empty default
  get_set_same key value table _ := lookup_insert_same key value table
  get_set_other key query value table different _ :=
    lookup_insert_other key query value table (Ne.symm different)

end Search.PositiveTrie
