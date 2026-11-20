import Applications.Search.PositiveTrie.Basic
import Applications.Numerals.PositivePaths

/-!
# Sparse maps and finite sets on positive-key tries

Optional payloads distinguish absence from a present value, even when that value
is itself an empty set. Boolean payloads describe set membership. Both carriers
reuse `BinaryTree`, and both insertions reuse the accepted positive-trie `ins`.
Pruning, erasure, simultaneous difference and root-first choice retain the source
recurrences on arbitrary raw trees; no normalization hypothesis is hidden here.

Source equations: Rocq Stdlib `FMapPositive` and `FSetPositive` at
`fda356e01346f7766b282ef9f44080cce2be23b3`. Upstream copyright INRIA, CNRS
and contributors; GNU LGPL version 2.1. See `docs/research/rocq-stdlib-notice.md`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Search.PositiveTrie

universe u v w

abbrev SparseMap (α : Type u) := BinaryTree (Option α)
abbrev KeySet := BinaryTree Bool

namespace SparseMap

variable {α : Type u} {β : Type v}

def find (key : PosNum) (tree : SparseMap α) : Option α := look none key tree

@[simp] theorem find_nil (key : PosNum) : find key (.nil : SparseMap α) = none :=
  look_leaf none key

@[simp] theorem find_one_node (value : Option α) (left right : SparseMap α) :
    find .one (.node value left right) = value := rfl

@[simp] theorem find_bit0_node (key : PosNum) (value : Option α)
    (left right : SparseMap α) :
    find (.bit0 key) (.node value left right) = find key left := rfl

@[simp] theorem find_bit1_node (key : PosNum) (value : Option α)
    (left right : SparseMap α) :
    find (.bit1 key) (.node value left right) = find key right := rfl

theorem find_eq_get_join (key : PosNum) (tree : SparseMap α) :
    find key tree = (tree.get key).join := by
  unfold find look BinaryTree.getOrElse
  cases tree.get key <;> rfl

def add (key : PosNum) (value : α) (tree : SparseMap α) : SparseMap α :=
  ins none key (some value) tree

@[simp] theorem find_add_same (key : PosNum) (value : α) (tree : SparseMap α) :
    find key (add key value tree) = some value := look_ins_same none key (some value) tree

theorem find_add_other (key query : PosNum) (value : α) (tree : SparseMap α)
    (different : query ≠ key) : find query (add key value tree) = find query tree :=
  look_ins_other none key query (some value) tree different

theorem find_add (key query : PosNum) (value : α) (tree : SparseMap α) :
    find query (add key value tree) = if query = key then some value else find query tree := by
  by_cases h : query = key
  · subst query
    simp
  · simp only [h, ite_false, find_add_other key query value tree h]

/-- The same functional update law as the accepted total-table observation. -/
theorem find_add_function (key : PosNum) (value : α) (tree : SparseMap α) :
    (fun query => find query (add key value tree)) =
      Function.update (fun query => find query tree) key (some value) := by
  funext query
  by_cases h : query = key
  · subst query
    simp only [find_add_same, Function.update_self]
  · simp only [find_add_other key query value tree h, Function.update_of_ne h]

/-- Collapse exactly an unoccupied node with two empty children. -/
def prune : Option α → SparseMap α → SparseMap α → SparseMap α
  | none, .nil, .nil => .nil
  | value, left, right => .node value left right

theorem find_prune (key : PosNum) (value : Option α) (left right : SparseMap α) :
    find key (prune value left right) = find key (.node value left right) := by
  cases value <;> cases left <;> cases right <;> cases key <;> simp [prune]

/-- The provider's pruning removal, expressed with its common pruning step. -/
def erase : PosNum → SparseMap α → SparseMap α
  | _, .nil => .nil
  | .one, .node _ left right => prune none left right
  | .bit0 key, .node value left right => prune value (erase key left) right
  | .bit1 key, .node value left right => prune value left (erase key right)

theorem find_erase (key query : PosNum) (tree : SparseMap α) :
    find query (erase key tree) = if query = key then none else find query tree := by
  induction key generalizing query tree <;> cases tree <;> cases query <;>
    simp_all [erase, find_prune]

@[simp] theorem find_erase_same (key : PosNum) (tree : SparseMap α) :
    find key (erase key tree) = none := by simp only [find_erase, ite_true]

theorem find_erase_other (key query : PosNum) (tree : SparseMap α)
    (different : query ≠ key) : find query (erase key tree) = find query tree := by
  simp only [find_erase, different, ite_false]

/-- Occupied nodes, not the number of raw tree nodes. -/
def cardinal : SparseMap α → Nat
  | .nil => 0
  | .node none left right => cardinal left + cardinal right
  | .node (some _) left right => (cardinal left + cardinal right) + 1

theorem cardinal_node (value : Option α) (left right : SparseMap α) :
    cardinal (.node value left right) =
      cardinal left + cardinal right + (if value.isSome then 1 else 0) := by
  cases value <;> simp [cardinal]

theorem cardinal_prune (value : Option α) (left right : SparseMap α) :
    cardinal (prune value left right) = cardinal (.node value left right) := by
  cases value <;> cases left <;> cases right <;> rfl

theorem cardinal_erase_add (key : PosNum) (tree : SparseMap α) :
    cardinal (erase key tree) + (if (find key tree).isSome then 1 else 0) =
      cardinal tree := by
  induction key generalizing tree with
  | one =>
      cases tree with
      | nil => rfl
      | node value left right =>
          cases value <;> simp [erase, cardinal_prune, cardinal]
  | bit0 key ih =>
      cases tree with
      | nil => rfl
      | node value left right =>
          have h := ih left
          simp only [erase, cardinal_prune, cardinal_node, find_bit0_node]
          rw [← h]
          ac_rfl
  | bit1 key ih =>
      cases tree with
      | nil => rfl
      | node value left right =>
          have h := ih right
          simp only [erase, cardinal_prune, cardinal_node, find_bit1_node]
          rw [← h]
          ac_rfl

theorem cardinal_erase_of_some (key : PosNum) (tree : SparseMap α) (value : α)
    (present : find key tree = some value) : cardinal (erase key tree) + 1 = cardinal tree := by
  simpa only [present, Option.isSome_some, ite_true] using cardinal_erase_add key tree

theorem cardinal_erase_lt (key : PosNum) (tree : SparseMap α) (value : α)
    (present : find key tree = some value) : cardinal (erase key tree) < cardinal tree := by
  have h := cardinal_erase_of_some key tree value present
  omega

theorem cardinal_erase_of_none (key : PosNum) (tree : SparseMap α)
    (absent : find key tree = none) : cardinal (erase key tree) = cardinal tree := by
  simpa only [absent, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero]
    using cardinal_erase_add key tree

def map (f : α → β) (tree : SparseMap α) : SparseMap β :=
  BinaryTree.map (Option.map f) tree

theorem find_map (f : α → β) (key : PosNum) (tree : SparseMap α) :
    find key (map f tree) = (find key tree).map f := by
  induction key generalizing tree <;> cases tree <;> simp_all [map, BinaryTree.map]

theorem cardinal_map (f : α → β) (tree : SparseMap α) :
    cardinal (map f tree) = cardinal tree := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr => cases value <;> simp_all [map, BinaryTree.map, cardinal]

/-- The provider's forward-prefix key-aware map. -/
def mapiFrom (f : PosNum → α → β) (pathPrefix : PosNum) : SparseMap α → SparseMap β
  | .nil => .nil
  | .node value left right =>
      .node (value.map (f pathPrefix))
        (mapiFrom f (Numerals.PositivePaths.append pathPrefix (.bit0 .one)) left)
        (mapiFrom f (Numerals.PositivePaths.append pathPrefix (.bit1 .one)) right)

/-- Ignoring the generated key gives exactly the existing payload map. -/
theorem mapiFrom_key_ignore (f : α → β) (pathPrefix : PosNum) (tree : SparseMap α) :
    mapiFrom (fun _ => f) pathPrefix tree = map f tree := by
  induction tree generalizing pathPrefix with
  | nil => rfl
  | node value left right ihl ihr => simp only [mapiFrom, map, BinaryTree.map, ihl, ihr]

end SparseMap

namespace KeySet

def mem (key : PosNum) (tree : KeySet) : Bool := look false key tree

@[simp] theorem mem_nil (key : PosNum) : mem key .nil = false := look_leaf false key

@[simp] theorem mem_one_node (value : Bool) (left right : KeySet) :
    mem .one (.node value left right) = value := rfl

@[simp] theorem mem_bit0_node (key : PosNum) (value : Bool) (left right : KeySet) :
    mem (.bit0 key) (.node value left right) = mem key left := rfl

@[simp] theorem mem_bit1_node (key : PosNum) (value : Bool) (left right : KeySet) :
    mem (.bit1 key) (.node value left right) = mem key right := rfl

def add (key : PosNum) (tree : KeySet) : KeySet := ins false key true tree

@[simp] theorem mem_add_same (key : PosNum) (tree : KeySet) :
    mem key (add key tree) = true := look_ins_same false key true tree

theorem mem_add_other (key query : PosNum) (tree : KeySet) (different : query ≠ key) :
    mem query (add key tree) = mem query tree := look_ins_other false key query true tree different

theorem mem_add (key query : PosNum) (tree : KeySet) :
    mem query (add key tree) = (decide (query = key) || mem query tree) := by
  by_cases h : query = key
  · subst query
    simp
  · simp only [mem_add_other key query tree h, h, decide_false, Bool.false_or]

def prune : Bool → KeySet → KeySet → KeySet
  | false, .nil, .nil => .nil
  | value, left, right => .node value left right

theorem mem_prune (key : PosNum) (value : Bool) (left right : KeySet) :
    mem key (prune value left right) = mem key (.node value left right) := by
  cases value <;> cases left <;> cases right <;> cases key <;> simp [prune]

def erase : PosNum → KeySet → KeySet
  | _, .nil => .nil
  | .one, .node _ left right => prune false left right
  | .bit0 key, .node value left right => prune value (erase key left) right
  | .bit1 key, .node value left right => prune value left (erase key right)

theorem mem_erase (key query : PosNum) (tree : KeySet) :
    mem query (erase key tree) = if query = key then false else mem query tree := by
  induction key generalizing query tree <;> cases tree <;> cases query <;>
    simp_all [erase, mem_prune]

@[simp] theorem mem_erase_same (key : PosNum) (tree : KeySet) :
    mem key (erase key tree) = false := by simp only [mem_erase, ite_true]

theorem mem_erase_other (key query : PosNum) (tree : KeySet) (different : query ≠ key) :
    mem query (erase key tree) = mem query tree := by simp only [mem_erase, different, ite_false]

/-- Simultaneous traversal; a missing right tree returns the left tree unchanged. -/
def diff : KeySet → KeySet → KeySet
  | .nil, _ => .nil
  | tree@(.node _ _ _), .nil => tree
  | .node value left right, .node value' left' right' =>
      prune (value && !value') (diff left left') (diff right right')

theorem mem_diff (key : PosNum) (left right : KeySet) :
    mem key (diff left right) = (mem key left && !mem key right) := by
  induction left generalizing key right with
  | nil => simp [diff]
  | node value l r ihl ihr =>
      cases right with
      | nil => simp [diff]
      | node value' l' r' => cases key <;> simp_all [diff, mem_prune]

def cardinal : KeySet → Nat
  | .nil => 0
  | .node false left right => cardinal left + cardinal right
  | .node true left right => (cardinal left + cardinal right) + 1

theorem cardinal_node (value : Bool) (left right : KeySet) :
    cardinal (.node value left right) =
      cardinal left + cardinal right + (if value then 1 else 0) := by
  cases value <;> simp [cardinal]

theorem cardinal_prune (value : Bool) (left right : KeySet) :
    cardinal (prune value left right) = cardinal (.node value left right) := by
  cases value <;> cases left <;> cases right <;> rfl

theorem cardinal_erase_add (key : PosNum) (tree : KeySet) :
    cardinal (erase key tree) + (if mem key tree then 1 else 0) = cardinal tree := by
  induction key generalizing tree with
  | one =>
      cases tree with
      | nil => rfl
      | node value left right => cases value <;> simp [erase, cardinal_prune, cardinal]
  | bit0 key ih =>
      cases tree with
      | nil => rfl
      | node value left right =>
          have h := ih left
          simp only [erase, cardinal_prune, cardinal_node, mem_bit0_node]
          rw [← h]
          ac_rfl
  | bit1 key ih =>
      cases tree with
      | nil => rfl
      | node value left right =>
          have h := ih right
          simp only [erase, cardinal_prune, cardinal_node, mem_bit1_node]
          rw [← h]
          ac_rfl

theorem cardinal_erase_of_mem (key : PosNum) (tree : KeySet) (present : mem key tree = true) :
    cardinal (erase key tree) + 1 = cardinal tree := by
  simpa only [present, ite_true] using cardinal_erase_add key tree

theorem cardinal_erase_lt (key : PosNum) (tree : KeySet) (present : mem key tree = true) :
    cardinal (erase key tree) < cardinal tree := by
  have h := cardinal_erase_of_mem key tree present
  omega

theorem cardinal_erase_of_not_mem (key : PosNum) (tree : KeySet)
    (absent : mem key tree = false) : cardinal (erase key tree) = cardinal tree := by
  simpa only [absent, Bool.false_eq_true, ite_false, Nat.add_zero] using cardinal_erase_add key tree

/-- Source choice visits a present root before either subtree. -/
def choose : KeySet → Option PosNum
  | .nil => none
  | .node true _ _ => some .one
  | .node false left right =>
      match choose left with
      | some key => some (.bit0 key)
      | none => (choose right).map PosNum.bit1

theorem choose_mem (tree : KeySet) {key : PosNum} (chosen : choose tree = some key) :
    mem key tree = true := by
  induction tree generalizing key with
  | nil => simp [choose] at chosen
  | node value left right ihl ihr =>
      cases value with
      | true =>
          simp only [choose, Option.some.injEq] at chosen
          subst key
          rfl
      | false =>
          cases hl : choose left with
          | some k =>
              simp only [choose, hl, Option.some.injEq] at chosen
              subst key
              exact ihl hl
          | none =>
              cases hr : choose right with
              | none => simp [choose, hl, hr] at chosen
              | some k =>
                  simp only [choose, hl, hr, Option.map_some, Option.some.injEq] at chosen
                  subst key
                  exact ihr hr

theorem all_mem_false_node (value : Bool) (left right : KeySet) :
    (∀ key, mem key (.node value left right) = false) ↔
      value = false ∧ (∀ key, mem key left = false) ∧ (∀ key, mem key right = false) := by
  constructor
  · intro h
    exact ⟨h .one, fun key => h (.bit0 key), fun key => h (.bit1 key)⟩
  · rintro ⟨hv, hl, hr⟩ key
    cases key with
    | one => exact hv
    | bit0 key => exact hl key
    | bit1 key => exact hr key

theorem choose_none_iff (tree : KeySet) :
    choose tree = none ↔ ∀ key, mem key tree = false := by
  induction tree with
  | nil => simp [choose]
  | node value left right ihl ihr =>
      rw [all_mem_false_node, ← ihl, ← ihr]
      cases value <;> cases hl : choose left <;> cases hr : choose right <;> simp [choose, hl, hr]

/-- Empty padding does not affect deterministic source choice. -/
theorem choose_ext {left right : KeySet} (same : ∀ key, mem key left = mem key right) :
    choose left = choose right := by
  induction left generalizing right with
  | nil =>
      symm
      apply (choose_none_iff right).mpr
      intro key
      rw [← same key, mem_nil]
  | node value l r ihl ihr =>
      cases right with
      | nil =>
          apply (choose_none_iff _).mpr
          intro key
          rw [same key, mem_nil]
      | node value' l' r' =>
          have hv : value = value' := same .one
          have hl : ∀ key, mem key l = mem key l' := fun key => same (.bit0 key)
          have hr : ∀ key, mem key r = mem key r' := fun key => same (.bit1 key)
          subst value'
          cases value <;> simp only [choose, ihl hl, ihr hr]

end KeySet
end Search.PositiveTrie
