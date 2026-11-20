import Applications.Search.PositiveTrie.Enumeration
import Applications.Numerals.PositivePaths.Length
import Applications.Trees.Observations
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Occupancy normalization and structural bounds for finite positive tries

Normalization excludes empty padding without changing any raw semantic API.
Occupied-key bit mass is a mathematical list observation, not a traversal
inserted into the graph-coloring program. Optional occupancy ignores the value
of a present payload; Boolean occupancy is set membership.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Search.PositiveTrie

open Numerals.PositiveArithmetic Numerals.PositivePaths

universe u v
variable {α : Type u} {β : Type v}

def Normalized (occupied : α → Bool) : BinaryTree α → Prop
  | .nil => True
  | .node value left right =>
      Normalized occupied left ∧ Normalized occupied right ∧
        (occupied value = true ∨ left ≠ .nil ∨ right ≠ .nil)

theorem normalized_nil (occupied : α → Bool) : Normalized occupied .nil := trivial

theorem ins_ne_nil (default : α) (key : PosNum) (value : α) (tree : BinaryTree α) :
    ins default key value tree ≠ .nil := by
  cases key <;> cases tree <;> simp only [ins, ne_eq, reduceCtorEq, not_false_eq_true]

theorem normalized_ins (occupied : α → Bool) (default : α) (key : PosNum)
    (value : α) (tree : BinaryTree α) (present : occupied value = true)
    (normal : Normalized occupied tree) : Normalized occupied (ins default key value tree) := by
  induction key generalizing tree with
  | one =>
      cases tree with
      | nil => exact ⟨trivial, trivial, Or.inl present⟩
      | node old left right => exact ⟨normal.1, normal.2.1, Or.inl present⟩
  | bit0 key ih =>
      cases tree with
      | nil => exact ⟨ih .nil trivial, trivial, Or.inr (Or.inl (ins_ne_nil _ _ _ _))⟩
      | node old left right =>
          exact ⟨ih left normal.1, normal.2.1, Or.inr (Or.inl (ins_ne_nil _ _ _ _))⟩
  | bit1 key ih =>
      cases tree with
      | nil => exact ⟨trivial, ih .nil trivial, Or.inr (Or.inr (ins_ne_nil _ _ _ _))⟩
      | node old left right =>
          exact ⟨normal.1, ih right normal.2.1, Or.inr (Or.inr (ins_ne_nil _ _ _ _))⟩

theorem normalized_map_iff (occupied : α → Bool) (occupied' : β → Bool)
    (label : α → β) (same : ∀ value, occupied' (label value) = occupied value)
    (tree : BinaryTree α) :
    Normalized occupied' (BinaryTree.map label tree) ↔ Normalized occupied tree := by
  have empty (t : BinaryTree α) : BinaryTree.map label t = .nil ↔ t = .nil := by
    cases t <;> simp only [BinaryTree.map, reduceCtorEq]
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      simp only [BinaryTree.map, Normalized, ihl, ihr, same, ne_eq, empty]

namespace KeySet

abbrev Normalized (tree : KeySet) : Prop := Search.PositiveTrie.Normalized id tree

theorem normalized_nil : Normalized .nil := trivial

theorem normalized_add (key : PosNum) {tree : KeySet} (normal : Normalized tree) :
    Normalized (add key tree) := Search.PositiveTrie.normalized_ins id false key true tree rfl normal

theorem normalized_prune (value : Bool) {left right : KeySet}
    (normalLeft : Normalized left) (normalRight : Normalized right) :
    Normalized (prune value left right) := by
  cases value <;> cases left <;> cases right <;>
    simp_all [prune, Normalized, Search.PositiveTrie.Normalized]

theorem normalized_erase (key : PosNum) {tree : KeySet} (normal : Normalized tree) :
    Normalized (erase key tree) := by
  induction key generalizing tree with
  | one =>
      cases tree with
      | nil => trivial
      | node value left right => exact normalized_prune false normal.1 normal.2.1
  | bit0 key ih =>
      cases tree with
      | nil => trivial
      | node value left right => exact normalized_prune value (ih normal.1) normal.2.1
  | bit1 key ih =>
      cases tree with
      | nil => trivial
      | node value left right => exact normalized_prune value normal.1 (ih normal.2.1)

theorem normalized_diff {left : KeySet} (normal : Normalized left) (right : KeySet) :
    Normalized (diff left right) := by
  induction left generalizing right with
  | nil => trivial
  | node value left rightTree ihl ihr =>
      cases right with
      | nil => exact normal
      | node other otherLeft otherRight =>
          exact normalized_prune (value && !other) (ihl normal.1 otherLeft)
            (ihr normal.2.1 otherRight)

theorem exists_mem_of_normalized {tree : KeySet} (normal : Normalized tree)
    (nonempty : tree ≠ .nil) : ∃ key, mem key tree = true := by
  induction tree with
  | nil => exact (nonempty rfl).elim
  | node value left right ihl ihr =>
      cases value with
      | true => exact ⟨.one, rfl⟩
      | false =>
          rcases normal.2.2 with impossible | hl | hr
          · cases impossible
          · obtain ⟨key, present⟩ := ihl normal.1 hl
            exact ⟨.bit0 key, present⟩
          · obtain ⟨key, present⟩ := ihr normal.2.1 hr
            exact ⟨.bit1 key, present⟩

theorem cardinal_pos_of_normalized {tree : KeySet} (normal : Normalized tree)
    (nonempty : tree ≠ .nil) : 0 < cardinal tree := by
  obtain ⟨key, present⟩ := exists_mem_of_normalized normal nonempty
  have member := (mem_rawKeys key tree).mpr present
  cases keysEq : rawKeys tree with
  | nil => simp only [keysEq, List.not_mem_nil] at member
  | cons key rest => rw [← rawKeys_length, keysEq]; exact Nat.zero_lt_succ _

theorem cardinal_eq_zero_iff_of_normalized {tree : KeySet} (normal : Normalized tree) :
    cardinal tree = 0 ↔ tree = .nil := by
  constructor
  · intro zero
    by_contra nonempty
    have positive := cardinal_pos_of_normalized normal nonempty
    omega
  · rintro rfl
    rfl

def keyMass (tree : KeySet) : Nat := ((rawKeys tree).map bitLength).sum

theorem sum_bitLength_shift (lift : PosNum → PosNum)
    (lengths : ∀ key, bitLength (lift key) = bitLength key + 1) (keys : List PosNum) :
    ((keys.map lift).map bitLength).sum = (keys.map bitLength).sum + keys.length := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, lengths, ih]
      omega

theorem keyMass_node (value : Bool) (left right : KeySet) :
    keyMass (.node value left right) =
      keyMass left + keyMass right + cardinal (.node value left right) := by
  have leftMass := sum_bitLength_shift PosNum.bit0 bitLength_bit0 (rawKeys left)
  have rightMass := sum_bitLength_shift PosNum.bit1 bitLength_bit1 (rawKeys right)
  cases value <;>
    simp only [keyMass, rawKeys, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, bitLength_one, leftMass, rightMass, rawKeys_length, cardinal] <;> omega

theorem numNodes_le_keyMass {tree : KeySet} (normal : Normalized tree) :
    tree.numNodes ≤ keyMass tree := by
  induction tree with
  | nil => exact Nat.le_refl 0
  | node value left right ihl ihr =>
      have hl := ihl normal.1
      have hr := ihr normal.2.1
      have positive := cardinal_pos_of_normalized normal (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
      rw [BinaryTree.numNodes, keyMass_node]
      omega

theorem keyMass_le_cardinal_mul (tree : KeySet) (bound : Nat)
    (bounded : ∀ key, mem key tree = true → bitLength key ≤ bound) :
    keyMass tree ≤ cardinal tree * bound := by
  have h := List.sum_le_length_nsmul ((rawKeys tree).map bitLength) bound (by
    intro value member
    obtain ⟨key, inKeys, same⟩ := List.mem_map.mp member
    subst value
    exact bounded key ((mem_rawKeys key tree).mp inKeys))
  simpa only [keyMass, List.length_map, rawKeys_length, nsmul_eq_mul, Nat.cast_id] using h

theorem numNodes_le_cardinal_mul {tree : KeySet} (normal : Normalized tree) (bound : Nat)
    (bounded : ∀ key, mem key tree = true → bitLength key ≤ bound) :
    tree.numNodes ≤ cardinal tree * bound :=
  (numNodes_le_keyMass normal).trans (keyMass_le_cardinal_mul tree bound bounded)

theorem height_le_of_bitLength {tree : KeySet} (normal : Normalized tree) (bound : Nat)
    (bounded : ∀ key, mem key tree = true → bitLength key ≤ bound) :
    tree.height ≤ bound := by
  induction tree generalizing bound with
  | nil => exact Nat.zero_le _
  | node value left right ihl ihr =>
      obtain ⟨key, present⟩ := exists_mem_of_normalized normal (by
        simp only [ne_eq, reduceCtorEq, not_false_eq_true])
      have positive := bitLength_pos key
      have rootBound := bounded key present
      have hl := ihl normal.1 (bound - 1) (by
        intro k hk
        have h := bounded (.bit0 k) hk
        rw [bitLength_bit0] at h
        omega)
      have hr := ihr normal.2.1 (bound - 1) (by
        intro k hk
        have h := bounded (.bit1 k) hk
        rw [bitLength_bit1] at h
        omega)
      rw [BinaryTree.height]
      omega

theorem prefix_bitLength_le {tree : KeySet} (normal : Normalized tree)
    (nonempty : tree ≠ .nil) (pathPrefix : PosNum) (bound : Nat)
    (bounded : ∀ key, mem key tree = true → bitLength (append pathPrefix key) ≤ bound) :
    bitLength pathPrefix ≤ bound := by
  obtain ⟨key, present⟩ := exists_mem_of_normalized normal nonempty
  exact (bitLength_le_append pathPrefix key).trans (bounded key present)

end KeySet

namespace SparseMap

abbrev Normalized (tree : SparseMap α) : Prop := Search.PositiveTrie.Normalized Option.isSome tree

theorem normalized_nil : Normalized (.nil : SparseMap α) := trivial

theorem normalized_add (key : PosNum) (value : α) {tree : SparseMap α}
    (normal : Normalized tree) : Normalized (add key value tree) :=
  Search.PositiveTrie.normalized_ins Option.isSome none key (some value) tree rfl normal

theorem normalized_prune (value : Option α) {left right : SparseMap α}
    (normalLeft : Normalized left) (normalRight : Normalized right) :
    Normalized (prune value left right) := by
  cases value <;> cases left <;> cases right <;>
    simp_all [prune, Normalized, Search.PositiveTrie.Normalized]

theorem normalized_erase (key : PosNum) {tree : SparseMap α} (normal : Normalized tree) :
    Normalized (erase key tree) := by
  induction key generalizing tree with
  | one =>
      cases tree with
      | nil => trivial
      | node value left right => exact normalized_prune none normal.1 normal.2.1
  | bit0 key ih =>
      cases tree with
      | nil => trivial
      | node value left right => exact normalized_prune value (ih normal.1) normal.2.1
  | bit1 key ih =>
      cases tree with
      | nil => trivial
      | node value left right => exact normalized_prune value normal.1 (ih normal.2.1)

theorem normalized_map (label : α → β) {tree : SparseMap α} (normal : Normalized tree) :
    Normalized (map label tree) :=
  (normalized_map_iff Option.isSome Option.isSome (Option.map label)
    (fun value => by cases value <;> rfl) tree).mpr normal

/-- Keep the actual raw shape while observing only optional occupancy. -/
def occupancyTree (tree : SparseMap α) : KeySet := BinaryTree.map Option.isSome tree

theorem mem_occupancyTree (key : PosNum) (tree : SparseMap α) :
    KeySet.mem key (occupancyTree tree) = (find key tree).isSome := by
  induction key generalizing tree <;> cases tree <;>
    simp_all only [occupancyTree, BinaryTree.map, KeySet.mem_nil, find_nil,
      Option.isSome_none, KeySet.mem_one_node, find_one_node, KeySet.mem_bit0_node,
      find_bit0_node, KeySet.mem_bit1_node, find_bit1_node]

theorem normalized_occupancyTree_iff (tree : SparseMap α) :
    KeySet.Normalized (occupancyTree tree) ↔ Normalized tree :=
  normalized_map_iff Option.isSome id Option.isSome (fun _ => rfl) tree

theorem cardinal_occupancyTree (tree : SparseMap α) :
    KeySet.cardinal (occupancyTree tree) = cardinal tree := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      cases value <;> simp_all only [occupancyTree, BinaryTree.map, Option.isSome_none,
        Option.isSome_some, KeySet.cardinal, cardinal]

theorem numNodes_occupancyTree (tree : SparseMap α) :
    (occupancyTree tree).numNodes = tree.numNodes := Trees.numNodes_map Option.isSome tree

theorem height_occupancyTree (tree : SparseMap α) :
    (occupancyTree tree).height = tree.height := Trees.height_map Option.isSome tree

theorem rawKeys_occupancyTree (tree : SparseMap α) :
    KeySet.rawKeys (occupancyTree tree) = (rawEntries tree).map Prod.fst := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      cases value <;> simp_all only [occupancyTree, BinaryTree.map, Option.isSome_none,
        Option.isSome_some, KeySet.rawKeys, rawEntries, List.map_append,
        List.map_cons, List.map_map, Function.comp_def]

def keyMass (tree : SparseMap α) : Nat := ((rawEntries tree).map (fun e => bitLength e.1)).sum

theorem keyMass_occupancyTree (tree : SparseMap α) :
    KeySet.keyMass (occupancyTree tree) = keyMass tree := by
  rw [KeySet.keyMass, rawKeys_occupancyTree, List.map_map]
  rfl

theorem keyMass_node (value : Option α) (left right : SparseMap α) :
    keyMass (.node value left right) =
      keyMass left + keyMass right + cardinal (.node value left right) := by
  have h := KeySet.keyMass_node value.isSome (occupancyTree left) (occupancyTree right)
  change KeySet.keyMass (occupancyTree (.node value left right)) =
    KeySet.keyMass (occupancyTree left) + KeySet.keyMass (occupancyTree right) +
      KeySet.cardinal (occupancyTree (.node value left right)) at h
  simpa only [keyMass_occupancyTree, cardinal_occupancyTree] using h

theorem exists_find_of_normalized {tree : SparseMap α} (normal : Normalized tree)
    (nonempty : tree ≠ .nil) : ∃ key value, find key tree = some value := by
  have occupancyNonempty : occupancyTree tree ≠ .nil := by
    cases tree with
    | nil => exact (nonempty rfl).elim
    | node value left right => simp only [occupancyTree, BinaryTree.map, ne_eq, reduceCtorEq, not_false_eq_true]
  obtain ⟨key, present⟩ := KeySet.exists_mem_of_normalized
    ((normalized_occupancyTree_iff tree).mpr normal) occupancyNonempty
  rw [mem_occupancyTree] at present
  cases found : find key tree with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at present
  | some value => exact ⟨key, value, found⟩

theorem cardinal_eq_zero_iff_of_normalized {tree : SparseMap α} (normal : Normalized tree) :
    cardinal tree = 0 ↔ tree = .nil := by
  have h := KeySet.cardinal_eq_zero_iff_of_normalized
    ((normalized_occupancyTree_iff tree).mpr normal)
  rw [cardinal_occupancyTree] at h
  cases tree <;> simpa only [occupancyTree, BinaryTree.map, reduceCtorEq] using h

theorem numNodes_le_keyMass {tree : SparseMap α} (normal : Normalized tree) :
    tree.numNodes ≤ keyMass tree := by
  have h := KeySet.numNodes_le_keyMass ((normalized_occupancyTree_iff tree).mpr normal)
  simpa only [numNodes_occupancyTree, keyMass_occupancyTree] using h

theorem keyMass_le_cardinal_mul (tree : SparseMap α) (bound : Nat)
    (bounded : ∀ key value, find key tree = some value → bitLength key ≤ bound) :
    keyMass tree ≤ cardinal tree * bound := by
  have h := KeySet.keyMass_le_cardinal_mul (occupancyTree tree) bound (by
    intro key present
    rw [mem_occupancyTree] at present
    cases found : find key tree with
    | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at present
    | some value => exact bounded key value found)
  simpa only [keyMass_occupancyTree, cardinal_occupancyTree] using h

theorem numNodes_le_cardinal_mul {tree : SparseMap α} (normal : Normalized tree) (bound : Nat)
    (bounded : ∀ key value, find key tree = some value → bitLength key ≤ bound) :
    tree.numNodes ≤ cardinal tree * bound :=
  (numNodes_le_keyMass normal).trans (keyMass_le_cardinal_mul tree bound bounded)

theorem height_le_of_bitLength {tree : SparseMap α} (normal : Normalized tree) (bound : Nat)
    (bounded : ∀ key value, find key tree = some value → bitLength key ≤ bound) :
    tree.height ≤ bound := by
  have h := KeySet.height_le_of_bitLength ((normalized_occupancyTree_iff tree).mpr normal) bound (by
    intro key present
    rw [mem_occupancyTree] at present
    cases found : find key tree with
    | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at present
    | some value => exact bounded key value found)
  simpa only [height_occupancyTree] using h

theorem prefix_bitLength_le {tree : SparseMap α} (normal : Normalized tree)
    (nonempty : tree ≠ .nil) (pathPrefix : PosNum) (bound : Nat)
    (bounded : ∀ key value, find key tree = some value → bitLength (append pathPrefix key) ≤ bound) :
    bitLength pathPrefix ≤ bound := by
  obtain ⟨key, value, present⟩ := exists_find_of_normalized normal nonempty
  exact (bitLength_le_append pathPrefix key).trans (bounded key value present)

end SparseMap
end Search.PositiveTrie
