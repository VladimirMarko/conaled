import Applications.Search.PositiveTrie.Normalized
import Mathlib.Tactic.Ring

/-!
# Mathematical masses for literal finite-trie traversals

Raw prefix mass includes unoccupied nodes. Reversal mass includes only occupied
set keys. Copied cells count occupied left outputs, not raw left-subtree size.
These are proof observations; none is inserted into an executable traversal.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.PositiveTrie.Traversal

open Search.PositiveTrie Numerals.PositiveArithmetic Numerals.PositivePaths

universe u v
variable {α : Type u} {β : Type v}

def pathMass : BinaryTree α → Nat
  | .nil => 0
  | .node _ left right => pathMass left + pathMass right + left.numNodes + right.numNodes + 1

def prefixMass (tree : BinaryTree α) (pathPrefix : PosNum) : Nat :=
  pathMass tree + tree.numNodes * (bitLength pathPrefix - 1)

theorem prefixMass_nil (pathPrefix : PosNum) :
    prefixMass (.nil : BinaryTree α) pathPrefix = 0 := by
  simp [prefixMass, pathMass, BinaryTree.numNodes]

theorem prefixMass_one (tree : BinaryTree α) : prefixMass tree .one = pathMass tree := by
  simp [prefixMass]

theorem prefixMass_shift (tree : BinaryTree α) (pathPrefix : PosNum) :
    prefixMass tree pathPrefix = prefixMass tree .one + tree.numNodes * (bitLength pathPrefix - 1) := by
  rw [prefixMass_one]
  rfl

theorem numNodes_le_pathMass (tree : BinaryTree α) : tree.numNodes ≤ pathMass tree := by
  cases tree <;> simp only [BinaryTree.numNodes, pathMass] <;> omega

theorem numNodes_le_prefixMass (tree : BinaryTree α) (pathPrefix : PosNum) :
    tree.numNodes ≤ prefixMass tree pathPrefix := by
  have h := numNodes_le_pathMass tree
  dsimp only [prefixMass]
  omega

theorem mul_bitLength (n : Nat) (p : PosNum) :
    n * bitLength p = n * (bitLength p - 1) + n := by
  have hp : bitLength p = (bitLength p - 1) + 1 := by have h := bitLength_pos p; omega
  calc
    _ = n * ((bitLength p - 1) + 1) := congrArg (n * ·) hp
    _ = _ := by ring

theorem prefixMass_node (value : α) (left right : BinaryTree α) (p : PosNum) :
    prefixMass (.node value left right) p = bitLength p +
      prefixMass left (append p (.bit0 .one)) + prefixMass right (append p (.bit1 .one)) := by
  have hl : bitLength (append p (.bit0 .one)) - 1 = bitLength p := by
    have h := bitLength_append_add p (.bit0 .one)
    simp only [bitLength_bit0, bitLength_one] at h
    omega
  have hr : bitLength (append p (.bit1 .one)) - 1 = bitLength p := by
    have h := bitLength_append_add p (.bit1 .one)
    simp only [bitLength_bit1, bitLength_one] at h
    omega
  have positive := bitLength_pos p
  simp only [prefixMass, pathMass, BinaryTree.numNodes, hl, hr, Nat.add_mul,
    Nat.one_mul, mul_bitLength]
  omega

theorem pathMass_map (label : α → β) (tree : BinaryTree α) :
    pathMass (BinaryTree.map label tree) = pathMass tree := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      simp only [BinaryTree.map, pathMass, ihl, ihr, Trees.numNodes_map]

theorem prefixMass_map (label : α → β) (tree : BinaryTree α) (p : PosNum) :
    prefixMass (BinaryTree.map label tree) p = prefixMass tree p := by
  simp only [prefixMass, pathMass_map, Trees.numNodes_map]

theorem set_prefixMass_le {tree : KeySet} (normal : KeySet.Normalized tree)
    (p : PosNum) (bound : Nat)
    (bounded : ∀ key, KeySet.mem key tree = true → bitLength (append p key) ≤ bound) :
    prefixMass tree p ≤ tree.numNodes * bound := by
  induction tree generalizing p with
  | nil => simp only [prefixMass_nil, BinaryTree.numNodes, Nat.zero_mul, Nat.le_refl]
  | node value left right ihl ihr =>
      have hp := KeySet.prefix_bitLength_le normal (by simp) p bound bounded
      have hl := ihl normal.1 (append p (.bit0 .one)) (by
        intro key present
        simpa only [append_bit0] using bounded (.bit0 key) present)
      have hr := ihr normal.2.1 (append p (.bit1 .one)) (by
        intro key present
        simpa only [append_bit1] using bounded (.bit1 key) present)
      rw [prefixMass_node, BinaryTree.numNodes, Nat.add_mul, Nat.add_mul, Nat.one_mul]
      omega

theorem map_prefixMass_le {tree : SparseMap α} (normal : SparseMap.Normalized tree)
    (p : PosNum) (bound : Nat)
    (bounded : ∀ key value, SparseMap.find key tree = some value →
      bitLength (append p key) ≤ bound) :
    prefixMass tree p ≤ tree.numNodes * bound := by
  have h := set_prefixMass_le ((SparseMap.normalized_occupancyTree_iff tree).mpr normal)
    p bound (by
      intro key present
      rw [SparseMap.mem_occupancyTree] at present
      cases found : SparseMap.find key tree with
      | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at present
      | some value => exact bounded key value found)
  simpa only [SparseMap.occupancyTree, prefixMass_map, Trees.numNodes_map] using h

theorem map_prefixMass_one_le {tree : SparseMap α} (normal : SparseMap.Normalized tree)
    (bound : Nat)
    (bounded : ∀ key value, SparseMap.find key tree = some value → bitLength key ≤ bound) :
    prefixMass tree .one ≤ SparseMap.cardinal tree * bound ^ 2 := by
  have hn := SparseMap.numNodes_le_cardinal_mul normal bound bounded
  calc
    _ ≤ tree.numNodes * bound := map_prefixMass_le normal .one bound bounded
    _ ≤ (SparseMap.cardinal tree * bound) * bound := Nat.mul_le_mul_right bound hn
    _ = _ := by ring

def reversalMass (tree : KeySet) (reversedPrefix : PosNum) : Nat :=
  KeySet.keyMass tree + KeySet.cardinal tree * (bitLength reversedPrefix - 1)

theorem reversalMass_nil (r : PosNum) : reversalMass .nil r = 0 := by
  simp [reversalMass, KeySet.keyMass, KeySet.rawKeys, KeySet.cardinal]

theorem reversalMass_one (tree : KeySet) : reversalMass tree .one = KeySet.keyMass tree := by
  simp [reversalMass]

theorem reversalMass_shift (tree : KeySet) (r : PosNum) :
    reversalMass tree r = KeySet.keyMass tree + KeySet.cardinal tree * (bitLength r - 1) := rfl

theorem reversalMass_node (value : Bool) (left right : KeySet) (r : PosNum) :
    reversalMass (.node value left right) r = reversalMass left (.bit0 r) +
      (if value then bitLength r else 0) + reversalMass right (.bit1 r) := by
  have positive := bitLength_pos r
  cases value <;>
    simp only [reversalMass, KeySet.keyMass_node, KeySet.cardinal, Bool.false_eq_true,
      ↓reduceIte, bitLength_bit0, bitLength_bit1, Nat.add_sub_cancel, Nat.add_mul,
      Nat.one_mul, mul_bitLength] <;> omega

theorem reversalMass_eq_sum (tree : KeySet) (r : PosNum) :
    reversalMass tree r =
      ((KeySet.rawKeys tree).map (fun key => bitLength (reverseAppend r key))).sum := by
  have lengthLaw (key : PosNum) :
      bitLength (reverseAppend r key) = bitLength key + (bitLength r - 1) := by
    have h := bitLength_reverseAppend_add r key
    have positive := bitLength_pos r
    omega
  have sumLaw (keys : List PosNum) :
      (keys.map (fun key => bitLength (reverseAppend r key))).sum =
        (keys.map bitLength).sum + keys.length * (bitLength r - 1) := by
    induction keys with
    | nil => simp
    | cons key keys ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [ih, lengthLaw]
        simp only [Nat.add_mul, Nat.one_mul]
        omega
  rw [sumLaw, KeySet.rawKeys_length]
  rfl

theorem cardinal_le_reversalMass (tree : KeySet) (r : PosNum) :
    KeySet.cardinal tree ≤ reversalMass tree r := by
  have h : KeySet.cardinal tree ≤ KeySet.keyMass tree := by
    cases tree with
    | nil => exact Nat.le_refl 0
    | node value left right => rw [KeySet.keyMass_node]; omega
  dsimp only [reversalMass]
  omega

theorem reversalMass_le (tree : KeySet) (r : PosNum) (bound : Nat)
    (bounded : ∀ key, KeySet.mem key tree = true → bitLength (reverseAppend r key) ≤ bound) :
    reversalMass tree r ≤ KeySet.cardinal tree * bound := by
  rw [reversalMass_eq_sum]
  have h := List.sum_le_length_nsmul
    ((KeySet.rawKeys tree).map (fun key => bitLength (reverseAppend r key))) bound (by
      intro value member
      obtain ⟨key, present, rfl⟩ := List.mem_map.mp member
      exact bounded key ((KeySet.mem_rawKeys key tree).mp present))
  simpa only [List.length_map, KeySet.rawKeys_length, nsmul_eq_mul, Nat.cast_id] using h

def copiedCells : SparseMap α → Nat
  | .nil => 0
  | .node _ left right => copiedCells left + copiedCells right + SparseMap.cardinal left

theorem copiedCells_add_cardinal_le (tree : SparseMap α) :
    copiedCells tree + SparseMap.cardinal tree ≤ SparseMap.keyMass tree := by
  induction tree with
  | nil => exact Nat.le_refl 0
  | node value left right ihl ihr =>
      rw [copiedCells, SparseMap.keyMass_node]
      cases value <;> simp only [SparseMap.cardinal] <;> omega

theorem copiedCells_le (tree : SparseMap α) (bound : Nat)
    (bounded : ∀ key value, SparseMap.find key tree = some value → bitLength key ≤ bound) :
    copiedCells tree ≤ SparseMap.cardinal tree * bound := by
  have h := copiedCells_add_cardinal_le tree
  have mass := SparseMap.keyMass_le_cardinal_mul tree bound bounded
  omega

end Resources.PositiveTrie.Traversal
