import Applications.Search.PositiveTrie.Normalized
import Applications.Resources.PositivePaths
import Applications.Resources.PositiveTrie.Finite
import Examples.ColoringSelection

/-!
# Normalized finite tries and actual path work

These cases were specified before implementation. They connect raw execution,
optional/Boolean observations, normalization, occupied bit mass and structural
bounds. The source graph and palette are the already accepted book inputs.
No whole coloring cost or physical allocation claim follows from these cases.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PositiveFiniteTrieWork

open Search.PositiveTrie Numerals.PositiveArithmetic Numerals.PositivePaths
open Resources.PositiveTrie.Finite Examples.ColoringSelection

theorem path_values : append 5 3 = 13 ∧ reverseAppend 5 3 = 14 ∧ reverse 5 = 6 := by decide

theorem path_lengths : bitLength (5 : PosNum) = 3 ∧ bitLength (3 : PosNum) = 2 ∧
    bitLength (append 5 3) = 4 ∧ bitLength (reverseAppend 5 3) = 4 := by decide

theorem append_length_client : bitLength (append 5 3) + 1 = 3 + 2 :=
  bitLength_append_add 5 3

theorem reverse_length_client : bitLength (reverseAppend 5 3) + 1 = 3 + 2 :=
  bitLength_reverseAppend_add 5 3

theorem reverse_preserves_length : bitLength (reverse 5) = 3 := bitLength_reverse 5

theorem append_run_client :
    (Resources.PositivePaths.appendRun 5 3).1 = append 5 3 ∧
      (Resources.PositivePaths.appendRun 5 3).2 = (3, 2) :=
  ⟨Resources.PositivePaths.appendRun_value 5 3, Resources.PositivePaths.appendRun_cost 5 3⟩

theorem reverseAppend_run_client :
    (Resources.PositivePaths.reverseAppendRun 5 3).1 = reverseAppend 5 3 ∧
      (Resources.PositivePaths.reverseAppendRun 5 3).2 = (3, 2) :=
  ⟨Resources.PositivePaths.reverseAppendRun_value 5 3,
    Resources.PositivePaths.reverseAppendRun_cost 5 3⟩

theorem reverse_run_client :
    (Resources.PositivePaths.reverseRun 5).1 = reverse 5 ∧
      (Resources.PositivePaths.reverseRun 5).2 = (3, 2) :=
  ⟨Resources.PositivePaths.reverseRun_value 5, Resources.PositivePaths.reverseRun_cost 5⟩

theorem path_terminal_events :
    Resources.PositivePaths.appendRun 1 7 = (7, (1, 0)) ∧
      Resources.PositivePaths.reverseAppendRun 1 7 = (7, (1, 0)) ∧
      Resources.PositivePaths.reverseRun 1 = (1, (1, 0)) := by decide

def map8 : SparseMap Nat := SparseMap.add 8 42 .nil
def set8 : KeySet := KeySet.add 8 .nil

theorem map8_normalized : SparseMap.Normalized map8 :=
  SparseMap.normalized_add 8 42 SparseMap.normalized_nil

theorem set8_normalized : KeySet.Normalized set8 :=
  KeySet.normalized_add 8 KeySet.normalized_nil

theorem map8_sizes : SparseMap.cardinal map8 = 1 ∧ map8.numNodes = 4 ∧
    SparseMap.keyMass map8 = 4 ∧ map8.height = 4 := by decide

theorem set8_sizes : KeySet.cardinal set8 = 1 ∧ set8.numNodes = 4 ∧
    KeySet.keyMass set8 = 4 ∧ set8.height = 4 := by decide

theorem singleton_key {α : Type} (key : PosNum) (value : α) (query : PosNum) (answer : α)
    (present : SparseMap.find query (SparseMap.add key value .nil) = some answer) : query = key := by
  by_contra different
  rw [SparseMap.find_add_other key query value .nil different, SparseMap.find_nil] at present
  cases present

theorem map8_bit_bound (key : PosNum) (value : Nat) (present : SparseMap.find key map8 = some value) :
    bitLength key ≤ 4 := by
  have same := singleton_key 8 42 key value present
  subst key
  decide

theorem set8_bit_bound (key : PosNum) (present : KeySet.mem key set8 = true) : bitLength key ≤ 4 := by
  have same : key = 8 := by simpa [set8, KeySet.mem_add] using present
  subst key
  decide

theorem map8_structural_bound : map8.numNodes ≤ 1 * 4 ∧ map8.height ≤ 4 :=
  ⟨SparseMap.numNodes_le_cardinal_mul map8_normalized 4 map8_bit_bound,
    SparseMap.height_le_of_bitLength map8_normalized 4 map8_bit_bound⟩

theorem set8_structural_bound : set8.numNodes ≤ 1 * 4 ∧ set8.height ≤ 4 :=
  ⟨KeySet.numNodes_le_cardinal_mul set8_normalized 4 set8_bit_bound,
    KeySet.height_le_of_bitLength set8_normalized 4 set8_bit_bound⟩

theorem empty_map_zero_bound : (BinaryTree.nil : SparseMap Nat).numNodes ≤ 0 * 0 ∧
    (BinaryTree.nil : SparseMap Nat).height ≤ 0 := by
  have bounded (key : PosNum) (value : Nat) :
      SparseMap.find key .nil = some value → bitLength key ≤ 0 := by
    simp only [SparseMap.find_nil, reduceCtorEq, false_implies]
  exact ⟨SparseMap.numNodes_le_cardinal_mul SparseMap.normalized_nil 0 bounded,
    SparseMap.height_le_of_bitLength SparseMap.normalized_nil 0 bounded⟩

theorem empty_set_zero_bound : (BinaryTree.nil : KeySet).numNodes ≤ 0 * 0 ∧
    (BinaryTree.nil : KeySet).height ≤ 0 := by
  have bounded (key : PosNum) : KeySet.mem key .nil = true → bitLength key ≤ 0 := by
    simp only [KeySet.mem_nil, Bool.false_eq_true, false_implies]
  exact ⟨KeySet.numNodes_le_cardinal_mul KeySet.normalized_nil 0 bounded,
    KeySet.height_le_of_bitLength KeySet.normalized_nil 0 bounded⟩

theorem map8_occupied_witness : ∃ key value, SparseMap.find key map8 = some value :=
  SparseMap.exists_find_of_normalized map8_normalized (by decide)

theorem set8_occupied_witness : ∃ key, KeySet.mem key set8 = true :=
  KeySet.exists_mem_of_normalized set8_normalized (by decide)

theorem map8_insert_cost : (mapAddRun 8 42 (.nil : SparseMap Nat)).2 = (4, 4) :=
  mapAddRun_cost 8 42 .nil

theorem set8_insert_cost : (setAddRun 8 .nil).2 = (4, 4) := setAddRun_cost 8 .nil

theorem map8_lookup : findRun 8 map8 = (some 42, (4, 0)) := by decide

theorem set8_lookup : memRun 8 set8 = (true, (4, 0)) := by decide

theorem map8_missing_lookup : findRun 1 map8 = (none, (1, 0)) := by decide

theorem set8_missing_lookup : memRun 1 set8 = (false, (1, 0)) := by decide

theorem map8_written_lookup_client :
    (findRun 8 (mapAddRun 8 42 (.nil : SparseMap Nat)).1).1 = some 42 ∧
      (findRun 8 (mapAddRun 8 42 (.nil : SparseMap Nat)).1).2 = (4, 0) :=
  ⟨findRun_mapAddRun_value 8 42 .nil, findRun_mapAddRun_cost 8 42 .nil⟩

theorem set8_written_lookup_client :
    (memRun 8 (setAddRun 8 .nil).1).1 = true ∧
      (memRun 8 (setAddRun 8 .nil).1).2 = (4, 0) :=
  ⟨memRun_setAddRun_value 8 .nil, memRun_setAddRun_cost 8 .nil⟩

theorem map8_composed_cost :
    (Resources.bind (mapAddRun 8 42 (.nil : SparseMap Nat)) (findRun 8)).2 = (8, 4) :=
  mapAddRun_findRun_cost 8 42 .nil

theorem set8_composed_cost :
    (Resources.bind (setAddRun 8 .nil) (memRun 8)).2 = (8, 4) := setAddRun_memRun_cost 8 .nil

def longSingleton (height : Nat) : SparseMap Nat :=
  SparseMap.add (Resources.PositiveTrie.longKey height) 42 .nil

theorem longSingleton_normalized (height : Nat) : SparseMap.Normalized (longSingleton height) :=
  SparseMap.normalized_add _ _ SparseMap.normalized_nil

theorem longSingleton_cardinal (height : Nat) : SparseMap.cardinal (longSingleton height) = 1 := by
  rw [← SparseMap.keys_card]
  change (SparseMap.keys (SparseMap.add _ _ .nil)).card = 1
  rw [SparseMap.keys_add]
  simp [SparseMap.keys, SparseMap.elements, SparseMap.elementsFrom]

theorem longSingleton_nodes (height : Nat) : (longSingleton height).numNodes = height + 1 := by
  have h := Resources.PositiveTrie.insRun_nil_numNodes (none : Option Nat)
    (Resources.PositiveTrie.longKey height) (some 42)
  simpa only [Resources.PositiveTrie.insRun_value, Resources.PositiveTrie.longKey_bitLength,
    longSingleton, SparseMap.add] using h

theorem longSingleton_write_cost (height : Nat) :
    (mapAddRun (Resources.PositiveTrie.longKey height) 42 (.nil : SparseMap Nat)).2 =
      (height + 1, height + 1) := by
  rw [mapAddRun_cost, Resources.PositiveTrie.longKey_bitLength]

theorem longSingleton_lookup_cost (height : Nat) :
    (findRun (Resources.PositiveTrie.longKey height) (longSingleton height)).2 = (height + 1, 0) := by
  have h := findRun_mapAddRun_cost (Resources.PositiveTrie.longKey height) 42 (.nil : SparseMap Nat)
  rw [mapAddRun_value, Resources.PositiveTrie.longKey_bitLength] at h
  exact h

theorem normalized_singleton_work_unbounded (bound : Nat) :
    ∃ tree : SparseMap Nat, SparseMap.Normalized tree ∧ SparseMap.cardinal tree = 1 ∧
      ∃ key, bound < (findRun key tree).2.1 := by
  refine ⟨longSingleton bound, longSingleton_normalized bound, longSingleton_cardinal bound,
    Resources.PositiveTrie.longKey bound, ?_⟩
  rw [longSingleton_lookup_cost]
  exact Nat.lt_succ_self bound

def presentEmpty : SparseMap KeySet := .node (some .nil) .nil .nil
def absentLeaf : SparseMap KeySet := .node none .nil .nil

theorem presentEmpty_normalized : SparseMap.Normalized presentEmpty := by
  simp [presentEmpty, SparseMap.Normalized, Search.PositiveTrie.Normalized]

theorem absentLeaf_not_normalized : ¬ SparseMap.Normalized absentLeaf := by
  simp [absentLeaf, SparseMap.Normalized, Search.PositiveTrie.Normalized]

theorem presentEmpty_sizes : SparseMap.cardinal presentEmpty = 1 ∧ presentEmpty.numNodes = 1 ∧
    SparseMap.keyMass presentEmpty = 1 := by decide

theorem absentLeaf_sizes : SparseMap.cardinal absentLeaf = 0 ∧ absentLeaf.numNodes = 1 ∧
    SparseMap.keyMass absentLeaf = 0 := by decide

def padding : Nat → KeySet
  | 0 => .nil
  | height + 1 => .node false (padding height) .nil

theorem padding_mem (height : Nat) (key : PosNum) : KeySet.mem key (padding height) = false := by
  induction height generalizing key with
  | zero => exact KeySet.mem_nil key
  | succ height ih => cases key <;> simp only [padding, KeySet.mem_one_node,
      KeySet.mem_bit0_node, KeySet.mem_bit1_node, KeySet.mem_nil, ih]

theorem padding_cardinal (height : Nat) : KeySet.cardinal (padding height) = 0 := by
  induction height <;> simp_all [padding, KeySet.cardinal]

theorem padding_rawKeys (height : Nat) : KeySet.rawKeys (padding height) = [] := by
  induction height <;> simp_all [padding, KeySet.rawKeys]

theorem padding_mass (height : Nat) : KeySet.keyMass (padding height) = 0 := by
  simp only [KeySet.keyMass, padding_rawKeys, List.map_nil, List.sum_nil]

theorem padding_nodes (height : Nat) : (padding height).numNodes = height := by
  induction height <;> simp_all [padding, BinaryTree.numNodes]

theorem padding_height (height : Nat) : (padding height).height = height := by
  induction height <;> simp_all [padding, BinaryTree.height]

theorem padding_normalized_iff (height : Nat) : KeySet.Normalized (padding height) ↔ height = 0 := by
  induction height with
  | zero => simp [padding, KeySet.Normalized, Search.PositiveTrie.Normalized]
  | succ height ih =>
      constructor
      · intro normal
        have zero := ih.mp normal.1
        subst height
        simp [padding, KeySet.Normalized, Search.PositiveTrie.Normalized] at normal
      · intro impossible
        omega

theorem padding3_lookup : memRun 8 (padding 3) = (false, (4, 0)) := by decide

theorem padding_breaks_cardinality_bound (bound : Nat) :
    KeySet.cardinal (padding (bound + 1)) = 0 ∧ bound < (padding (bound + 1)).numNodes := by
  rw [padding_cardinal, padding_nodes]
  exact ⟨rfl, Nat.lt_succ_self bound⟩

theorem unoccupied_insert_not_normalized :
    ¬ Search.PositiveTrie.Normalized id (ins false 1 false .nil) := by
  simp [ins, Search.PositiveTrie.Normalized]

theorem occupied_insert_normalized : KeySet.Normalized (KeySet.add 1 .nil) :=
  KeySet.normalized_add 1 KeySet.normalized_nil

theorem zero_payload_normalized : SparseMap.Normalized (SparseMap.add 1 (0 : Nat) .nil) :=
  SparseMap.normalized_add 1 0 SparseMap.normalized_nil

def twoValues : SparseMap Nat := SparseMap.add 2 9 (SparseMap.add 1 7 .nil)

theorem twoValues_normalized : SparseMap.Normalized twoValues :=
  SparseMap.normalized_add 2 9 (SparseMap.normalized_add 1 7 SparseMap.normalized_nil)

theorem constant_map_normalized : SparseMap.Normalized (SparseMap.map (fun _ : Nat => 0) twoValues) :=
  SparseMap.normalized_map _ twoValues_normalized

theorem constant_map_keys : SparseMap.keys (SparseMap.map (fun _ : Nat => 0) twoValues) =
    SparseMap.keys twoValues := SparseMap.keys_map _ twoValues

theorem constant_map_entries : SparseMap.elements (SparseMap.map (fun _ : Nat => 0) twoValues) =
    [(2, 0), (1, 0)] := by decide

theorem map8_erase : SparseMap.erase 8 map8 = .nil ∧ SparseMap.erase 1 map8 = map8 := by decide

theorem set8_erase : KeySet.erase 8 set8 = .nil ∧ KeySet.erase 1 set8 = set8 := by decide

theorem map8_erase_normalized : SparseMap.Normalized (SparseMap.erase 8 map8) ∧
    SparseMap.Normalized (SparseMap.erase 1 map8) :=
  ⟨SparseMap.normalized_erase 8 map8_normalized, SparseMap.normalized_erase 1 map8_normalized⟩

theorem set8_erase_normalized : KeySet.Normalized (KeySet.erase 8 set8) ∧
    KeySet.Normalized (KeySet.erase 1 set8) :=
  ⟨KeySet.normalized_erase 8 set8_normalized, KeySet.normalized_erase 1 set8_normalized⟩

theorem map8_erase_empty_from_cardinal : SparseMap.erase 8 map8 = .nil :=
  (SparseMap.cardinal_eq_zero_iff_of_normalized map8_erase_normalized.1).mp (by decide)

theorem set8_erase_empty_from_cardinal : KeySet.erase 8 set8 = .nil :=
  (KeySet.cardinal_eq_zero_iff_of_normalized set8_erase_normalized.1).mp (by decide)

def leftSet : KeySet := KeySet.add 2 (KeySet.add 1 .nil)

theorem leftSet_normalized : KeySet.Normalized leftSet :=
  KeySet.normalized_add 2 (KeySet.normalized_add 1 KeySet.normalized_nil)

theorem difference_right_not_normalized : ¬ KeySet.Normalized (padding 3) := by
  rw [padding_normalized_iff]
  decide

theorem difference_normalized : KeySet.Normalized (KeySet.diff leftSet (padding 3)) :=
  KeySet.normalized_diff leftSet_normalized (padding 3)

theorem difference_values : KeySet.diff leftSet (padding 3) = leftSet ∧
    KeySet.diff .nil (padding 3) = .nil ∧ KeySet.diff leftSet .nil = leftSet := by decide

theorem parent_prefix_bound : bitLength (8 : PosNum) ≤ 4 := by
  apply SparseMap.prefix_bitLength_le
    (tree := SparseMap.add 1 (7 : Nat) .nil) (SparseMap.normalized_add 1 7 SparseMap.normalized_nil)
    (by decide) 8 4
  intro key value present
  have same := singleton_key 1 7 key value present
  subst key
  decide

theorem set_parent_prefix_bound : bitLength (8 : PosNum) ≤ 4 := by
  apply KeySet.prefix_bitLength_le
    (tree := KeySet.add 1 .nil) (KeySet.normalized_add 1 KeySet.normalized_nil)
    (by decide) 8 4
  intro key present
  have same : key = 1 := by simpa [KeySet.mem_add] using present
  subst key
  decide

theorem nil_child_prefix_value : append 8 (.bit0 .one) = 16 := by decide

theorem nil_child_prefix_too_long : 4 < bitLength (append 8 (.bit0 .one)) := by
  have h := bitLength_append_add 8 (.bit0 .one)
  change bitLength (append 8 (.bit0 .one)) + 1 = 4 + 2 at h
  omega

theorem sourceGraph_normalized : SparseMap.Normalized sourceGraph := by
  simp only [sourceGraph, sourceEdges, Graphs.Coloring.mkGraph, List.foldr_cons,
    List.foldr_nil, Graphs.Coloring.addEdge]
  repeat first | apply SparseMap.normalized_add | exact SparseMap.normalized_nil

theorem palette_normalized : KeySet.Normalized palette := by
  simp only [palette, List.foldr_cons, List.foldr_nil]
  repeat first | apply KeySet.normalized_add | exact KeySet.normalized_nil

theorem sourceGraph_sizes : SparseMap.cardinal sourceGraph = 5 ∧ sourceGraph.numNodes = 6 ∧
    SparseMap.keyMass sourceGraph = 12 ∧ sourceGraph.height = 3 := by decide

theorem palette_sizes : KeySet.cardinal palette = 3 ∧ palette.numNodes = 3 ∧
    KeySet.keyMass palette = 5 ∧ palette.height = 2 := by decide

theorem sourceGraph_bit_bound (key : PosNum) (value : KeySet)
    (present : SparseMap.find key sourceGraph = some value) : bitLength key ≤ 3 := by
  have member := (KeySet.mem_elements key (Graphs.Coloring.nodes sourceGraph)).mpr
    ((Graphs.Coloring.mem_nodes sourceGraph key).mpr ⟨value, present⟩)
  rw [sourceGraph_domain] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

theorem palette_bit_bound (key : PosNum) (present : KeySet.mem key palette = true) :
    bitLength key ≤ 2 := by
  have member := (KeySet.mem_elements key palette).mpr present
  have entries : KeySet.elements palette = [2, 1, 3] := by decide
  rw [entries] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide

theorem sourceGraph_mass_bounds : sourceGraph.numNodes ≤ SparseMap.keyMass sourceGraph ∧
    SparseMap.keyMass sourceGraph ≤ 5 * 3 :=
  ⟨SparseMap.numNodes_le_keyMass sourceGraph_normalized,
    SparseMap.keyMass_le_cardinal_mul sourceGraph 3 sourceGraph_bit_bound⟩

theorem palette_mass_bounds : palette.numNodes ≤ KeySet.keyMass palette ∧
    KeySet.keyMass palette ≤ 3 * 2 :=
  ⟨KeySet.numNodes_le_keyMass palette_normalized,
    KeySet.keyMass_le_cardinal_mul palette 2 palette_bit_bound⟩

theorem sourceGraph_height_bound : sourceGraph.height ≤ 3 :=
  SparseMap.height_le_of_bitLength sourceGraph_normalized 3 sourceGraph_bit_bound

theorem palette_height_bound : palette.height ≤ 2 :=
  KeySet.height_le_of_bitLength palette_normalized 2 palette_bit_bound

end Examples.PositiveFiniteTrieWork
