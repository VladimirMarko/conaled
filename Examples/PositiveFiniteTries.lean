import Applications.Search.PositiveTrie.Enumeration

/-!
# Finite positive tries: presence, order and choice

The cases distinguish a stored empty value from absence, raw padding from finite
content, numeric order from path order, and enumeration order from source choice.
The universal observation theorems connect the concrete calculations to clients.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PositiveFiniteTries

open Search.PositiveTrie Numerals.PositivePaths

universe u

theorem bit_order_opposes_numeric :
    BitLt (2 : PosNum) 1 ∧ ¬ (Numerals.PositiveKeys.numeric 2 < Numerals.PositiveKeys.numeric 1) := by
  change True ∧ ¬ (2 : Nat) < 1
  exact ⟨trivial, by omega⟩

theorem bit_order_crosses_root (key : PosNum) : BitLt (.bit0 key) (.bit1 key) :=
  bitLt_trans (q := .one) (by trivial) (by trivial)

theorem append_worked :
    append (.bit0 (.bit1 .one)) (.bit1 .one) = .bit0 (.bit1 (.bit1 .one)) := rfl

theorem reverse_path_roundtrip (key : PosNum) : reverse (reverse key) = key := reverse_reverse key

def storedEmpty : SparseMap KeySet := SparseMap.add 2 .nil .nil

theorem storedEmpty_present : SparseMap.find 2 storedEmpty = some .nil :=
  SparseMap.find_add_same 2 (BinaryTree.nil : KeySet) .nil

theorem storedEmpty_absent : SparseMap.find 1 storedEmpty = none := by
  rw [storedEmpty, SparseMap.find_add_other 2 1 (BinaryTree.nil : KeySet) .nil (by decide),
    SparseMap.find_nil]

theorem storedEmpty_cardinal : SparseMap.cardinal storedEmpty = 1 := rfl

theorem storedEmpty_erased_count : SparseMap.cardinal (SparseMap.erase 2 storedEmpty) = 0 := by
  have h := SparseMap.cardinal_erase_of_some 2 storedEmpty .nil storedEmpty_present
  rw [storedEmpty_cardinal] at h
  omega

theorem storedEmpty_observed : (SparseMap.observe storedEmpty).lookup 2 = some .nil := by
  rw [SparseMap.observe_lookup, storedEmpty_present]

theorem arbitrary_payload_present {α : Type u} (value : α) :
    (SparseMap.observe (SparseMap.add 2 value .nil)).lookup 2 = some value := by
  rw [SparseMap.observe_lookup, SparseMap.find_add_same]

theorem arbitrary_payload_overwrite {α : Type u} (old new : α) :
    SparseMap.find 2 (SparseMap.add 2 new (SparseMap.add 2 old .nil)) = some new :=
  SparseMap.find_add_same 2 new (SparseMap.add 2 old .nil)

/-- Function payloads do not need a decidable equality instance. -/
theorem function_payload_observed (n : Nat) :
    ((SparseMap.observe (SparseMap.add 2 (fun k : Nat => k + 1) .nil)).lookup 2).map
      (fun f => f n) = some (n + 1) := by
  rw [SparseMap.observe_lookup, SparseMap.find_add_same]
  rfl

def paddedMap : SparseMap Nat := .node none (.node none .nil .nil) .nil

/-- Pruning examines raw empty children, so erasing the root need not normalize padding. -/
theorem paddedMap_erase_root : SparseMap.erase 1 paddedMap = paddedMap := rfl

theorem paddedMap_empty_elements : SparseMap.elements paddedMap = [] := by
  rw [SparseMap.elements_eq_rawEntries]
  rfl

theorem paddedMap_not_nil : paddedMap ≠ .nil := by intro h; cases h

def paddedEmpty : KeySet := .node false .nil .nil

theorem paddedEmpty_ne_nil : paddedEmpty ≠ .nil := by intro h; cases h

theorem paddedEmpty_same_members (key : PosNum) : KeySet.mem key paddedEmpty = KeySet.mem key .nil := by
  cases key <;> simp [paddedEmpty]

theorem paddedEmpty_same_observation : KeySet.observe paddedEmpty = KeySet.observe .nil :=
  KeySet.observe_ext paddedEmpty_same_members

theorem paddedEmpty_same_elements : KeySet.elements paddedEmpty = [] :=
  KeySet.elements_ext paddedEmpty_same_members

theorem paddedEmpty_same_choice : KeySet.choose paddedEmpty = none :=
  KeySet.choose_ext paddedEmpty_same_members

theorem paddedEmpty_cardinal : KeySet.cardinal paddedEmpty = 0 := by
  rw [← KeySet.elements_length, paddedEmpty_same_elements]
  rfl

theorem paddedEmpty_raw_nodes : BinaryTree.numNodes paddedEmpty = 1 := rfl

def oneTwo : KeySet := KeySet.add 2 (KeySet.add 1 .nil)

theorem oneTwo_elements : KeySet.elements oneTwo = [2, 1] := by
  rw [KeySet.elements_eq_rawKeys]
  rfl

theorem oneTwo_choose : KeySet.choose oneTwo = some 1 := rfl

theorem oneTwo_chosen_member : (1 : PosNum) ∈ KeySet.observe oneTwo :=
  KeySet.choose_mem_observe oneTwo oneTwo_choose

theorem oneTwo_cardinal : KeySet.cardinal oneTwo = 2 := by
  rw [← KeySet.elements_length, oneTwo_elements]
  rfl

/-- The sorted first element is not the provider's root-first choice. -/
theorem oneTwo_choice_ne_first : KeySet.choose oneTwo ≠ (KeySet.elements oneTwo).head? := by
  rw [oneTwo_choose, oneTwo_elements]
  decide

/-- A noncommuting callback distinguishes the left fold from its reversal. -/
theorem oneTwo_fold_order :
    KeySet.fold (fun key acc => 10 * acc + Numerals.PositiveKeys.numeric key) oneTwo 0 = 21 := by
  rw [KeySet.fold_eq, oneTwo_elements]
  rfl

theorem repeated_add_cardinal (key : PosNum) (tree : KeySet) :
    KeySet.cardinal (KeySet.add key (KeySet.add key tree)) = KeySet.cardinal (KeySet.add key tree) := by
  rw [← KeySet.observe_card, ← KeySet.observe_card, KeySet.observe_add, KeySet.observe_add,
    Finset.insert_idem]

def sourceMap : SparseMap KeySet :=
  SparseMap.add 3 .nil (SparseMap.add 9 .nil (SparseMap.add 2 .nil .nil))

theorem sourceMap_elements : SparseMap.elements sourceMap = [(2, .nil), (9, .nil), (3, .nil)] := by
  rw [SparseMap.elements_eq_rawEntries]
  rfl

theorem sourceMap_keys_order : (SparseMap.elements sourceMap).map Prod.fst = [2, 9, 3] := by
  rw [sourceMap_elements]
  rfl

theorem sourceMap_domain_elements : KeySet.elements (SparseMap.domain sourceMap) = [2, 9, 3] := by
  rw [SparseMap.elements_domain, sourceMap_keys_order]

theorem storedEmpty_in_domain : KeySet.mem 2 (SparseMap.domain storedEmpty) = true :=
  (SparseMap.mem_domain 2 storedEmpty).mpr ⟨.nil, storedEmpty_present⟩

theorem sourceMap_cardinal : SparseMap.cardinal sourceMap = 3 := by
  rw [← SparseMap.elements_length, sourceMap_elements]
  rfl

theorem sourceMap_keys_card : (SparseMap.keys sourceMap).card = 3 := by
  rw [SparseMap.keys_card, sourceMap_cardinal]

theorem sourceMap_erased_elements :
    SparseMap.elements (SparseMap.erase 9 sourceMap) = [(2, .nil), (3, .nil)] := by
  rw [SparseMap.elements_erase, sourceMap_elements]
  rfl

theorem sourceMap_absent_erase_elements :
    SparseMap.elements (SparseMap.erase 4 sourceMap) = SparseMap.elements sourceMap := by
  rw [SparseMap.elements_erase, sourceMap_elements]
  rfl

theorem sourceMap_fold_order :
    SparseMap.fold (fun key _ acc => 10 * acc + Numerals.PositiveKeys.numeric key) sourceMap 0 = 293 := by
  rw [SparseMap.fold_eq, sourceMap_elements]
  rfl

theorem equal_values_preserve_keys :
    SparseMap.keys (SparseMap.map (fun _ : KeySet => false) sourceMap) = SparseMap.keys sourceMap :=
  SparseMap.keys_map _ sourceMap

theorem equal_values_preserve_cardinal :
    SparseMap.cardinal (SparseMap.map (fun _ : KeySet => false) sourceMap) = 3 := by
  rw [SparseMap.cardinal_map, sourceMap_cardinal]

def oneTwoThree : KeySet := KeySet.add 1 (KeySet.add 2 (KeySet.add 3 .nil))
def twoFour : KeySet := KeySet.add 2 (KeySet.add 4 .nil)

theorem difference_worked : KeySet.observe (KeySet.diff oneTwoThree twoFour) = {1, 3} := by
  rw [KeySet.observe_diff]
  decide

theorem erased_worked : KeySet.elements (KeySet.erase 2 oneTwoThree) = [1, 3] := by
  rw [KeySet.elements_erase, KeySet.elements_eq_rawKeys]
  rfl

theorem absent_erase_count :
    KeySet.cardinal (KeySet.erase 4 oneTwoThree) = KeySet.cardinal oneTwoThree :=
  KeySet.cardinal_erase_of_not_mem 4 oneTwoThree (by rfl)

end Examples.PositiveFiniteTries
