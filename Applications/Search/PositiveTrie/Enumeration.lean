import Applications.Search.PositiveTrie.Finite
import Mathlib.Data.Finmap
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Sort

/-!
# Ordered finite-trie observations

The executable map traversal carries a forward prefix; the set traversal carries
a reversed prefix and an output accumulator. Both expose the same low-bit order
through proved structural observations. Their folds preserve arbitrary callback
order. Finset and Finmap are independent finite observations, not replacement
executable storage.

The provider recurrences are from Rocq Stdlib `FMapPositive` and `FSetPositive`
at `fda356e01346f7766b282ef9f44080cce2be23b3`. Upstream copyright INRIA, CNRS
and contributors; GNU LGPL version 2.1. See `docs/research/rocq-stdlib-notice.md`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Search.PositiveTrie

open Numerals.PositivePaths

universe u v

namespace SparseMap

variable {α : Type u} {σ : Type v}

/-- A structural observation used to prove properties of the source traversal. -/
def rawEntries : SparseMap α → List (PosNum × α)
  | .nil => []
  | .node none left right =>
      (rawEntries left).map (fun e => (.bit0 e.1, e.2)) ++
        (rawEntries right).map (fun e => (.bit1 e.1, e.2))
  | .node (some value) left right =>
      (rawEntries left).map (fun e => (.bit0 e.1, e.2)) ++
        (.one, value) :: (rawEntries right).map (fun e => (.bit1 e.1, e.2))

/-- The source's forward-prefix traversal, including its list append. -/
def elementsFrom : SparseMap α → PosNum → List (PosNum × α)
  | .nil, _ => []
  | .node none left right, pathPrefix =>
      elementsFrom left (append pathPrefix (.bit0 .one)) ++
        elementsFrom right (append pathPrefix (.bit1 .one))
  | .node (some value) left right, pathPrefix =>
      elementsFrom left (append pathPrefix (.bit0 .one)) ++
        (pathPrefix, value) :: elementsFrom right (append pathPrefix (.bit1 .one))

def elements (tree : SparseMap α) : List (PosNum × α) := elementsFrom tree .one

theorem elementsFrom_eq_rawEntries (tree : SparseMap α) (pathPrefix : PosNum) :
    elementsFrom tree pathPrefix =
      (rawEntries tree).map (fun e => (append pathPrefix e.1, e.2)) := by
  induction tree generalizing pathPrefix with
  | nil => rfl
  | node value left right ihl ihr =>
      cases value <;>
        simp only [elementsFrom, rawEntries, ihl, ihr, List.map_append, List.map_map,
          List.map_cons, Function.comp_def, append_bit0, append_bit1, append_one_right]

theorem elements_eq_rawEntries (tree : SparseMap α) : elements tree = rawEntries tree := by
  rw [elements, elementsFrom_eq_rawEntries]
  change (rawEntries tree).map id = rawEntries tree
  exact List.map_id _

theorem mem_rawEntries (key : PosNum) (value : α) (tree : SparseMap α) :
    (key, value) ∈ rawEntries tree ↔ find key tree = some value := by
  induction tree generalizing key with
  | nil => simp [rawEntries]
  | node root left right ihl ihr =>
      cases root <;> cases key <;>
        simp_all [rawEntries, List.mem_map, Prod.exists, Prod.mk.injEq]
      exact eq_comm

theorem mem_elements (key : PosNum) (value : α) (tree : SparseMap α) :
    (key, value) ∈ elements tree ↔ find key tree = some value := by
  rw [elements_eq_rawEntries, mem_rawEntries]

theorem rawEntries_pairwise (tree : SparseMap α) :
    (rawEntries tree).Pairwise (fun x y => BitLt x.1 y.1) := by
  induction tree with
  | nil => exact List.Pairwise.nil
  | node value left right ihl ihr =>
      have hl : ((rawEntries left).map (fun e => (PosNum.bit0 e.1, e.2))).Pairwise
          (fun x y => BitLt x.1 y.1) := ihl.map _ (fun _ _ h => h)
      have hr : ((rawEntries right).map (fun e => (PosNum.bit1 e.1, e.2))).Pairwise
          (fun x y => BitLt x.1 y.1) := ihr.map _ (fun _ _ h => h)
      cases value with
      | none =>
          apply List.pairwise_append.mpr
          refine ⟨hl, hr, ?_⟩
          intro a ha b hb
          rcases List.mem_map.mp ha with ⟨x, _, rfl⟩
          rcases List.mem_map.mp hb with ⟨y, _, rfl⟩
          trivial
      | some value =>
          apply List.pairwise_append.mpr
          refine ⟨hl, List.pairwise_cons.mpr ⟨?_, hr⟩, ?_⟩
          · intro b hb
            rcases List.mem_map.mp hb with ⟨y, _, rfl⟩
            trivial
          · intro a ha b hb
            rcases List.mem_map.mp ha with ⟨x, _, rfl⟩
            rcases List.mem_cons.mp hb with h | hb
            · subst b
              trivial
            · rcases List.mem_map.mp hb with ⟨y, _, rfl⟩
              trivial

theorem elements_pairwise (tree : SparseMap α) :
    (elements tree).Pairwise (fun x y => BitLt x.1 y.1) := by
  rw [elements_eq_rawEntries]
  exact rawEntries_pairwise tree

theorem keys_pairwise (tree : SparseMap α) :
    ((elements tree).map Prod.fst).Pairwise BitLt := by
  simpa only [List.pairwise_map] using elements_pairwise tree

theorem keys_nodup (tree : SparseMap α) : ((elements tree).map Prod.fst).Nodup := by
  let : Std.Irrefl BitLt := ⟨bitLt_irrefl⟩
  exact (keys_pairwise tree).nodup

theorem rawEntries_length (tree : SparseMap α) : (rawEntries tree).length = cardinal tree := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      cases value <;>
        simp only [rawEntries, cardinal, List.length_append, List.length_map, List.length_cons, ihl, ihr]
      omega

theorem elements_length (tree : SparseMap α) : (elements tree).length = cardinal tree := by
  rw [elements_eq_rawEntries, rawEntries_length]

def keys (tree : SparseMap α) : Finset PosNum := ((elements tree).map Prod.fst).toFinset

theorem mem_keys (key : PosNum) (tree : SparseMap α) :
    key ∈ keys tree ↔ ∃ value, find key tree = some value := by
  simp only [keys, List.mem_toFinset, List.mem_map, Prod.exists]
  constructor
  · rintro ⟨k, value, h, hk⟩
    subst k
    exact ⟨value, (mem_elements key value tree).mp h⟩
  · rintro ⟨value, h⟩
    exact ⟨key, value, (mem_elements key value tree).mpr h, rfl⟩

theorem keys_isSome (key : PosNum) (tree : SparseMap α) :
    (find key tree).isSome ↔ key ∈ keys tree := by
  rw [mem_keys, Option.isSome_iff_exists]

theorem keys_card (tree : SparseMap α) : (keys tree).card = cardinal tree := by
  rw [keys, List.toFinset_card_of_nodup (keys_nodup tree), List.length_map, elements_length]

/-- Finite optional lookup is the existing Finmap contract, without payload equality. -/
def observe (tree : SparseMap α) : Finmap (fun _ : PosNum => α) :=
  Finmap.keysLookupEquiv.symm ⟨(keys tree, fun key => find key tree), fun key => keys_isSome key tree⟩

@[simp] theorem observe_lookup (tree : SparseMap α) (key : PosNum) :
    (observe tree).lookup key = find key tree := Finmap.keysLookupEquiv_symm_apply_lookup _ key

@[simp] theorem observe_keys (tree : SparseMap α) : (observe tree).keys = keys tree :=
  Finmap.keysLookupEquiv_symm_apply_keys _

theorem observe_ext {left right : SparseMap α} (same : ∀ key, find key left = find key right) :
    observe left = observe right := by
  apply Finmap.ext_lookup
  intro key
  simpa only [observe_lookup] using same key

theorem observe_nil : observe (.nil : SparseMap α) = ∅ := by
  apply Finmap.ext_lookup
  intro key
  rw [observe_lookup, find_nil, Finmap.lookup_empty]

theorem observe_add (key : PosNum) (value : α) (tree : SparseMap α) :
    observe (add key value tree) = Finmap.insert key value (observe tree) := by
  apply Finmap.ext_lookup
  intro query
  by_cases h : query = key
  · subst query
    rw [observe_lookup, find_add_same, Finmap.lookup_insert]
  · rw [observe_lookup, find_add_other key query value tree h,
      Finmap.lookup_insert_of_ne _ h, observe_lookup]

theorem observe_erase (key : PosNum) (tree : SparseMap α) :
    observe (erase key tree) = Finmap.erase key (observe tree) := by
  apply Finmap.ext_lookup
  intro query
  by_cases h : query = key
  · subst query
    rw [observe_lookup, find_erase_same, Finmap.lookup_erase]
  · rw [observe_lookup, find_erase_other key query tree h, Finmap.lookup_erase_ne h, observe_lookup]

theorem keys_add (key : PosNum) (value : α) (tree : SparseMap α) :
    keys (add key value tree) = Insert.insert key (keys tree) := by
  ext query
  by_cases h : query = key <;> simp [mem_keys, find_add, h]

theorem keys_erase (key : PosNum) (tree : SparseMap α) :
    keys (erase key tree) = (keys tree).erase key := by
  rw [← observe_keys, observe_erase, Finmap.keys_erase, observe_keys]

theorem cardinal_erase_lt_of_mem (key : PosNum) (tree : SparseMap α) (present : key ∈ keys tree) :
    cardinal (erase key tree) < cardinal tree := by
  obtain ⟨value, hv⟩ := (mem_keys key tree).mp present
  exact cardinal_erase_lt key tree value hv

theorem rawEntries_map {β : Type v} (f : α → β) (tree : SparseMap α) :
    rawEntries (map f tree) = (rawEntries tree).map (fun e => (e.1, f e.2)) := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      cases value <;> simp_all [map, BinaryTree.map, rawEntries, List.map_map, Function.comp_def]

theorem elements_map {β : Type v} (f : α → β) (tree : SparseMap α) :
    elements (map f tree) = (elements tree).map (fun e => (e.1, f e.2)) := by
  rw [elements_eq_rawEntries, elements_eq_rawEntries, rawEntries_map]

theorem elements_ext {left right : SparseMap α} (same : ∀ key, find key left = find key right) :
    elements left = elements right := by
  let : Std.Irrefl (fun x y : PosNum × α => BitLt x.1 y.1) := ⟨fun _ => bitLt_irrefl _⟩
  let : Std.Antisymm (fun x y : PosNum × α => BitLt x.1 y.1) :=
    ⟨fun _ _ h h' => (bitLt_asymm h h').elim⟩
  apply List.Pairwise.eq_of_mem_iff (elements_pairwise left) (elements_pairwise right)
  rintro ⟨key, value⟩
  rw [mem_elements, mem_elements, same key]

theorem elements_erase (key : PosNum) (tree : SparseMap α) :
    elements (erase key tree) = (elements tree).filter (fun e => decide (e.1 ≠ key)) := by
  let : Std.Irrefl (fun x y : PosNum × α => BitLt x.1 y.1) := ⟨fun _ => bitLt_irrefl _⟩
  let : Std.Antisymm (fun x y : PosNum × α => BitLt x.1 y.1) :=
    ⟨fun _ _ h h' => (bitLt_asymm h h').elim⟩
  apply List.Pairwise.eq_of_mem_iff (elements_pairwise _) ((elements_pairwise tree).filter _)
  rintro ⟨query, value⟩
  by_cases h : query = key <;> simp [mem_elements, find_erase, h]

theorem elements_erase_of_mem (key : PosNum) (tree : SparseMap α) (_present : key ∈ keys tree) :
    elements (erase key tree) = (elements tree).filter (fun e => decide (e.1 ≠ key)) :=
  elements_erase key tree

theorem keys_map {β : Type v} (f : α → β) (tree : SparseMap α) :
    keys (map f tree) = keys tree := by
  ext key
  rw [← keys_isSome, ← keys_isSome, find_map]
  cases find key tree <;> simp

/-- Source ordered map fold: recurse left, process the root, recurse right. -/
def foldFrom (f : PosNum → α → σ → σ) : SparseMap α → σ → PosNum → σ
  | .nil, acc, _ => acc
  | .node none left right, acc, pathPrefix =>
      foldFrom f right (foldFrom f left acc (append pathPrefix (.bit0 .one)))
        (append pathPrefix (.bit1 .one))
  | .node (some value) left right, acc, pathPrefix =>
      foldFrom f right (f pathPrefix value (foldFrom f left acc (append pathPrefix (.bit0 .one))))
        (append pathPrefix (.bit1 .one))

def fold (f : PosNum → α → σ → σ) (tree : SparseMap α) (acc : σ) : σ :=
  foldFrom f tree acc .one

theorem foldFrom_eq (f : PosNum → α → σ → σ) (tree : SparseMap α) (acc : σ)
    (pathPrefix : PosNum) :
    foldFrom f tree acc pathPrefix =
      (elementsFrom tree pathPrefix).foldl (fun a e => f e.1 e.2 a) acc := by
  induction tree generalizing acc pathPrefix with
  | nil => rfl
  | node value left right ihl ihr =>
      cases value <;> simp only [foldFrom, elementsFrom, List.foldl_append, List.foldl_cons, ihl, ihr]

theorem fold_eq (f : PosNum → α → σ → σ) (tree : SparseMap α) (acc : σ) :
    fold f tree acc = (elements tree).foldl (fun a e => f e.1 e.2 a) acc :=
  foldFrom_eq f tree acc .one

end SparseMap

namespace KeySet

variable {σ : Type u}

def rawKeys : KeySet → List PosNum
  | .nil => []
  | .node false left right => (rawKeys left).map .bit0 ++ (rawKeys right).map .bit1
  | .node true left right => (rawKeys left).map .bit0 ++ .one :: (rawKeys right).map .bit1

/-- Source set enumeration with a reversed prefix and output tail. -/
def elementsAcc : KeySet → PosNum → List PosNum → List PosNum
  | .nil, _, tail => tail
  | .node false left right, reversedPrefix, tail =>
      elementsAcc left (.bit0 reversedPrefix) (elementsAcc right (.bit1 reversedPrefix) tail)
  | .node true left right, reversedPrefix, tail =>
      elementsAcc left (.bit0 reversedPrefix)
        (reverse reversedPrefix :: elementsAcc right (.bit1 reversedPrefix) tail)

def elements (tree : KeySet) : List PosNum := elementsAcc tree .one []

theorem elementsAcc_eq_rawKeys (tree : KeySet) (reversedPrefix : PosNum) (tail : List PosNum) :
    elementsAcc tree reversedPrefix tail = (rawKeys tree).map (reverseAppend reversedPrefix) ++ tail := by
  induction tree generalizing reversedPrefix tail with
  | nil => rfl
  | node value left right ihl ihr =>
      cases value <;>
        simp only [elementsAcc, rawKeys, ihl, ihr, List.map_append, List.map_map,
          List.map_cons, List.append_assoc, List.cons_append, Function.comp_def, reverse, reverseAppend]

theorem elements_eq_rawKeys (tree : KeySet) : elements tree = rawKeys tree := by
  rw [elements, elementsAcc_eq_rawKeys]
  change (rawKeys tree).map id ++ [] = rawKeys tree
  rw [List.map_id, List.append_nil]

theorem mem_rawKeys (key : PosNum) (tree : KeySet) : key ∈ rawKeys tree ↔ mem key tree = true := by
  induction tree generalizing key with
  | nil => simp [rawKeys]
  | node value left right ihl ihr => cases value <;> cases key <;> simp_all [rawKeys]

theorem mem_elements (key : PosNum) (tree : KeySet) : key ∈ elements tree ↔ mem key tree = true := by
  rw [elements_eq_rawKeys, mem_rawKeys]

theorem rawKeys_pairwise (tree : KeySet) : (rawKeys tree).Pairwise BitLt := by
  induction tree with
  | nil => exact List.Pairwise.nil
  | node value left right ihl ihr =>
      cases value <;>
        simpa [rawKeys, List.pairwise_append, List.pairwise_map, List.forall_mem_map, BitLt]
          using And.intro ihl ihr

theorem elements_pairwise (tree : KeySet) : (elements tree).Pairwise BitLt := by
  rw [elements_eq_rawKeys]
  exact rawKeys_pairwise tree

theorem elements_nodup (tree : KeySet) : (elements tree).Nodup := by
  let : Std.Irrefl BitLt := ⟨bitLt_irrefl⟩
  exact (elements_pairwise tree).nodup

theorem rawKeys_length (tree : KeySet) : (rawKeys tree).length = cardinal tree := by
  induction tree with
  | nil => rfl
  | node value left right ihl ihr =>
      cases value <;>
        simp only [rawKeys, cardinal, List.length_append, List.length_map, List.length_cons, ihl, ihr]
      omega

theorem elements_length (tree : KeySet) : (elements tree).length = cardinal tree := by
  rw [elements_eq_rawKeys, rawKeys_length]

def observe (tree : KeySet) : Finset PosNum := (elements tree).toFinset

@[simp] theorem observe_nil : observe .nil = ∅ := rfl

@[simp] theorem mem_observe (key : PosNum) (tree : KeySet) :
    key ∈ observe tree ↔ mem key tree = true := by simp [observe, mem_elements]

theorem observe_card (tree : KeySet) : (observe tree).card = cardinal tree := by
  rw [observe, List.toFinset_card_of_nodup (elements_nodup tree), elements_length]

theorem observe_ext {left right : KeySet} (same : ∀ key, mem key left = mem key right) :
    observe left = observe right := by
  ext key
  rw [mem_observe, mem_observe, same key]

theorem elements_ext {left right : KeySet} (same : ∀ key, mem key left = mem key right) :
    elements left = elements right := by
  let : Std.Irrefl BitLt := ⟨bitLt_irrefl⟩
  let : Std.Antisymm BitLt := ⟨fun _ _ h h' => (bitLt_asymm h h').elim⟩
  apply List.Pairwise.eq_of_mem_iff (elements_pairwise left) (elements_pairwise right)
  intro key
  rw [mem_elements, mem_elements, same key]

theorem elements_erase (key : PosNum) (tree : KeySet) :
    elements (erase key tree) = (elements tree).filter (fun k => decide (k ≠ key)) := by
  let : Std.Irrefl BitLt := ⟨bitLt_irrefl⟩
  let : Std.Antisymm BitLt := ⟨fun _ _ h h' => (bitLt_asymm h h').elim⟩
  apply List.Pairwise.eq_of_mem_iff (elements_pairwise _) ((elements_pairwise tree).filter _)
  intro query
  by_cases h : query = key <;> simp [mem_elements, mem_erase, h]

theorem elements_erase_of_mem (key : PosNum) (tree : KeySet) (_present : mem key tree = true) :
    elements (erase key tree) = (elements tree).filter (fun k => decide (k ≠ key)) :=
  elements_erase key tree

theorem observe_add (key : PosNum) (tree : KeySet) :
    observe (add key tree) = Insert.insert key (observe tree) := by
  ext query
  simp [mem_add]

theorem observe_erase (key : PosNum) (tree : KeySet) :
    observe (erase key tree) = (observe tree).erase key := by
  ext query
  by_cases h : query = key <;> simp [mem_erase, h]

theorem observe_diff (left right : KeySet) : observe (diff left right) = observe left \ observe right := by
  ext key
  simp [mem_diff]

theorem choose_none_iff_observe_empty (tree : KeySet) : choose tree = none ↔ observe tree = ∅ := by
  rw [choose_none_iff, Finset.eq_empty_iff_forall_notMem]
  simp

theorem choose_mem_observe (tree : KeySet) {key : PosNum} (chosen : choose tree = some key) :
    key ∈ observe tree := (mem_observe key tree).mpr (choose_mem tree chosen)

def foldFrom (f : PosNum → σ → σ) : KeySet → σ → PosNum → σ
  | .nil, acc, _ => acc
  | .node false left right, acc, reversedPrefix =>
      foldFrom f right (foldFrom f left acc (.bit0 reversedPrefix)) (.bit1 reversedPrefix)
  | .node true left right, acc, reversedPrefix =>
      foldFrom f right (f (reverse reversedPrefix) (foldFrom f left acc (.bit0 reversedPrefix)))
        (.bit1 reversedPrefix)

def fold (f : PosNum → σ → σ) (tree : KeySet) (acc : σ) : σ := foldFrom f tree acc .one

theorem foldl_elementsAcc (f : PosNum → σ → σ) (tree : KeySet) (reversedPrefix : PosNum)
    (tail : List PosNum) (acc : σ) :
    (elementsAcc tree reversedPrefix tail).foldl (fun a key => f key a) acc =
      tail.foldl (fun a key => f key a) (foldFrom f tree acc reversedPrefix) := by
  induction tree generalizing reversedPrefix tail acc with
  | nil => rfl
  | node value left right ihl ihr =>
      cases value <;> simp only [elementsAcc, foldFrom, ihl, ihr, List.foldl_cons]

theorem fold_eq (f : PosNum → σ → σ) (tree : KeySet) (acc : σ) :
    fold f tree acc = (elements tree).foldl (fun a key => f key a) acc := by
  simpa only [fold, elements, List.foldl_nil] using (foldl_elementsAcc f tree .one [] acc).symm

theorem foldl_add_observe (keys : List PosNum) (acc : KeySet) :
    observe (keys.foldl (fun s key => add key s) acc) = keys.toFinset ∪ observe acc := by
  induction keys generalizing acc with
  | nil => simp
  | cons key keys ih =>
      simpa only [List.foldl_cons, List.toFinset_cons, observe_add, Finset.union_insert,
        Finset.insert_union] using ih (add key acc)

end KeySet

namespace SparseMap

variable {α : Type u}

/-- The source `Mdomain`: ordered map fold inserting every occupied key. -/
def domain (tree : SparseMap α) : KeySet :=
  fold (fun key _ acc => KeySet.add key acc) tree .nil

theorem observe_domain (tree : SparseMap α) : KeySet.observe (domain tree) = keys tree := by
  rw [domain, fold_eq]
  have h : (elements tree).foldl (fun acc e => KeySet.add e.1 acc) .nil =
      ((elements tree).map Prod.fst).foldl (fun acc key => KeySet.add key acc) .nil :=
    (List.foldl_map (f := Prod.fst) (g := fun acc key => KeySet.add key acc)).symm
  rw [h, KeySet.foldl_add_observe, KeySet.observe_nil, Finset.union_empty]
  rfl

theorem mem_domain (key : PosNum) (tree : SparseMap α) :
    KeySet.mem key (domain tree) = true ↔ ∃ value, find key tree = some value := by
  rw [← KeySet.mem_observe, observe_domain, mem_keys]

theorem cardinal_domain (tree : SparseMap α) : KeySet.cardinal (domain tree) = cardinal tree := by
  rw [← KeySet.observe_card, observe_domain, keys_card]

theorem elements_domain (tree : SparseMap α) :
    KeySet.elements (domain tree) = (elements tree).map Prod.fst := by
  let : Std.Irrefl BitLt := ⟨bitLt_irrefl⟩
  let : Std.Antisymm BitLt := ⟨fun _ _ h h' => (bitLt_asymm h h').elim⟩
  apply List.Pairwise.eq_of_mem_iff (KeySet.elements_pairwise _) (keys_pairwise tree)
  intro key
  rw [KeySet.mem_elements, ← KeySet.mem_observe, observe_domain]
  simp only [keys, List.mem_toFinset]

end SparseMap
end Search.PositiveTrie
