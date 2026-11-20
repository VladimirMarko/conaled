import Applications.Search.PositiveTrie.Enumeration
import Applications.Sequences.RelatedMembership

/-!
# Related-list adapters for positive finite tries

The source key carrier and equality are definitionally PosNum and ordinary
equality. Pair equality includes both key and value, while pair ordering uses
only the key. These adapters retain source adjacent sortedness and pointwise
related lists without adding an order or equality decision on payloads.

See `docs/research/vfa-color.md` for the VFA/Rocq source correspondence and
`docs/research/rocq-stdlib-notice.md` for the provider attribution.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Search.PositiveTrie

open Numerals.PositivePaths Sequences.RelatedMembership

universe u v

namespace Relations

variable {α : Type u}

/-- The source positive-key view; this abbreviation introduces no new carrier. -/
abbrev Key := PosNum

abbrev KeyEq : Key → Key → Prop := Eq

theorem key_eq_posNum : Key = PosNum := rfl

theorem keyEq_eq : KeyEq = @Eq PosNum := rfl

theorem keyEq_equivalence : Equivalence KeyEq :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

theorem forall₂_keyEq_iff_eq (xs ys : List Key) : List.Forall₂ KeyEq xs ys ↔ xs = ys :=
  forall₂_eq_iff xs ys

theorem isChain_bitLt_iff_pairwise (xs : List Key) : xs.IsChain BitLt ↔ xs.Pairwise BitLt :=
  isChain_iff_pairwise_of_trans (S := BitLt) bitLt_trans xs

theorem isChain_bitLt_filter (f : Key → Bool) {xs : List Key} (sorted : xs.IsChain BitLt) :
    (xs.filter f).IsChain BitLt :=
  isChain_filter_of_trans (S := BitLt) bitLt_trans f sorted

theorem forall₂_keyEq_of_sorted {xs ys : List Key}
    (sortedXs : xs.IsChain BitLt) (sortedYs : ys.IsChain BitLt)
    (sameMembers : SameRelatedMembers KeyEq xs ys) : List.Forall₂ KeyEq xs ys := by
  apply forall₂_of_isChain_of_sameRelatedMembers (S := BitLt)
    keyEq_equivalence bitLt_irrefl bitLt_trans _ sortedXs sortedYs sameMembers
  rintro a a' b b' rfl rfl
  rfl

theorem eq_of_bitSorted_sameRelated {xs ys : List Key}
    (sortedXs : xs.IsChain BitLt) (sortedYs : ys.IsChain BitLt)
    (sameMembers : SameRelatedMembers KeyEq xs ys) : xs = ys :=
  (forall₂_keyEq_iff_eq xs ys).mp (forall₂_keyEq_of_sorted sortedXs sortedYs sameMembers)

/-- The source map relation compares the value as well as the key. -/
def EqKeyValue (a b : Key × α) : Prop := a.1 = b.1 ∧ a.2 = b.2

@[simp] theorem eqKeyValue_iff_eq (a b : Key × α) : EqKeyValue a b ↔ a = b := by
  constructor
  · exact fun h => Prod.ext h.1 h.2
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem eqKeyValue_eq : EqKeyValue (α := α) = Eq := by
  funext a b
  exact propext (eqKeyValue_iff_eq a b)

theorem eqKeyValue_equivalence : Equivalence (EqKeyValue (α := α)) := by
  rw [eqKeyValue_eq]
  exact ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

def KeyLt (a b : Key × α) : Prop := BitLt a.1 b.1

theorem keyLt_irrefl (a : Key × α) : ¬ KeyLt a a := bitLt_irrefl a.1

theorem keyLt_trans {a b c : Key × α} (hab : KeyLt a b) (hbc : KeyLt b c) :
    KeyLt a c := bitLt_trans hab hbc

theorem keyLt_congr {a a' b b' : Key × α}
    (left : EqKeyValue a a') (right : EqKeyValue b b') : KeyLt a b ↔ KeyLt a' b' := by
  unfold KeyLt
  rw [left.1, right.1]

theorem forall₂_eqKeyValue_iff_eq (xs ys : List (Key × α)) :
    List.Forall₂ EqKeyValue xs ys ↔ xs = ys := by
  rw [eqKeyValue_eq, forall₂_eq_iff]

theorem relatedMem_map_fst_key (query : Key) (xs : List (Key × α)) :
    RelatedMem KeyEq query (xs.map Prod.fst) ↔
      ∃ value, RelatedMem EqKeyValue (query, value) xs := by
  rw [eqKeyValue_eq]
  exact relatedMem_map_fst query xs

theorem isChain_keyLt_iff (xs : List (Key × α)) :
    xs.IsChain KeyLt ↔ (xs.map Prod.fst).IsChain BitLt :=
  isChain_map_fst BitLt xs

theorem forall₂_eqKeyValue_of_sorted {xs ys : List (Key × α)}
    (sortedXs : xs.IsChain KeyLt) (sortedYs : ys.IsChain KeyLt)
    (sameMembers : SameRelatedMembers EqKeyValue xs ys) : List.Forall₂ EqKeyValue xs ys :=
  forall₂_of_isChain_of_sameRelatedMembers (S := KeyLt)
    eqKeyValue_equivalence keyLt_irrefl keyLt_trans
    keyLt_congr sortedXs sortedYs sameMembers

theorem source_erase_test (query erased : Key) :
    (if query = erased then false else true) = decide (query ≠ erased) := by
  by_cases same : query = erased <;> simp [same]

end Relations

namespace KeySet

theorem not_mem_nil (key : PosNum) : mem key .nil ≠ true := by
  rw [mem_nil]
  decide

theorem elements_isChain (tree : KeySet) : (elements tree).IsChain BitLt :=
  (elements_pairwise tree).isChain

theorem relatedMem_elements (key : PosNum) (tree : KeySet) :
    RelatedMem Relations.KeyEq key (elements tree) ↔ mem key tree = true := by
  rw [relatedMem_eq, mem_elements]

theorem elements_erase_source (key : PosNum) (tree : KeySet) :
    elements (erase key tree) =
      (elements tree).filter (fun query => if query = key then false else true) := by
  simpa only [Relations.source_erase_test] using elements_erase key tree

theorem elements_erase_source_of_mem (key : PosNum) (tree : KeySet)
    (_present : mem key tree = true) :
    elements (erase key tree) =
      (elements tree).filter (fun query => if query = key then false else true) :=
  elements_erase_source key tree

end KeySet

namespace SparseMap

variable {α : Type u} {β : Type v}

theorem elements_isChain (tree : SparseMap α) : (elements tree).IsChain Relations.KeyLt :=
  (elements_pairwise tree).isChain

theorem relatedMem_elements (key : PosNum) (value : α) (tree : SparseMap α) :
    RelatedMem Relations.EqKeyValue (key, value) (elements tree) ↔ find key tree = some value := by
  rw [Relations.eqKeyValue_eq, relatedMem_eq, mem_elements]

/-- The used map-facts law retains the actual preimage witness for a noninjective map. -/
theorem find_map_eq_some_iff (f : α → β) (key : PosNum) (tree : SparseMap α) (value : β) :
    find key (map f tree) = some value ↔
      ∃ original, find key tree = some original ∧ f original = value := by
  rw [find_map, Option.map_eq_some_iff]

theorem elements_erase_forall₂ (key : PosNum) (tree : SparseMap α) :
    List.Forall₂ Relations.EqKeyValue (elements (erase key tree))
      ((elements tree).filter (fun entry => if entry.1 = key then false else true)) := by
  apply (Relations.forall₂_eqKeyValue_iff_eq _ _).mpr
  simpa only [Relations.source_erase_test] using elements_erase key tree

theorem elements_erase_forall₂_of_mem (key : PosNum) (tree : SparseMap α)
    (_present : key ∈ keys tree) :
    List.Forall₂ Relations.EqKeyValue (elements (erase key tree))
      ((elements tree).filter (fun entry => if entry.1 = key then false else true)) :=
  elements_erase_forall₂ key tree

end SparseMap

end Search.PositiveTrie
