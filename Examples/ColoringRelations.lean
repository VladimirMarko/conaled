import Applications.Search.PositiveTrie.Relations
import Examples.PositiveFiniteTries

/-!
# Related-list cases for the Color preliminaries

Modulo-ten membership forgets repetitions. The compatible strict-order theorem
recovers pointwise relation on sorted lists. Counterexamples retain the exact
boundaries of strictness, congruence and adjacent sortedness.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ColoringRelations

open Sequences.RelatedMembership
open Search.PositiveTrie Numerals.PositivePaths

universe u

def SameModTen (a b : Nat) : Prop := a % 10 = b % 10

theorem related_twenty_seven : RelatedMem SameModTen 27 [3, 17, 2] := by
  exact ⟨17, by decide, rfl⟩

theorem same_mod_members : SameRelatedMembers SameModTen [3, 17] [7, 3, 27] := by
  intro query
  simp only [relatedMem_cons, relatedMem_nil, or_false, SameModTen]
  omega

theorem same_mod_members_different_lengths :
    ([3, 17] : List Nat).length ≠ [7, 3, 27].length := by decide

theorem same_mod_members_not_forall₂ : ¬ List.Forall₂ SameModTen [3, 17] [7, 3, 27] := by
  intro related
  exact same_mod_members_different_lengths related.length_eq

theorem same_mod_members_not_perm : ¬ ([3, 17] : List Nat).Perm [7, 3, 27] := by
  intro permuted
  exact same_mod_members_different_lengths permuted.length_eq

theorem sameModTen_equivalence : Equivalence SameModTen :=
  ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

def ResidueLt (a b : Nat) : Prop := a % 10 < b % 10

theorem sorted_mod_classes : List.Forall₂ SameModTen [3, 17] [13, 7] := by
  apply forall₂_of_isChain_of_sameRelatedMembers (S := ResidueLt) sameModTen_equivalence
  · exact fun a => Nat.lt_irrefl (a % 10)
  · exact fun hab hbc => Nat.lt_trans hab hbc
  · intro a a' b b' haa' hbb'
    unfold ResidueLt
    rw [haa', hbb']
  · unfold ResidueLt
    decide
  · unfold ResidueLt
    decide
  · intro query
    simp [SameModTen]

theorem sorted_mod_classes_not_literal_equal :
    ([3, 17] : List Nat) ≠ [13, 7] := by decide

theorem modulo_filter_member :
    RelatedMem SameModTen 27 ([3, 17, 2].filter (fun n => decide (n % 10 = 7))) := by
  apply (relatedMem_filter _ (fun {a b} (same : SameModTen a b) => ?_)
    27 [3, 17, 2]).mpr
  · exact ⟨related_twenty_seven, by decide⟩
  · rw [same]

theorem modulo_filter_entries :
    ([3, 17, 2] : List Nat).filter (fun n => decide (n % 10 = 7)) = [17] := by decide

/-- A nonstrict order leaves multiplicity unconstrained. -/
theorem nonstrict_multiplicity_counterexample :
    SameRelatedMembers Eq ([1] : List Nat) [1, 1] ∧
      ([1] : List Nat).IsChain (· ≤ ·) ∧
      ([1, 1] : List Nat).IsChain (· ≤ ·) ∧
      ¬ List.Forall₂ Eq ([1] : List Nat) [1, 1] := by
  refine ⟨?_, by decide, by decide, ?_⟩
  · rw [sameRelatedMembers_eq]
    intro query
    simp
  · intro related
    have impossible := related.length_eq
    simp at impossible

/-- The filter accepts a related witness while rejecting the query. -/
theorem filter_congruence_counterexample :
    RelatedMem (fun _ _ : Bool => True) false ([true].filter id) ∧ id false ≠ true := by
  exact ⟨⟨true, by decide, True.intro⟩, by decide⟩

/-- Strict natural order does not respect the universal equivalence. -/
theorem order_compatibility_counterexample :
    Equivalence (fun _ _ : Nat => True) ∧
      ([0, 1] : List Nat).IsChain (· < ·) ∧
      ([0] : List Nat).IsChain (· < ·) ∧
      SameRelatedMembers (fun _ _ : Nat => True) [0, 1] [0] ∧
      ¬ List.Forall₂ (fun _ _ : Nat => True) [0, 1] [0] := by
  refine ⟨⟨fun _ => True.intro, fun _ => True.intro, fun _ _ => True.intro⟩,
    by decide, by decide, ?_, ?_⟩
  · intro query
    constructor <;> intro _
    · exact ⟨0, by decide, True.intro⟩
    · exact ⟨0, by decide, True.intro⟩
  · intro related
    have impossible := related.length_eq
    simp at impossible

def SuccessorStep (a b : Nat) : Prop := b = a + 1

theorem adjacent_filter_counterexample :
    ([0, 1, 2] : List Nat).IsChain SuccessorStep ∧
      ¬ ([0, 1, 2] : List Nat).Pairwise SuccessorStep ∧
      ¬ (([0, 1, 2] : List Nat).filter (fun n => decide (n ≠ 1))).IsChain SuccessorStep := by
  unfold SuccessorStep
  decide

theorem repeated_key_payload_witness {α : Type u} (a b : α) :
    ∃ value, RelatedMem Relations.EqKeyValue (1, value) [(1, a), (1, b)] := by
  apply (Relations.relatedMem_map_fst_key 1 [(1, a), (1, b)]).mp
  exact (relatedMem_eq _ _).mpr (by simp)

theorem same_key_not_pair_related :
    ¬ Relations.EqKeyValue ((1 : PosNum), false) (1, true) := by
  simp [Relations.EqKeyValue]

theorem function_payloads_sorted (f g : Nat → Nat) :
    ([(2, f), (1, g)] : List (PosNum × (Nat → Nat))).IsChain Relations.KeyLt := by
  simpa [List.isChain_cons_cons, Relations.KeyLt] using
    PositiveFiniteTries.bit_order_opposes_numeric.1

theorem function_payload_canonical (f g : Nat → Nat) {ys : List (PosNum × (Nat → Nat))}
    (sorted : ys.IsChain Relations.KeyLt)
    (sameMembers : SameRelatedMembers Relations.EqKeyValue [(2, f), (1, g)] ys) :
    List.Forall₂ Relations.EqKeyValue [(2, f), (1, g)] ys :=
  Relations.forall₂_eqKeyValue_of_sorted (function_payloads_sorted f g) sorted sameMembers

/-- Distinct same-key function pairs show why no trichotomy assumption belongs in the API. -/
theorem function_pairs_incomparable :
    ((1 : PosNum), fun _ : Nat => 0) ≠ (1, fun _ : Nat => 1) ∧
      ¬ Relations.KeyLt ((1 : PosNum), fun _ : Nat => 0) (1, fun _ : Nat => 1) ∧
      ¬ Relations.KeyLt ((1 : PosNum), fun _ : Nat => 1) (1, fun _ : Nat => 0) := by
  refine ⟨?_, bitLt_irrefl 1, bitLt_irrefl 1⟩
  intro same
  have impossible := congrArg (fun p : PosNum × (Nat → Nat) => p.2 0) same
  exact Nat.zero_ne_one impossible

theorem sourceMap_erase_related :
    List.Forall₂ Relations.EqKeyValue
      (SparseMap.elements (SparseMap.erase 9 PositiveFiniteTries.sourceMap))
      [(2, .nil), (3, .nil)] := by
  have related := SparseMap.elements_erase_forall₂ 9 PositiveFiniteTries.sourceMap
  have expected : (SparseMap.elements PositiveFiniteTries.sourceMap).filter
      (fun entry => if entry.1 = 9 then false else true) = [(2, .nil), (3, .nil)] := by
    rw [PositiveFiniteTries.sourceMap_elements]
    decide
  rw [expected] at related
  exact related

theorem oneTwo_erase_source :
    KeySet.elements (KeySet.erase 1 PositiveFiniteTries.oneTwo) = [2] := by
  calc
    _ = (KeySet.elements PositiveFiniteTries.oneTwo).filter
        (fun query => if query = 1 then false else true) :=
      KeySet.elements_erase_source_of_mem 1 PositiveFiniteTries.oneTwo (by rfl)
    _ = [2] := by rw [PositiveFiniteTries.oneTwo_elements]; decide

theorem sourceMap_colliding_value_witness :
    ∃ original, SparseMap.find 9 PositiveFiniteTries.sourceMap = some original ∧
      (fun _ : KeySet => false) original = false := by
  apply (SparseMap.find_map_eq_some_iff (fun _ : KeySet => false) 9
    PositiveFiniteTries.sourceMap false).mp
  rw [SparseMap.find_map]
  rfl

def appendDigit (acc digit : Nat) : Nat := 10 * acc + digit

theorem decimal_foldl : [1, 2, 3].foldl appendDigit 0 = 123 := rfl

theorem decimal_reverse_foldr :
    [1, 2, 3].reverse.foldr (fun digit acc => appendDigit acc digit) 0 = 123 := by
  calc
    _ = [1, 2, 3].foldl appendDigit 0 := List.foldl_eq_foldr_reverse.symm
    _ = 123 := decimal_foldl

theorem decimal_unreversed_foldr :
    [1, 2, 3].foldr (fun digit acc => appendDigit acc digit) 0 = 321 := rfl

theorem decimal_requires_reverse :
    [1, 2, 3].foldl appendDigit 0 ≠
      [1, 2, 3].foldr (fun digit acc => appendDigit acc digit) 0 := by
  rw [decimal_foldl, decimal_unreversed_foldr]
  decide

end Examples.ColoringRelations
