import Applications.Search.OrderedMap.DecodedKeysModels
import Applications.Search.OrderedMap.Workload
import Examples.ExtractedPrograms

/-!
# Source search trees through proved signed comparisons

The source constructor order and caller-supplied defaults are adapters around
the existing binary tree and Boolean-only map programs. Raw lookup/update laws,
invariant-guarded enumeration, independent partial models and finite workload
observations have distinct premises. Payloads retain their own universe.

These are mathematical clients. Resource refinements and actual standalone
execution remain separate Extract obligations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ExtractedTrees

universe u v
variable {W : Type u} {V : Type v}
open Representations.SignedComparison
open Search.OrderedTree (entries)
open Search.OrderedMap

/-- The source key is the supplied word carrier, without added arithmetic. -/
abbrev key (W : Type u) := W

abbrev tree (W : Type u) (V : Type v) := BinaryTree (W × V)

abbrev E : tree W V := .nil

/-- Preserve the source's left/key/value/right constructor argument order. -/
abbrev T (left : tree W V) (k : W) (value : V) (right : tree W V) : tree W V :=
  .node (k, value) left right

abbrev empty_tree : tree W V := E

abbrev lookup (ltb : W → W → Bool) : V → W → tree W V → V := DecodedKeys.lookup ltb
abbrev insert (ltb : W → W → Bool) : W → V → tree W V → tree W V := DecodedKeys.insert ltb
abbrev elements_aux : tree W V → List (W × V) → List (W × V) := DecodedKeys.elementsAux
abbrev elements : tree W V → List (W × V) := DecodedKeys.elements

theorem lookup_E (ltb : W → W → Bool) (default : V) (k : W) :
    lookup ltb default k E = default := DecodedKeys.lookup_empty ltb default k

theorem lookup_T (ltb : W → W → Bool) (default : V) (query k : W) (value : V)
    (left right : tree W V) :
    lookup ltb default query (T left k value right) =
      if ltb query k then lookup ltb default query left
      else if ltb k query then lookup ltb default query right else value :=
  DecodedKeys.lookup_node ltb default query (k, value) left right

theorem insert_E (ltb : W → W → Bool) (k : W) (value : V) :
    insert ltb k value E = T E k value E := DecodedKeys.insert_empty ltb k value

theorem insert_T (ltb : W → W → Bool) (k old : W) (value previous : V)
    (left right : tree W V) :
    insert ltb k value (T left old previous right) =
      if ltb k old then T (insert ltb k value left) old previous right
      else if ltb old k then T left old previous (insert ltb k value right)
      else T left k value right := DecodedKeys.insert_node ltb k value (old, previous) left right

theorem elements_aux_E (suffix : List (W × V)) : elements_aux E suffix = suffix :=
  DecodedKeys.elementsAux_empty suffix

theorem elements_aux_T (left right : tree W V) (k : W) (value : V)
    (suffix : List (W × V)) :
    elements_aux (T left k value right) suffix =
      elements_aux left ((k, value) :: elements_aux right suffix) :=
  DecodedKeys.elementsAux_node (k, value) left right suffix

theorem elements_aux_eq (t : tree W V) (suffix : List (W × V)) :
    elements_aux t suffix = entries t ++ suffix := DecodedKeys.elementsAux_eq t suffix

theorem elements_eq (t : tree W V) : elements t = elements_aux t [] := rfl

theorem lookup_empty (ltb : W → W → Bool) (default : V) (k : W) :
    lookup ltb default k empty_tree = default := lookup_E ltb default k

/-- The first source tree exercise holds on all raw trees under weak reflection. -/
theorem lookup_insert_eq (decode : W → Int) (ltb : W → W → Bool)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (default : V) (t : tree W V) (k : W) (value : V) :
    lookup ltb default k (insert ltb k value t) = value :=
  DecodedKeys.lookup_insert_eq decode ltb hlt default k value t

/-- Distinctness is of original keys; no search-tree invariant is added. -/
theorem lookup_insert_neq (decode : W → Int) (ltb : W → W → Bool)
    (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (default : V) (t : tree W V) (k query : W) (value : V) (different : k ≠ query) :
    lookup ltb default query (insert ltb k value t) = lookup ltb default query t :=
  DecodedKeys.lookup_insert_neq decode ltb hinj hlt default k query value t different

theorem word_lookup_insert_eq {w : Nat} (default : V) (t : tree (BitVec w) V)
    (k : BitVec w) (value : V) : lookup wordLtb default k (insert wordLtb k value t) = value :=
  lookup_insert_eq BitVec.toInt wordLtb wordLtb_true_iff default t k value

theorem word_lookup_insert_neq {w : Nat} (default : V) (t : tree (BitVec w) V)
    (k query : BitVec w) (value : V) (different : k ≠ query) :
    lookup wordLtb default query (insert wordLtb k value t) = lookup wordLtb default query t :=
  lookup_insert_neq BitVec.toInt wordLtb (word_decode_injective w) wordLtb_true_iff
    default t k query value different

theorem int64_lookup_insert_eq (default : V) (t : tree Int64 V) (k : Int64) (value : V) :
    lookup int64Ltb default k (insert int64Ltb k value t) = value :=
  lookup_insert_eq Int64.toInt int64Ltb int64Ltb_true_iff default t k value

theorem int64_lookup_insert_neq (default : V) (t : tree Int64 V)
    (k query : Int64) (value : V) (different : k ≠ query) :
    lookup int64Ltb default query (insert int64Ltb k value t) =
      lookup int64Ltb default query t :=
  lookup_insert_neq Int64.toInt int64Ltb int64_decode_injective int64Ltb_true_iff
    default t k query value different

theorem zero_width_replacement (default : V) (t : tree (BitVec 0) V)
    (k query : BitVec 0) (value : V) :
    lookup wordLtb default query (insert wordLtb k value t) = value := by
  have same : k = query := word_decode_injective 0 (by simp only [BitVec.toInt_zero_length])
  subst query
  exact word_lookup_insert_eq default t k value

/-- Weak decoder transport applies to the actual returned tree and supplied suffix. -/
theorem decoded_history_step (decode : W → Int) (ltb : W → W → Bool)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (k : W) (value : V) (t : tree W V) (suffix : List (W × V)) :
    (elements_aux (insert ltb k value t) suffix).map
        (fun binding => (decode binding.1, binding.2)) =
      DecodedKeys.elementsAux
        (Search.OrderedMap.bind (decode k) value (DecodedKeys.mapKeys decode t))
        (suffix.map (fun binding => (decode binding.1, binding.2))) := by
  rw [DecodedKeys.map_elementsAux, DecodedKeys.mapKeys_insert decode ltb hlt]

/-- A type-valued payload remains ordinary data in its independent universe. -/
theorem type_payload_update (default value : Type v) (k : Int)
    (t : tree Int (Type v)) : lookup intLtb default k (insert intLtb k value t) = value :=
  lookup_insert_eq id intLtb intLtb_true_iff default t k value

/-- Repeated signed writes replace the payload while retaining the other key. -/
def signedHistory : tree Int Nat :=
  insert intLtb (-3) 9 (insert intLtb 4 8 (insert intLtb (-3) 7 E))

theorem signed_history_last_write (default : Nat) :
    lookup intLtb default (-3) signedHistory = 9 :=
  lookup_insert_eq id intLtb intLtb_true_iff default _ (-3) 9

theorem signed_history_lookup :
    lookup intLtb 99 (-3) signedHistory = 9 ∧
      lookup intLtb 99 4 signedHistory = 8 ∧ lookup intLtb 99 (-1) signedHistory = 99 := by
  decide

theorem signed_history_elements : elements signedHistory = [(-3, 9), (4, 8)] := rfl

theorem signed_history_valid : DecodedKeys.BST id signedHistory := by
  apply DecodedKeys.bst_insert id intLtb intLtb_true_iff
  apply DecodedKeys.bst_insert id intLtb intLtb_true_iff
  apply DecodedKeys.bst_insert id intLtb intLtb_true_iff
  exact DecodedKeys.bst_empty id

theorem signed_history_keys_unique : (elements signedHistory |>.map Prod.fst).Nodup :=
  DecodedKeys.keys_nodup id signed_history_valid

theorem signed_history_sound :
    DecodedKeys.bound intLtb (-3) signedHistory = true ∧
      ∀ default : Nat, lookup intLtb default (-3) signedHistory = 9 := by
  apply DecodedKeys.elements_sound id intLtb intLtb_true_iff signed_history_valid
  change (-3, 9) ∈ elements signedHistory
  rw [signed_history_elements]
  simp

theorem signed_history_models :
    DecodedKeys.enumAbs id intLtb int_decode_injective intLtb_true_iff signedHistory (-3) =
        some 9 ∧
      DecodedKeys.mapOfTree id intLtb int_decode_injective intLtb_true_iff
        signedHistory (-3) = some 9 := by
  constructor
  · rw [DecodedKeys.enumAbs_lookup id intLtb int_decode_injective intLtb_true_iff
      signed_history_valid]
    rfl
  · rw [DecodedKeys.mapOfTree_lookup id intLtb int_decode_injective intLtb_true_iff
      signed_history_valid]
    rfl

/-- The complete history theorem is consumed through each independent model. -/
theorem history_models (decode : W → Int) (ltb : W → W → Bool)
    (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (default : V) (writes : List (W × V)) {t : tree W V} (valid : DecodedKeys.BST decode t) :
    letI := linearOrderOfStrict decode ltb hinj hlt
    DecodedKeys.enumAbs decode ltb hinj hlt
          (Search.TotalTable.setAll (DecodedKeys.table ltb default) writes t) =
        writeAll writes (DecodedKeys.enumAbs decode ltb hinj hlt t) ∧
      DecodedKeys.mapOfTree decode ltb hinj hlt
          (Search.TotalTable.setAll (DecodedKeys.table ltb default) writes t) =
        writeAll writes (DecodedKeys.mapOfTree decode ltb hinj hlt t) := by
  let _ := linearOrderOfStrict decode ltb hinj hlt
  exact ⟨DecodedKeys.enumAbs_setAll decode ltb hinj hlt default writes valid,
    DecodedKeys.mapOfTree_setAll decode ltb hinj hlt default writes valid⟩

theorem colliding_original_keys :
    ¬ Function.Injective (fun _ : Bool => (0 : Int)) ∧
      lookup (fun _ _ : Bool => false) 0 false
          (insert (fun _ _ : Bool => false) true 2
            (insert (fun _ _ : Bool => false) false 1 E)) = 2 ∧
      lookup (fun _ _ : Bool => false) 0 false
          (insert (fun _ _ : Bool => false) false 1 E) = 1 :=
  ⟨ExtractedPrograms.constant_decoder_not_injective, DecodedKeys.colliding_keys_counterexample⟩

theorem stored_default_not_canonical :
    (∀ query : Int,
      lookup intLtb 0 query (E : tree Int Nat) =
        lookup intLtb 0 query (insert intLtb 0 0 E)) ∧
      elements (E : tree Int Nat) ≠ elements (insert intLtb 0 0 E) :=
  DecodedKeys.default_observation_not_canonical

theorem malformed_membership :
    let t : tree Int Nat := T (T E 1 7 E) 0 0 E
    (1, 7) ∈ elements t ∧ lookup intLtb 99 1 t = 99 ∧
      DecodedKeys.bound intLtb 1 t = false :=
  DecodedKeys.malformed_membership_boundary

theorem malformed_not_valid :
    ¬ DecodedKeys.BST id (T (T E (1 : Int) (7 : Nat) E) 0 0 E) := by
  simp [DecodedKeys.BST, Search.OrderedTree.OrderedBy, Search.OrderedTree.All]

/-- Signed endpoint keys pass through the supplied primitive, preserving payloads. -/
theorem four_bit_endpoints :
    (elements (insert wordLtb (BitVec.ofInt 4 7) 2
      (insert wordLtb (BitVec.ofInt 4 (-8)) 1 E))).map
        (fun binding => (binding.1.toInt, binding.2)) = [(-8, 1), (7, 2)] := by
  rw [DecodedKeys.map_elements,
    DecodedKeys.mapKeys_insert BitVec.toInt wordLtb wordLtb_true_iff,
    DecodedKeys.mapKeys_insert BitVec.toInt wordLtb wordLtb_true_iff,
    DecodedKeys.mapKeys_empty]
  decide

theorem int64_endpoints :
    (elements (insert int64Ltb (Int64.ofInt ((2 : Int) ^ 63 - 1)) 2
      (insert int64Ltb (Int64.ofInt (-(2 : Int) ^ 63)) 1 E))).map
        (fun binding => (binding.1.toInt, binding.2)) =
      [(-(2 : Int) ^ 63, 1), ((2 : Int) ^ 63 - 1, 2)] := by
  rw [DecodedKeys.map_elements,
    DecodedKeys.mapKeys_insert Int64.toInt int64Ltb int64Ltb_true_iff,
    DecodedKeys.mapKeys_insert Int64.toInt int64Ltb int64Ltb_true_iff,
    DecodedKeys.mapKeys_empty]
  decide

/-- Source Boolean search is connected to the independent reversed-write model. -/
theorem source_workload_lookup (writes : List (Int × V)) (query : Int) :
    DecodedKeys.lookup? intLtb query (Workload.build writes) = Workload.model writes query :=
  (DecodedKeys.lookup?_eq_lookup intLtb intLtb_true_iff query _).trans
    (Workload.build_lookup writes query)

theorem source_workload_default (writes : List (Int × V)) (default : V) (query : Int) :
    lookup intLtb default query (Workload.build writes) =
      (Workload.model writes query).getD default :=
  congrArg (fun result => result.getD default) (source_workload_lookup writes query)

theorem source_workload_history (writes : List (Int × V)) (default : V) :
    Search.TotalTable.setAll (DecodedKeys.table intLtb default) writes E = Workload.build writes := by
  rw [DecodedKeys.table_eq_rawTreeTable intLtb intLtb_true_iff default]
  exact (Workload.buildFrom_eq_setAll default writes E).symm

/-- Complete partial meaning, rather than one default view, fixes canonical entries. -/
theorem canonical_workload_histories (first second : List (Int × V))
    (same : Workload.model first = Workload.model second) :
    elements (Workload.build first) = elements (Workload.build second) := by
  apply DecodedKeys.elements_eq_of_lookup?_eq id intLtb int_decode_injective intLtb_true_iff
    (Workload.build_ordered first) (Workload.build_ordered second)
  intro query
  rw [source_workload_lookup, source_workload_lookup, same]

theorem reordered_distinct_histories :
    elements (Workload.build ([(2, 20), (1, 10), (3, 30)] : List (Int × Nat))) =
      elements (Workload.build ([(1, 10), (3, 30), (2, 20)] : List (Int × Nat))) := by
  apply canonical_workload_histories
  funext query
  by_cases h1 : query = 1 <;> by_cases h2 : query = 2 <;> by_cases h3 : query = 3 <;>
    simp_all [Workload.model, listLookup]

theorem workload_empty : Workload.hits ([] : List Nat) [] = 0 := by
  rw [Workload.hits_eq_expected]
  rfl

theorem workload_empty_with_queries : Workload.hits ([] : List Nat) [0, 0, 7] = 0 := by
  rw [Workload.hits_eq_expected]
  decide

theorem workload_repeated_queries : Workload.hits ([3, 1, 3] : List Nat) [3, 2, 1, 3, 7] = 3 := by
  rw [Workload.hits_eq_expected]
  decide

theorem workload_signed_queries :
    Workload.hits ([-3, 0, 4, -3] : List Int) [-3, -1, 4, 0, 4] = 4 := by
  rw [Workload.hits_eq_expected]
  decide

theorem workload_presence_and_default :
    Workload.queryResults [2, 4] (Workload.build ([(2, 5), (2, 0)] : List (Int × Nat))) =
        [some 0, none] ∧
      Workload.queryValues 0 [2, 4] (Workload.build ([(2, 5), (2, 0)] : List (Int × Nat))) =
        [0, 0] := by
  rw [Workload.queryResults_model, Workload.queryValues_model]
  decide

theorem workload_type_payload (first last : Type v) :
    Search.OrderedMap.lookup (2 : Int) (Workload.build [(2, first), (2, last)]) = some last := by
  rw [Workload.build_lookup]
  rfl

theorem source_consecutive_schedule (n : Nat) :
    (Workload.sourceIndices n).map (fun j => n - j) = List.range n ∧
      Workload.hits ((Workload.sourceIndices n).map (fun j => n - j))
        ((Workload.sourceIndices n).map (fun j => n - j)) = n :=
  ⟨Workload.sourceIndices_consecutive n, Workload.source_schedule_hits n⟩

end Examples.ExtractedTrees
