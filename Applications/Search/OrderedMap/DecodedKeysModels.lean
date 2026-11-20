import Applications.Search.OrderedMap.DecodedKeys
import Applications.Search.OrderedMap.EnumeratedTable
import Applications.Representations.SignedComparison

/-!
# Decoded-key table and model contracts

The first soundness bridge retains weak reflection alone. Raw completeness and
distinct-original-key observations additionally require injective decoding.
The full model contracts then reuse the two independent existing abstractions
and the seven-field ADT interfaces through exact operation/invariant bridges.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap.DecodedKeys

universe u v
variable {κ : Type u} {ν : Type v}
open Search.OrderedTree (All OrderedBy entries)

section StrictReflection
variable (decode : κ → Int) (ltb : κ → κ → Bool)
variable (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
include hlt

/-- Invariant-guarded membership soundness does not require decoder injection. -/
theorem lookup?_eq_some_of_mem {t : BinaryTree (κ × ν)} (valid : BST decode t)
    {key : κ} {value : ν} (member : (key, value) ∈ elements t) :
    lookup? ltb key t = some value := by
  have decodedMember : (decode key, value) ∈ entries (mapKeys decode t) := by
    rw [entries_mapKeys]
    exact List.mem_map.mpr ⟨(key, value), by simpa only [elements_eq] using member, rfl⟩
  have found := (Search.OrderedMap.lookup_eq_some_iff_mem_entries
    ((bst_iff_mapKeys decode t).mp valid) (decode key) value).mpr decodedMember
  rw [lookup?_decode decode ltb hlt] at found
  exact found

/-- Pair membership determines presence and the value for every caller default. -/
theorem elements_sound {t : BinaryTree (κ × ν)} (valid : BST decode t)
    {key : κ} {value : ν} (member : (key, value) ∈ elements t) :
    bound ltb key t = true ∧ ∀ default : ν, lookup ltb default key t = value := by
  have found := lookup?_eq_some_of_mem decode ltb hlt valid member
  constructor
  · simp only [bound, found, Option.isSome_some]
  · intro default
    simp only [lookup, found, Option.getD_some]

theorem absent_no_entry {t : BinaryTree (κ × ν)} (valid : BST decode t)
    (key : κ) (absent : bound ltb key t = false) (value : ν) :
    (key, value) ∉ elements t := by
  intro member
  have present := (elements_sound decode ltb hlt valid member).1
  rw [absent] at present
  cases present

end StrictReflection

section InjectiveReflection
variable (decode : κ → Int) (ltb : κ → κ → Bool)
variable (hinj : Function.Injective decode)
variable (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
include hinj hlt

/-- Distinctness concerns original keys; the tree is arbitrary and may be malformed. -/
theorem lookup?_insert_neq (key query : κ) (value : ν) (t : BinaryTree (κ × ν))
    (different : key ≠ query) :
    lookup? ltb query (insert ltb key value t) = lookup? ltb query t := by
  have decodedNe : decode query ≠ decode key := fun same => different (hinj same).symm
  calc
    lookup? ltb query (insert ltb key value t) =
        Search.OrderedMap.lookup (decode query)
          (mapKeys decode (insert ltb key value t)) :=
      (lookup?_decode decode ltb hlt query _).symm
    _ = Search.OrderedMap.lookup (decode query)
        (Search.OrderedMap.bind (decode key) value (mapKeys decode t)) := by
      rw [mapKeys_insert decode ltb hlt]
    _ = Search.OrderedMap.lookup (decode query) (mapKeys decode t) := by
      rw [Search.OrderedMap.lookup_bind, ite_eq_right decodedNe]
    _ = lookup? ltb query t := lookup?_decode decode ltb hlt query t

theorem lookup_insert_neq (default : ν) (key query : κ) (value : ν)
    (t : BinaryTree (κ × ν)) (different : key ≠ query) :
    lookup ltb default query (insert ltb key value t) = lookup ltb default query t :=
  congrArg (fun result => result.getD default)
    (lookup?_insert_neq decode ltb hinj hlt key query value t different)

theorem bound_insert_neq (key query : κ) (value : ν) (t : BinaryTree (κ × ν))
    (different : key ≠ query) :
    bound ltb query (insert ltb key value t) = bound ltb query t :=
  congrArg Option.isSome (lookup?_insert_neq decode ltb hinj hlt key query value t different)

/-- Successful search identifies an original stored pair without assuming BST. -/
theorem mem_elements_of_lookup? {t : BinaryTree (κ × ν)} {key : κ} {value : ν}
    (found : lookup? ltb key t = some value) : (key, value) ∈ elements t := by
  have decodedFound : Search.OrderedMap.lookup (decode key) (mapKeys decode t) =
      some value := (lookup?_decode decode ltb hlt key t).trans found
  have decodedMember := Search.OrderedMap.mem_entries_of_lookup decodedFound
  rw [entries_mapKeys] at decodedMember
  rcases List.mem_map.mp decodedMember with ⟨binding, member, same⟩
  have sameKey : binding.1 = key := hinj (congrArg Prod.fst same)
  have sameValue : binding.2 = value := congrArg Prod.snd same
  have sameBinding : binding = (key, value) := Prod.ext sameKey sameValue
  rw [elements_eq]
  exact sameBinding ▸ member

theorem elements_complete (default : ν) (key : κ) (value : ν)
    (t : BinaryTree (κ × ν)) (present : bound ltb key t = true)
    (found : lookup ltb default key t = value) : (key, value) ∈ elements t :=
  mem_elements_of_lookup? decode ltb hinj hlt
    ((binding_iff default (fun query => lookup? ltb query t) key value).mpr ⟨present, found⟩)

/-- Each raw represented tree has finite observed key support. The ambient
partial-meaning type still permits functions with infinite support. -/
theorem lookup?_finite_support (t : BinaryTree (κ × ν)) :
    ∃ keys : List κ, ∀ key value, lookup? ltb key t = some value → key ∈ keys := by
  refine ⟨(elements t).map Prod.fst, ?_⟩
  intro key value found
  exact SourceModel.in_keys_of_mem (mem_elements_of_lookup? decode ltb hinj hlt found)

/-- This absence converse is valid on raw trees, unlike its converse above. -/
theorem no_entry_absent (key : κ) (t : BinaryTree (κ × ν))
    (absent : ∀ value, (key, value) ∉ elements t) : bound ltb key t = false := by
  change (lookup? ltb key t).isSome = false
  cases found : lookup? ltb key t with
  | none => rfl
  | some value =>
      exact False.elim (absent value (mem_elements_of_lookup? decode ltb hinj hlt found))

end InjectiveReflection

/-- Relate the invariant to an existing original-key order without copying it. -/
theorem bst_iff_ordered [LT κ] (decode : κ → Int)
    (compatible : ∀ a b : κ, a < b ↔ decode a < decode b)
    (t : BinaryTree (κ × ν)) :
    BST decode t ↔ OrderedBy Prod.fst t := by
  induction t with
  | nil => rfl
  | node binding left right ihl ihr =>
      change
        (BST decode left ∧ BST decode right ∧
          All (fun other => decode other.1 < decode binding.1) left ∧
          All (fun other => decode binding.1 < decode other.1) right) ↔
        (OrderedBy Prod.fst left ∧ OrderedBy Prod.fst right ∧
          All (fun other => other.1 < binding.1) left ∧
          All (fun other => binding.1 < other.1) right)
      simp only [ihl, ihr, Search.OrderedTree.all_iff, compatible]

/-- Existing operation records package the actual Boolean wrappers. -/
def ops (ltb : κ → κ → Bool) : Search.OrderedMap.Ops κ ν (BinaryTree (κ × ν)) where
  empty := .nil
  bind := insert ltb
  lookup := lookup? ltb

def table (ltb : κ → κ → Bool) (default : ν) :
    TotalTable.Ops κ ν (BinaryTree (κ × ν)) :=
  TotalTable.ofPartial (ops ltb) default

def observations (ltb : κ → κ → Bool) :
    EnumeratedTable.Observations κ ν (BinaryTree (κ × ν)) :=
  EnumeratedTable.observationsOfPartial (ops ltb) elements

section LawfulOperationCongruence
variable [LinearOrder κ]

theorem ops_eq_rawTrees (ltb : κ → κ → Bool)
    (compatible : ∀ a b, ltb a b = true ↔ a < b) :
    ops (ν := ν) ltb = Search.OrderedMap.rawTrees κ ν := by
  have writes : insert (ν := ν) ltb = Search.OrderedMap.bind := by
    funext key value t
    exact insert_eq_bind ltb compatible key value t
  have searches : lookup? (ν := ν) ltb = Search.OrderedMap.lookup := by
    funext query t
    exact lookup?_eq_lookup ltb compatible query t
  simp only [ops, Search.OrderedMap.rawTrees, writes, searches]

theorem table_eq_rawTreeTable (ltb : κ → κ → Bool)
    (compatible : ∀ a b, ltb a b = true ↔ a < b) (default : ν) :
    table ltb default = EnumeratedTable.rawTreeTable default := by
  simp only [table, EnumeratedTable.rawTreeTable, ops_eq_rawTrees ltb compatible]

theorem observations_eq_rawTreeObservations (ltb : κ → κ → Bool)
    (compatible : ∀ a b, ltb a b = true ↔ a < b) :
    observations (ν := ν) ltb = EnumeratedTable.rawTreeObservations := by
  have enumeration : elements (κ := κ) (ν := ν) = entries := funext elements_eq
  simp only [observations, EnumeratedTable.rawTreeObservations,
    ops_eq_rawTrees ltb compatible, enumeration]

end LawfulOperationCongruence

section CompleteContracts
variable (decode : κ → Int) (ltb : κ → κ → Bool)
variable (hinj : Function.Injective decode)
variable (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
include hinj hlt

/-- The ADT contract keeps all base and presence laws unconditional. -/
theorem enumerated_laws (default : ν) :
    EnumeratedTable.Laws (table ltb default) (observations ltb) default (BST decode) := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  let _ : DecidableLT κ :=
    (Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt).toDecidableLT
  have validEq : BST (ν := ν) decode = OrderedBy Prod.fst :=
    funext fun t => propext (bst_iff_ordered decode (fun _ _ => Iff.rfl) t)
  rw [table_eq_rawTreeTable ltb hlt, observations_eq_rawTreeObservations ltb hlt, validEq]
  exact EnumeratedTable.rawTree_laws default

theorem table_laws (default : ν) :
    TotalTable.Laws (table ltb default) default (fun _ => True) :=
  (enumerated_laws decode ltb hinj hlt default).table_laws

theorem strong_elements :
    letI : LT κ := Representations.SignedComparison.strictOrder decode
    EnumeratedTable.StrongElements (observations (ν := ν) ltb) (BST decode) := by
  let _ : LT κ := Representations.SignedComparison.strictOrder decode
  exact
    { absent_no_entry := fun key _ valid absent =>
        absent_no_entry decode ltb hlt valid key absent
      no_entry_absent := no_entry_absent decode ltb hinj hlt
      keys_sorted := fun _ valid => keys_pairwise decode valid
      keys_nodup := fun _ valid => keys_nodup decode valid }

/-- The exact separator equation retains the source's right-side premise. -/
theorem kvsInsert_split (key : κ) (value : ν) (pivot : κ) (pivotValue : ν)
    (left right : List (κ × ν))
    (hl : ∀ binding ∈ left, decode binding.1 < decode pivot)
    (hr : ∀ binding ∈ right, decode pivot < decode binding.1) :
    kvsInsert ltb key value (left ++ (pivot, pivotValue) :: right) =
      if ltb key pivot then kvsInsert ltb key value left ++ (pivot, pivotValue) :: right
      else if ltb pivot key then left ++ (pivot, pivotValue) :: kvsInsert ltb key value right
      else left ++ (key, value) :: right := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  let _ : DecidableLT κ :=
    (Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt).toDecidableLT
  have equation := Search.OrderedMap.kvsInsert_split
    key value pivot pivotValue left right hl hr
  by_cases before : ltb key pivot = true
  · have before' : key < pivot := (hlt key pivot).mp before
    simpa only [kvsInsert_eq_ordered ltb hlt, ite_eq_left before, ite_eq_left before'] using equation
  · have before' : ¬ key < pivot := mt (hlt key pivot).mpr before
    by_cases after : ltb pivot key = true
    · have after' : pivot < key := (hlt pivot key).mp after
      simpa only [kvsInsert_eq_ordered ltb hlt, ite_eq_right before, ite_eq_right before',
        ite_eq_left after, ite_eq_left after'] using equation
    · have after' : ¬ pivot < key := mt (hlt pivot key).mpr after
      simpa only [kvsInsert_eq_ordered ltb hlt, ite_eq_right before, ite_eq_right before',
        ite_eq_right after, ite_eq_right after'] using equation

theorem elements_insert {t : BinaryTree (κ × ν)} (valid : BST decode t)
    (key : κ) (value : ν) :
    elements (insert ltb key value t) = kvsInsert ltb key value (elements t) := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  let _ : DecidableLT κ :=
    (Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt).toDecidableLT
  have ordered := (bst_iff_ordered decode (fun _ _ => Iff.rfl) t).mp valid
  simpa only [elements_eq, insert_eq_bind ltb hlt, kvsInsert_eq_ordered ltb hlt] using
    Search.OrderedMap.entries_bind ordered key value

/-- Head-winning list meaning, reusing the accepted decoder and equality decision. -/
def listAbs (bindings : List (κ × ν)) : Meaning κ ν :=
  letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  listObserve bindings

/-- Inorder abstraction; this does not introduce another enumeration algorithm. -/
def enumAbs (t : BinaryTree (κ × ν)) : Meaning κ ν :=
  letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  SourceModel.enumAbs t

/-- The independent structural abstraction retains collision-removing child union. -/
def mapOfTree (t : BinaryTree (κ × ν)) : Meaning κ ν :=
  letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  SourceModel.mapOfTree t

@[simp] theorem listAbs_empty :
    listAbs decode ltb hinj hlt ([] : List (κ × ν)) = fun _ => none := rfl

theorem listAbs_cons (binding : κ × ν) (rest : List (κ × ν)) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    listAbs decode ltb hinj hlt (binding :: rest) =
      write binding.1 binding.2 (listAbs decode ltb hinj hlt rest) := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  exact SourceModel.listObserve_cons binding rest

@[simp] theorem enumAbs_empty :
    enumAbs decode ltb hinj hlt (.nil : BinaryTree (κ × ν)) = fun _ => none := rfl

@[simp] theorem mapOfTree_empty :
    mapOfTree decode ltb hinj hlt (.nil : BinaryTree (κ × ν)) = fun _ => none := rfl

/-- First-binding list decoding has finite support, including shadowed raw lists. -/
theorem listAbs_finite_support (bindings : List (κ × ν)) :
    ∃ keys : List κ, ∀ key value,
      listAbs decode ltb hinj hlt bindings key = some value → key ∈ keys := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  exact SourceModel.listObserve_finite_support bindings

/-- Finiteness of enumeration meaning needs no ordering invariant. -/
theorem enumAbs_finite_support (t : BinaryTree (κ × ν)) :
    ∃ keys : List κ, ∀ key value,
      enumAbs decode ltb hinj hlt t key = some value → key ∈ keys := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  exact SourceModel.enumAbs_finite_support t

/-- The independent structural meaning likewise has finite support on every
raw tree; its search agreement still needs the separate invariant. -/
theorem mapOfTree_finite_support (t : BinaryTree (κ × ν)) :
    ∃ keys : List κ, ∀ key value,
      mapOfTree decode ltb hinj hlt t key = some value → key ∈ keys := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  exact SourceModel.mapOfTree_finite_support t

theorem enumAbs_elements (t : BinaryTree (κ × ν)) :
    listAbs decode ltb hinj hlt (elements t) = enumAbs decode ltb hinj hlt t := by
  rw [elements_eq]
  rfl

theorem enumAbs_lookup {t : BinaryTree (κ × ν)} (valid : BST decode t) (key : κ) :
    enumAbs decode ltb hinj hlt t key = lookup? ltb key t := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  let _ : DecidableLT κ :=
    (Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt).toDecidableLT
  have ordered := (bst_iff_ordered decode (fun _ _ => Iff.rfl) t).mp valid
  change SourceModel.enumAbs t key = lookup? ltb key t
  exact (SourceModel.enumAbs_eq_lookup ordered key).trans
    (lookup?_eq_lookup ltb hlt key t).symm

theorem enumAbs_bound {t : BinaryTree (κ × ν)} (valid : BST decode t) (key : κ) :
    hasBinding (enumAbs decode ltb hinj hlt t) key = bound ltb key t :=
  congrArg Option.isSome (enumAbs_lookup decode ltb hinj hlt valid key)

theorem enumAbs_default {t : BinaryTree (κ × ν)} (valid : BST decode t)
    (default : ν) (key : κ) :
    withDefault default (enumAbs decode ltb hinj hlt t) key = lookup ltb default key t :=
  congrArg (fun result => result.getD default) (enumAbs_lookup decode ltb hinj hlt valid key)

theorem listAbs_kvsInsert (key : κ) (value : ν) (bindings : List (κ × ν)) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    listAbs decode ltb hinj hlt (kvsInsert ltb key value bindings) =
      write key value (listAbs decode ltb hinj hlt bindings) := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  let _ : DecidableLT κ :=
    (Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt).toDecidableLT
  change listObserve (kvsInsert ltb key value bindings) = write key value (listObserve bindings)
  rw [kvsInsert_eq_ordered ltb hlt]
  exact SourceModel.listObserve_kvsInsert key value bindings

theorem enumAbs_insert {t : BinaryTree (κ × ν)} (valid : BST decode t)
    (key : κ) (value : ν) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    enumAbs decode ltb hinj hlt (insert ltb key value t) =
      write key value (enumAbs decode ltb hinj hlt t) := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  let _ : DecidableLT κ :=
    (Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt).toDecidableLT
  have ordered := (bst_iff_ordered decode (fun _ _ => Iff.rfl) t).mp valid
  change SourceModel.enumAbs (insert ltb key value t) = write key value (SourceModel.enumAbs t)
  rw [insert_eq_bind ltb hlt]
  exact SourceModel.enumAbs_bind ordered key value

theorem mapOfTree_lookup {t : BinaryTree (κ × ν)} (valid : BST decode t) (key : κ) :
    mapOfTree decode ltb hinj hlt t key = lookup? ltb key t := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  let _ : DecidableLT κ :=
    (Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt).toDecidableLT
  have ordered := (bst_iff_ordered decode (fun _ _ => Iff.rfl) t).mp valid
  change SourceModel.mapOfTree t key = lookup? ltb key t
  exact (SourceModel.mapOfTree_eq_lookup ordered key).trans
    (lookup?_eq_lookup ltb hlt key t).symm

theorem mapOfTree_bound {t : BinaryTree (κ × ν)} (valid : BST decode t) (key : κ) :
    hasBinding (mapOfTree decode ltb hinj hlt t) key = bound ltb key t :=
  congrArg Option.isSome (mapOfTree_lookup decode ltb hinj hlt valid key)

theorem mapOfTree_default {t : BinaryTree (κ × ν)} (valid : BST decode t)
    (default : ν) (key : κ) :
    withDefault default (mapOfTree decode ltb hinj hlt t) key = lookup ltb default key t :=
  congrArg (fun result => result.getD default)
    (mapOfTree_lookup decode ltb hinj hlt valid key)

/-- This transfer invokes the accepted structural update proof, not enum coherence. -/
theorem mapOfTree_insert {t : BinaryTree (κ × ν)} (valid : BST decode t)
    (key : κ) (value : ν) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    mapOfTree decode ltb hinj hlt (insert ltb key value t) =
      write key value (mapOfTree decode ltb hinj hlt t) := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  let _ : DecidableLT κ :=
    (Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt).toDecidableLT
  have ordered := (bst_iff_ordered decode (fun _ _ => Iff.rfl) t).mp valid
  change SourceModel.mapOfTree (insert ltb key value t) = write key value (SourceModel.mapOfTree t)
  rw [insert_eq_bind ltb hlt]
  exact SourceModel.mapOfTree_bind ordered key value

theorem enumAbs_eq_mapOfTree {t : BinaryTree (κ × ν)} (valid : BST decode t) :
    enumAbs decode ltb hinj hlt t = mapOfTree decode ltb hinj hlt t := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  have ordered := (bst_iff_ordered decode (fun _ _ => Iff.rfl) t).mp valid
  exact SourceModel.enumAbs_eq_mapOfTree ordered

theorem elements_relate_structural {t : BinaryTree (κ × ν)} (valid : BST decode t) :
    listAbs decode ltb hinj hlt (elements t) = mapOfTree decode ltb hinj hlt t :=
  (enumAbs_elements decode ltb hinj hlt t).trans
    (enumAbs_eq_mapOfTree decode ltb hinj hlt valid)

/-- Complete partial meanings determine canonical lists, not merely one default view. -/
theorem elements_eq_of_enumAbs_eq {left right : BinaryTree (κ × ν)}
    (hl : BST decode left) (hr : BST decode right)
    (same : enumAbs decode ltb hinj hlt left = enumAbs decode ltb hinj hlt right) :
    elements left = elements right := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  have orderedLeft := (bst_iff_ordered decode (fun _ _ => Iff.rfl) left).mp hl
  have orderedRight := (bst_iff_ordered decode (fun _ _ => Iff.rfl) right).mp hr
  simpa only [elements_eq] using
    SourceModel.entries_eq_of_enumAbs_eq orderedLeft orderedRight same

theorem elements_eq_of_lookup?_eq {left right : BinaryTree (κ × ν)}
    (hl : BST decode left) (hr : BST decode right)
    (same : ∀ key, lookup? ltb key left = lookup? ltb key right) :
    elements left = elements right := by
  apply elements_eq_of_enumAbs_eq decode ltb hinj hlt hl hr
  funext key
  rw [enumAbs_lookup decode ltb hinj hlt hl,
    enumAbs_lookup decode ltb hinj hlt hr, same key]

theorem elements_eq_of_mapOfTree_eq {left right : BinaryTree (κ × ν)}
    (hl : BST decode left) (hr : BST decode right)
    (same : mapOfTree decode ltb hinj hlt left = mapOfTree decode ltb hinj hlt right) :
    elements left = elements right := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  have orderedLeft := (bst_iff_ordered decode (fun _ _ => Iff.rfl) left).mp hl
  have orderedRight := (bst_iff_ordered decode (fun _ _ => Iff.rfl) right).mp hr
  simpa only [elements_eq] using
    SourceModel.entries_eq_of_mapOfTree_eq orderedLeft orderedRight same

theorem model_enum_laws (default : ν) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    EnumeratedTable.ModelLaws (table ltb default) (observations ltb) default
      (BST decode) (enumAbs decode ltb hinj hlt) := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  let _ : DecidableLT κ :=
    (Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt).toDecidableLT
  have validEq : BST (ν := ν) decode = OrderedBy Prod.fst :=
    funext fun t => propext (bst_iff_ordered decode (fun _ _ => Iff.rfl) t)
  change EnumeratedTable.ModelLaws (table ltb default) (observations ltb) default
    (BST decode) SourceModel.enumAbs
  rw [table_eq_rawTreeTable ltb hlt, observations_eq_rawTreeObservations ltb hlt, validEq]
  exact EnumeratedTable.rawTree_model_enum default

theorem model_structural_laws (default : ν) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    EnumeratedTable.ModelLaws (table ltb default) (observations ltb) default
      (BST decode) (mapOfTree decode ltb hinj hlt) := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  let _ : DecidableLT κ :=
    (Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt).toDecidableLT
  have validEq : BST (ν := ν) decode = OrderedBy Prod.fst :=
    funext fun t => propext (bst_iff_ordered decode (fun _ _ => Iff.rfl) t)
  change EnumeratedTable.ModelLaws (table ltb default) (observations ltb) default
    (BST decode) SourceModel.mapOfTree
  rw [table_eq_rawTreeTable ltb hlt, observations_eq_rawTreeObservations ltb hlt, validEq]
  exact EnumeratedTable.rawTree_model_structural default

/-- Reuse the existing arbitrary chronological history client. -/
theorem enumAbs_setAll (default : ν) (writes : List (κ × ν))
    {t : BinaryTree (κ × ν)} (valid : BST decode t) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    enumAbs decode ltb hinj hlt (TotalTable.setAll (table ltb default) writes t) =
      writeAll writes (enumAbs decode ltb hinj hlt t) := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  exact (model_enum_laws decode ltb hinj hlt default).setAll writes valid

theorem mapOfTree_setAll (default : ν) (writes : List (κ × ν))
    {t : BinaryTree (κ × ν)} (valid : BST decode t) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    mapOfTree decode ltb hinj hlt (TotalTable.setAll (table ltb default) writes t) =
      writeAll writes (mapOfTree decode ltb hinj hlt t) := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  exact (model_structural_laws decode ltb hinj hlt default).setAll writes valid

end CompleteContracts

/-- Equal default-valued observations can hide a stored default binding. -/
theorem default_observation_not_canonical :
    (∀ query : Int,
      lookup (fun a b : Int => decide (a < b)) 0 query .nil =
        lookup (fun a b : Int => decide (a < b)) 0 query
          (insert (fun a b : Int => decide (a < b)) 0 0 .nil)) ∧
      elements (.nil : BinaryTree (Int × Nat)) ≠
        elements (insert (fun a b : Int => decide (a < b)) 0 0 .nil) := by
  constructor
  · intro query
    rw [insert_empty, lookup_empty, lookup_node]
    split
    · rfl
    · split <;> rfl
  · rw [elements_eq, insert_empty, elements_eq, Search.OrderedTree.entries_node]
    simp

/-- A malformed tree retains its hidden pair in enumeration, but search can miss it. -/
theorem malformed_membership_boundary :
    let t : BinaryTree (Int × Nat) := .node (0, 0) (.node (1, 7) .nil .nil) .nil
    (1, 7) ∈ elements t ∧
      lookup (fun a b : Int => decide (a < b)) 99 1 t = 99 ∧
      bound (fun a b : Int => decide (a < b)) 1 t = false := by
  decide

/-- Type-valued payloads require neither payload equality nor a distinguished value. -/
theorem type_payload_same_key (default value : Type v) (key : Int)
    (t : BinaryTree (Int × Type v)) :
    lookup (fun a b : Int => decide (a < b)) default key
      (insert (fun a b : Int => decide (a < b)) key value t) = value :=
  lookup_insert_eq id (fun a b : Int => decide (a < b))
    (fun _ _ => by simp) default key value t

end Search.OrderedMap.DecodedKeys
