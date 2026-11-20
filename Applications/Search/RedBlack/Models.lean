import Applications.Search.RedBlack.Ordering
import Applications.Search.OrderedMap.DecodedKeysModels

/-!
# Map observations of source colored trees

Presence is observed before applying a caller default. The model bridges use
the accepted ordinary-tree abstractions after erasing colors, and condition
source update laws on strict decoded BST validity.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.RedBlack

universe u v
variable {κ : Type u} {ν : Type v}

/-- Presence distinguishes a stored default-valued payload from absence. -/
def bound (ltb : κ → κ → Bool) (query : κ) (t : Tree κ ν) : Bool :=
  (lookup? ltb query t).isSome

@[simp] theorem bound_nil (ltb : κ → κ → Bool) (query : κ) :
    bound ltb query (.nil : Tree κ ν) = false := rfl

theorem bound_default (ltb : κ → κ → Bool) (default : ν) (query : κ)
    (t : Tree κ ν) (absent : bound ltb query t = false) :
    lookup ltb default query t = default := by
  cases found : lookup? ltb query t with
  | none => simp [lookup, found]
  | some value => simp [bound, found] at absent

/-- One successful payload is independent of all caller defaults. -/
theorem bound_value (ltb : κ → κ → Bool) (query : κ) (t : Tree κ ν)
    (present : bound ltb query t = true) :
    ∃ value : ν, ∀ default : ν, lookup ltb default query t = value := by
  cases found : lookup? ltb query t with
  | none => simp [bound, found] at present
  | some value => exact ⟨value, fun _ => by simp [lookup, found]⟩

theorem eraseColors_bound (ltb : κ → κ → Bool) (query : κ) (t : Tree κ ν) :
    OrderedMap.DecodedKeys.bound ltb query (eraseColors t) = bound ltb query t :=
  congrArg Option.isSome (eraseColors_lookup? ltb query t)

theorem relation_elements (R : κ → κ → Prop) (pivot : κ) {t : Tree κ ν}
    (all : ForallT (fun key _ => R key pivot) t) :
    ∀ binding ∈ elements t, R binding.1 pivot :=
  (forallT_elements_iff (fun key _ => R key pivot) t).mp all

theorem decoded_keys_pairwise (decode : κ → Int) {t : Tree κ ν} (valid : BST decode t) :
    ((elements t).map (fun binding => decode binding.1)).Pairwise (· < ·) := by
  simpa only [eraseColors_elements] using
    OrderedMap.DecodedKeys.decoded_keys_pairwise decode valid

theorem keys_pairwise (decode : κ → Int) {t : Tree κ ν} (valid : BST decode t) :
    ((elements t).map Prod.fst).Pairwise (fun a b => decode a < decode b) := by
  simpa only [eraseColors_elements] using OrderedMap.DecodedKeys.keys_pairwise decode valid

theorem keys_sorted (decode : κ → Int) {t : Tree κ ν} (valid : BST decode t) :
    ((elements t).map Prod.fst).IsChain (fun a b => decode a ≤ decode b) := by
  simpa only [eraseColors_elements] using OrderedMap.DecodedKeys.keys_sorted decode valid

theorem keys_nodup (decode : κ → Int) {t : Tree κ ν} (valid : BST decode t) :
    ((elements t).map Prod.fst).Nodup := by
  simpa only [eraseColors_elements] using OrderedMap.DecodedKeys.keys_nodup decode valid

section StrictReflection
variable (decode : κ → Int) (ltb : κ → κ → Bool)
variable (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
include hlt

/-- Stored bindings are found on valid trees without original-key injectivity. -/
theorem lookup?_eq_some_of_mem {t : Tree κ ν} {key : κ} {value : ν}
    (valid : BST decode t) (member : (key, value) ∈ elements t) :
    lookup? ltb key t = some value := by
  have stored : (key, value) ∈ OrderedMap.DecodedKeys.elements (eraseColors t) := by
    rwa [eraseColors_elements]
  exact (eraseColors_lookup? ltb key t).symm.trans
    (OrderedMap.DecodedKeys.lookup?_eq_some_of_mem decode ltb hlt valid stored)

theorem elements_sound {t : Tree κ ν} {key : κ} {value : ν}
    (valid : BST decode t) (member : (key, value) ∈ elements t) :
    bound ltb key t = true ∧ ∀ default : ν, lookup ltb default key t = value := by
  have found := lookup?_eq_some_of_mem decode ltb hlt valid member
  exact ⟨congrArg Option.isSome found,
    fun default => congrArg (fun result => result.getD default) found⟩

/-- Search absence rules out an enumerated binding only under BST. -/
theorem absent_no_entry {t : Tree κ ν} (valid : BST decode t) (key : κ)
    (absent : bound ltb key t = false) (value : ν) : (key, value) ∉ elements t := by
  intro member
  have present := (elements_sound decode ltb hlt valid member).1
  rw [absent] at present
  cases present

theorem bound_ins_eq {t : Tree κ ν} (valid : BST decode t) (key : κ) (value : ν) :
    bound ltb key (ins ltb key value t) = true :=
  congrArg Option.isSome (lookup?_ins_eq decode ltb hlt valid key value)

theorem bound_insert_eq {t : Tree κ ν} (valid : BST decode t) (key : κ) (value : ν) :
    bound ltb key (insert ltb key value t) = true :=
  congrArg Option.isSome (lookup?_insert_eq decode ltb hlt valid key value)

end StrictReflection

section InjectiveReflection
variable (decode : κ → Int) (ltb : κ → κ → Bool)
variable (hinj : Function.Injective decode)
variable (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
include hinj hlt

/-- Successful search identifies an original pair on arbitrary raw trees. -/
theorem mem_elements_of_lookup? {t : Tree κ ν} {key : κ} {value : ν}
    (found : lookup? ltb key t = some value) : (key, value) ∈ elements t := by
  have member := OrderedMap.DecodedKeys.mem_elements_of_lookup? decode ltb hinj hlt
    ((eraseColors_lookup? ltb key t).trans found)
  simpa only [eraseColors_elements] using member

theorem elements_complete (default : ν) (key : κ) (value : ν) (t : Tree κ ν)
    (present : bound ltb key t = true) (found : lookup ltb default key t = value) :
    (key, value) ∈ elements t :=
  mem_elements_of_lookup? decode ltb hinj hlt
    ((OrderedMap.binding_iff default (fun query => lookup? ltb query t) key value).mpr
      ⟨present, found⟩)

theorem lookup?_finite_support (t : Tree κ ν) :
    ∃ keys : List κ, ∀ key value, lookup? ltb key t = some value → key ∈ keys := by
  simpa only [eraseColors_lookup?] using
    OrderedMap.DecodedKeys.lookup?_finite_support decode ltb hinj hlt (eraseColors t)

/-- Missing enumeration entries imply search absence on raw trees. -/
theorem no_entry_absent (key : κ) (t : Tree κ ν)
    (absent : ∀ value, (key, value) ∉ elements t) : bound ltb key t = false := by
  have ordinary : ∀ value, (key, value) ∉ OrderedMap.DecodedKeys.elements (eraseColors t) := by
    simpa only [eraseColors_elements] using absent
  simpa only [eraseColors_bound] using
    OrderedMap.DecodedKeys.no_entry_absent decode ltb hinj hlt key (eraseColors t) ordinary

theorem bound_ins_neq {t : Tree κ ν} (valid : BST decode t)
    (key query : κ) (value : ν) (different : key ≠ query) :
    bound ltb query (ins ltb key value t) = bound ltb query t :=
  congrArg Option.isSome (lookup?_ins_neq decode ltb hinj hlt valid key query value different)

theorem bound_insert_neq {t : Tree κ ν} (valid : BST decode t)
    (key query : κ) (value : ν) (different : key ≠ query) :
    bound ltb query (insert ltb key value t) = bound ltb query t :=
  congrArg Option.isSome (lookup?_insert_neq decode ltb hinj hlt valid key query value different)

end InjectiveReflection

/-- The existing partial-map operation interface uses the actual source insertion. -/
def ops (ltb : κ → κ → Bool) : OrderedMap.Ops κ ν (Tree κ ν) where
  empty := empty
  bind := insert ltb
  lookup := lookup? ltb

def table (ltb : κ → κ → Bool) (default : ν) : TotalTable.Ops κ ν (Tree κ ν) :=
  TotalTable.ofPartial (ops ltb) default

def observations (ltb : κ → κ → Bool) :
    OrderedMap.EnumeratedTable.Observations κ ν (Tree κ ν) :=
  OrderedMap.EnumeratedTable.observationsOfPartial (ops ltb) elements

/-- The accepted valid-state adapter retains the same source computations. -/
def validOps (decode : κ → Int) (ltb : κ → κ → Bool)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b) :
    OrderedMap.Ops κ ν {t : Tree κ ν // BST decode t} :=
  (ops ltb).restrict (BST decode) (bst_nil decode)
    (fun key value _ valid => insert_bst decode ltb hlt valid key value)

section CompleteContracts
variable (decode : κ → Int) (ltb : κ → κ → Bool)
variable (hinj : Function.Injective decode)
variable (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
include hinj hlt

/-- Canonical enumeration transports the proved source search equation to the
accepted replacement-aware list insertion. No tree-shape equation is asserted. -/
theorem elements_ins {t : Tree κ ν} (valid : BST decode t) (key : κ) (value : ν) :
    elements (ins ltb key value t) =
      OrderedMap.DecodedKeys.kvsInsert ltb key value (elements t) := by
  have same := OrderedMap.DecodedKeys.elements_eq_of_lookup?_eq decode ltb hinj hlt
    (ins_bst decode ltb hlt valid key value)
    (OrderedMap.DecodedKeys.bst_insert decode ltb hlt valid key value)
    (fun query => by
      rw [eraseColors_lookup?]
      exact lookup?_ins_eq_unbalanced decode ltb hlt valid key value query)
  simpa only [eraseColors_elements,
    OrderedMap.DecodedKeys.elements_insert decode ltb hinj hlt valid key value] using same

theorem elements_insert {t : Tree κ ν} (valid : BST decode t) (key : κ) (value : ν) :
    elements (insert ltb key value t) =
      OrderedMap.DecodedKeys.kvsInsert ltb key value (elements t) := by
  rw [insert_eq_makeBlack_ins, makeBlack_elements,
    elements_ins decode ltb hinj hlt valid]

/-- Reuse the accepted head-winning list abstraction. -/
def listAbs (bindings : List (κ × ν)) : OrderedMap.Meaning κ ν :=
  OrderedMap.DecodedKeys.listAbs decode ltb hinj hlt bindings

/-- The enumeration abstraction keeps the original keys and optional presence. -/
def enumAbs (t : Tree κ ν) : OrderedMap.Meaning κ ν :=
  OrderedMap.DecodedKeys.enumAbs decode ltb hinj hlt (eraseColors t)

/-- The independent structural abstraction retains the accepted collision-removing union. -/
def mapOfTree (t : Tree κ ν) : OrderedMap.Meaning κ ν :=
  OrderedMap.DecodedKeys.mapOfTree decode ltb hinj hlt (eraseColors t)

@[simp] theorem listAbs_empty :
    listAbs decode ltb hinj hlt ([] : List (κ × ν)) = fun _ => none := rfl

theorem listAbs_cons (binding : κ × ν) (rest : List (κ × ν)) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    listAbs decode ltb hinj hlt (binding :: rest) =
      OrderedMap.write binding.1 binding.2 (listAbs decode ltb hinj hlt rest) :=
  OrderedMap.DecodedKeys.listAbs_cons decode ltb hinj hlt binding rest

@[simp] theorem enumAbs_empty :
    enumAbs decode ltb hinj hlt (empty : Tree κ ν) = fun _ => none := rfl

@[simp] theorem mapOfTree_empty :
    mapOfTree decode ltb hinj hlt (empty : Tree κ ν) = fun _ => none := rfl

theorem listAbs_finite_support (bindings : List (κ × ν)) :
    ∃ keys : List κ, ∀ key value,
      listAbs decode ltb hinj hlt bindings key = some value → key ∈ keys :=
  OrderedMap.DecodedKeys.listAbs_finite_support decode ltb hinj hlt bindings

theorem enumAbs_finite_support (t : Tree κ ν) :
    ∃ keys : List κ, ∀ key value,
      enumAbs decode ltb hinj hlt t key = some value → key ∈ keys :=
  OrderedMap.DecodedKeys.enumAbs_finite_support decode ltb hinj hlt (eraseColors t)

theorem mapOfTree_finite_support (t : Tree κ ν) :
    ∃ keys : List κ, ∀ key value,
      mapOfTree decode ltb hinj hlt t key = some value → key ∈ keys :=
  OrderedMap.DecodedKeys.mapOfTree_finite_support decode ltb hinj hlt (eraseColors t)

theorem enumAbs_elements (t : Tree κ ν) :
    listAbs decode ltb hinj hlt (elements t) = enumAbs decode ltb hinj hlt t := by
  unfold listAbs enumAbs
  rw [← eraseColors_elements]
  exact OrderedMap.DecodedKeys.enumAbs_elements decode ltb hinj hlt (eraseColors t)

theorem enumAbs_lookup {t : Tree κ ν} (valid : BST decode t) (key : κ) :
    enumAbs decode ltb hinj hlt t key = lookup? ltb key t :=
  (OrderedMap.DecodedKeys.enumAbs_lookup decode ltb hinj hlt valid key).trans
    (eraseColors_lookup? ltb key t)

theorem enumAbs_bound {t : Tree κ ν} (valid : BST decode t) (key : κ) :
    OrderedMap.hasBinding (enumAbs decode ltb hinj hlt t) key = bound ltb key t :=
  congrArg Option.isSome (enumAbs_lookup decode ltb hinj hlt valid key)

theorem enumAbs_default {t : Tree κ ν} (valid : BST decode t) (default : ν) (key : κ) :
    OrderedMap.withDefault default (enumAbs decode ltb hinj hlt t) key =
      lookup ltb default key t :=
  congrArg (fun result => result.getD default) (enumAbs_lookup decode ltb hinj hlt valid key)

theorem listAbs_kvsInsert (key : κ) (value : ν) (bindings : List (κ × ν)) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    listAbs decode ltb hinj hlt (OrderedMap.DecodedKeys.kvsInsert ltb key value bindings) =
      OrderedMap.write key value (listAbs decode ltb hinj hlt bindings) :=
  OrderedMap.DecodedKeys.listAbs_kvsInsert decode ltb hinj hlt key value bindings

theorem enumAbs_insert {t : Tree κ ν} (valid : BST decode t) (key : κ) (value : ν) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    enumAbs decode ltb hinj hlt (insert ltb key value t) =
      OrderedMap.write key value (enumAbs decode ltb hinj hlt t) := by
  let _ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  rw [← enumAbs_elements decode ltb hinj hlt (insert ltb key value t),
    elements_insert decode ltb hinj hlt valid,
    listAbs_kvsInsert decode ltb hinj hlt, enumAbs_elements decode ltb hinj hlt]

theorem mapOfTree_lookup {t : Tree κ ν} (valid : BST decode t) (key : κ) :
    mapOfTree decode ltb hinj hlt t key = lookup? ltb key t :=
  (OrderedMap.DecodedKeys.mapOfTree_lookup decode ltb hinj hlt valid key).trans
    (eraseColors_lookup? ltb key t)

theorem mapOfTree_bound {t : Tree κ ν} (valid : BST decode t) (key : κ) :
    OrderedMap.hasBinding (mapOfTree decode ltb hinj hlt t) key = bound ltb key t :=
  congrArg Option.isSome (mapOfTree_lookup decode ltb hinj hlt valid key)

theorem mapOfTree_default {t : Tree κ ν} (valid : BST decode t) (default : ν) (key : κ) :
    OrderedMap.withDefault default (mapOfTree decode ltb hinj hlt t) key =
      lookup ltb default key t :=
  congrArg (fun result => result.getD default) (mapOfTree_lookup decode ltb hinj hlt valid key)

/-- Structural update uses its independent lookup agreement and the proved
source update laws; it does not substitute enumeration for the structural meaning. -/
theorem mapOfTree_insert {t : Tree κ ν} (valid : BST decode t) (key : κ) (value : ν) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    mapOfTree decode ltb hinj hlt (insert ltb key value t) =
      OrderedMap.write key value (mapOfTree decode ltb hinj hlt t) := by
  let _ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  funext query
  rw [mapOfTree_lookup decode ltb hinj hlt (insert_bst decode ltb hlt valid key value)]
  change lookup? ltb query (insert ltb key value t) =
    if query = key then some value else mapOfTree decode ltb hinj hlt t query
  by_cases same : query = key
  · rw [ite_eq_left same, same, lookup?_insert_eq decode ltb hlt valid]
  · rw [ite_eq_right same,
      lookup?_insert_neq decode ltb hinj hlt valid key query value (Ne.symm same),
      mapOfTree_lookup decode ltb hinj hlt valid]

theorem enumAbs_eq_mapOfTree {t : Tree κ ν} (valid : BST decode t) :
    enumAbs decode ltb hinj hlt t = mapOfTree decode ltb hinj hlt t :=
  OrderedMap.DecodedKeys.enumAbs_eq_mapOfTree decode ltb hinj hlt valid

theorem elements_relate_structural {t : Tree κ ν} (valid : BST decode t) :
    listAbs decode ltb hinj hlt (elements t) = mapOfTree decode ltb hinj hlt t :=
  (enumAbs_elements decode ltb hinj hlt t).trans
    (enumAbs_eq_mapOfTree decode ltb hinj hlt valid)

/-- Complete partial meanings determine canonical lists; one default view does not. -/
theorem elements_eq_of_enumAbs_eq {left right : Tree κ ν}
    (hl : BST decode left) (hr : BST decode right)
    (same : enumAbs decode ltb hinj hlt left = enumAbs decode ltb hinj hlt right) :
    elements left = elements right := by
  simpa only [eraseColors_elements] using
    OrderedMap.DecodedKeys.elements_eq_of_enumAbs_eq decode ltb hinj hlt hl hr same

theorem elements_eq_of_lookup?_eq {left right : Tree κ ν}
    (hl : BST decode left) (hr : BST decode right)
    (same : ∀ key, lookup? ltb key left = lookup? ltb key right) :
    elements left = elements right := by
  have ordinary := OrderedMap.DecodedKeys.elements_eq_of_lookup?_eq decode ltb hinj hlt hl hr
    (fun key => by simpa only [eraseColors_lookup?] using same key)
  simpa only [eraseColors_elements] using ordinary

theorem elements_eq_of_mapOfTree_eq {left right : Tree κ ν}
    (hl : BST decode left) (hr : BST decode right)
    (same : mapOfTree decode ltb hinj hlt left = mapOfTree decode ltb hinj hlt right) :
    elements left = elements right := by
  simpa only [eraseColors_elements] using
    OrderedMap.DecodedKeys.elements_eq_of_mapOfTree_eq decode ltb hinj hlt hl hr same

/-- The source realization satisfies the accepted validity-guarded enumeration model. -/
theorem model_enum_laws (default : ν) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    OrderedMap.EnumeratedTable.ModelLaws (table ltb default) (observations ltb) default
      (BST decode) (enumAbs decode ltb hinj hlt) := by
  let _ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  exact
    { empty_valid := bst_nil decode
      set_valid := fun key value _ valid => insert_bst decode ltb hlt valid key value
      empty := enumAbs_empty decode ltb hinj hlt
      bound := fun _ key valid => enumAbs_bound decode ltb hinj hlt valid key
      get := fun _ key valid => enumAbs_default decode ltb hinj hlt valid default key
      set := fun _ key value valid => (enumAbs_insert decode ltb hinj hlt valid key value).symm
      elements := fun t _ => (enumAbs_elements decode ltb hinj hlt t).symm }

theorem model_structural_laws (default : ν) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    OrderedMap.EnumeratedTable.ModelLaws (table ltb default) (observations ltb) default
      (BST decode) (mapOfTree decode ltb hinj hlt) := by
  let _ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  exact
    { empty_valid := bst_nil decode
      set_valid := fun key value _ valid => insert_bst decode ltb hlt valid key value
      empty := mapOfTree_empty decode ltb hinj hlt
      bound := fun _ key valid => mapOfTree_bound decode ltb hinj hlt valid key
      get := fun _ key valid => mapOfTree_default decode ltb hinj hlt valid default key
      set := fun _ key value valid => (mapOfTree_insert decode ltb hinj hlt valid key value).symm
      elements := fun _ valid => (elements_relate_structural decode ltb hinj hlt valid).symm }

/-- Total-table update laws retain BST validity on the raw colored carrier. -/
theorem table_laws (default : ν) :
    TotalTable.Laws (table ltb default) default (BST decode) := by
  let _ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  exact (model_enum_laws decode ltb hinj hlt default).totalLaws

theorem strong_elements :
    letI : LT κ := Representations.SignedComparison.strictOrder decode
    OrderedMap.EnumeratedTable.StrongElements (observations (ν := ν) ltb) (BST decode) := by
  let _ : LT κ := Representations.SignedComparison.strictOrder decode
  exact
    { absent_no_entry := fun key _ valid absent =>
        absent_no_entry decode ltb hlt valid key absent
      no_entry_absent := no_entry_absent decode ltb hinj hlt
      keys_sorted := fun _ valid => keys_pairwise decode valid
      keys_nodup := fun _ valid => keys_nodup decode valid }

/-- Unconditional partial-map laws apply to the existing BST-valid subtype adapter. -/
theorem partial_enum_laws :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    OrderedMap.Laws (validOps (ν := ν) decode ltb hlt)
      (fun t => enumAbs decode ltb hinj hlt t.1) := by
  let _ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  exact OrderedMap.Laws.ofValid (bst_nil decode)
    (fun key value _ valid => insert_bst decode ltb hlt valid key value)
    (enumAbs_empty decode ltb hinj hlt)
    (fun key value _ valid => enumAbs_insert decode ltb hinj hlt valid key value)
    (fun key _ valid => (enumAbs_lookup decode ltb hinj hlt valid key).symm)

theorem partial_structural_laws :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    OrderedMap.Laws (validOps (ν := ν) decode ltb hlt)
      (fun t => mapOfTree decode ltb hinj hlt t.1) := by
  let _ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  exact OrderedMap.Laws.ofValid (bst_nil decode)
    (fun key value _ valid => insert_bst decode ltb hlt valid key value)
    (mapOfTree_empty decode ltb hinj hlt)
    (fun key value _ valid => mapOfTree_insert decode ltb hinj hlt valid key value)
    (fun key _ valid => (mapOfTree_lookup decode ltb hinj hlt valid key).symm)

end CompleteContracts

end Search.RedBlack
