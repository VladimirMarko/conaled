import Applications.Search.OrderedMap.Enumeration
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.List.Sort

/-!
# Decoded keys for the source binary search tree

The executable wrappers receive only a supplied Boolean comparison. Their
branches reuse OrderedMap.lookup and OrderedMap.bind; decoding and reflection
are proof parameters, never arguments to those wrappers. Traversal reuses the
existing accumulator fold. Weak decoder equations do not require injectivity.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap.DecodedKeys

universe u v
variable {κ : Type u} {ν : Type v}
open Search.OrderedTree (All OrderedBy entries)

/-- Map only keys through the existing tree map. Payloads retain their universe. -/
def mapKeys (decode : κ → Int) (t : BinaryTree (κ × ν)) : BinaryTree (Int × ν) :=
  t.map (fun binding => (decode binding.1, binding.2))

@[simp] theorem mapKeys_empty (decode : κ → Int) :
    mapKeys decode (.nil : BinaryTree (κ × ν)) = .nil := rfl

theorem mapKeys_node (decode : κ → Int) (binding : κ × ν)
    (left right : BinaryTree (κ × ν)) :
    mapKeys decode (.node binding left right) =
      .node (decode binding.1, binding.2) (mapKeys decode left) (mapKeys decode right) := rfl

theorem entries_mapKeys (decode : κ → Int) (t : BinaryTree (κ × ν)) :
    entries (mapKeys decode t) =
      (entries t).map (fun binding => (decode binding.1, binding.2)) :=
  Trees.inorder_map _ t

/-- Extract.elements_aux is the existing fast traversal, with an arbitrary suffix. -/
abbrev elementsAux (t : BinaryTree (κ × ν)) := fastEntriesAcc t

/-- Extract.elements calls that fast traversal at the empty suffix. -/
abbrev elements (t : BinaryTree (κ × ν)) := fastEntries t

@[simp] theorem elementsAux_empty (suffix : List (κ × ν)) :
    elementsAux .nil suffix = suffix := rfl

theorem elementsAux_node (binding : κ × ν) (left right : BinaryTree (κ × ν))
    (suffix : List (κ × ν)) :
    elementsAux (.node binding left right) suffix =
      elementsAux left (binding :: elementsAux right suffix) := rfl

theorem elementsAux_eq (t : BinaryTree (κ × ν)) (suffix : List (κ × ν)) :
    elementsAux t suffix = entries t ++ suffix :=
  fastEntriesAcc_eq t suffix

theorem elements_eq (t : BinaryTree (κ × ν)) : elements t = entries t :=
  fastEntries_eq t

@[simp] theorem elements_empty : elements (.nil : BinaryTree (κ × ν)) = [] := rfl

theorem map_elementsAux (decode : κ → Int) (t : BinaryTree (κ × ν))
    (suffix : List (κ × ν)) :
    (elementsAux t suffix).map (fun binding => (decode binding.1, binding.2)) =
      elementsAux (mapKeys decode t)
        (suffix.map (fun binding => (decode binding.1, binding.2))) := by
  rw [elementsAux_eq, elementsAux_eq, entries_mapKeys, List.map_append]

theorem map_elements (decode : κ → Int) (t : BinaryTree (κ × ν)) :
    (elements t).map (fun binding => (decode binding.1, binding.2)) =
      elements (mapKeys decode t) := by
  rw [elements_eq, elements_eq, entries_mapKeys]

/-- The source all-node predicate reuses the common tree predicate. -/
abbrev ForallT (P : κ → ν → Prop) (t : BinaryTree (κ × ν)) :=
  All (fun binding => P binding.1 binding.2) t

/-- Strict separators constrain every descendant of both subtrees. -/
def BST (decode : κ → Int) (t : BinaryTree (κ × ν)) : Prop :=
  OrderedBy (fun binding => decode binding.1) t

@[simp] theorem bst_empty (decode : κ → Int) :
    BST decode (.nil : BinaryTree (κ × ν)) := trivial

theorem bst_iff_mapKeys (decode : κ → Int) (t : BinaryTree (κ × ν)) :
    BST decode t ↔ OrderedBy Prod.fst (mapKeys decode t) := by
  change OrderedBy (fun binding => decode binding.1) t ↔
    OrderedBy Prod.fst (t.map (fun binding => (decode binding.1, binding.2)))
  induction t with
  | nil => rfl
  | node binding left right ihl ihr =>
      simp only [OrderedBy, BinaryTree.map, Search.OrderedTree.all_map, ← ihl, ← ihr]

theorem all_mapKeys (decode : κ → Int) (P : Int × ν → Prop)
    (t : BinaryTree (κ × ν)) :
    All P (mapKeys decode t) ↔
      All (fun binding => P (decode binding.1, binding.2)) t :=
  Search.OrderedTree.all_map _ P t

theorem all_elements {P : κ × ν → Prop} {t : BinaryTree (κ × ν)} (all : All P t) :
    ∀ binding ∈ elements t, P binding := by
  rw [elements_eq]
  exact all_entries all

theorem forallT_elements_iff (P : κ → ν → Prop) (t : BinaryTree (κ × ν)) :
    ForallT P t ↔ ∀ binding ∈ elements t, P binding.1 binding.2 := by
  simp only [ForallT, elements_eq, Search.OrderedTree.all_iff,
    Search.OrderedTree.contains_iff_mem_entries]

theorem relation_elements (R : κ → κ → Prop) (pivot : κ)
    {t : BinaryTree (κ × ν)} (all : ForallT (fun key _ => R key pivot) t) :
    ∀ binding ∈ elements t, R binding.1 pivot :=
  all_elements all

/-- Strict order on decoded projected keys needs no injection of the decoder. -/
theorem decoded_keys_pairwise (decode : κ → Int) {t : BinaryTree (κ × ν)}
    (valid : BST decode t) :
    ((elements t).map (fun binding => decode binding.1)).Pairwise (· < ·) := by
  have ordered := ordered_entries_keys_pairwise ((bst_iff_mapKeys decode t).mp valid)
  simpa only [elements_eq, entries_mapKeys, List.map_map, Function.comp_def] using ordered

theorem keys_pairwise (decode : κ → Int) {t : BinaryTree (κ × ν)}
    (valid : BST decode t) :
    ((elements t).map Prod.fst).Pairwise (fun a b => decode a < decode b) := by
  simpa only [List.pairwise_map] using decoded_keys_pairwise decode valid

/-- Recover the source's non-strict adjacent-chain specification. -/
theorem keys_sorted (decode : κ → Int) {t : BinaryTree (κ × ν)}
    (valid : BST decode t) :
    ((elements t).map Prod.fst).IsChain (fun a b => decode a ≤ decode b) :=
  ((keys_pairwise decode valid).imp fun less => le_of_lt less).isChain

/-- Uniqueness is of original projected keys, not merely of whole pairs. -/
theorem keys_nodup (decode : κ → Int) {t : BinaryTree (κ × ν)}
    (valid : BST decode t) : ((elements t).map Prod.fst).Nodup := by
  apply List.Nodup.of_map (f := decode)
  simpa only [List.map_map, Function.comp_def] using
    (decoded_keys_pairwise decode valid).nodup

section Comparison
variable [LT κ] [DecidableLT κ]

/-- A branch-preserving decoder commutes with directed search on every raw tree. -/
theorem lookup_mapKeys (decode : κ → Int)
    (compatible : ∀ a b : κ, a < b ↔ decode a < decode b)
    (query : κ) (t : BinaryTree (κ × ν)) :
    Search.OrderedMap.lookup (decode query) (mapKeys decode t) =
      Search.OrderedMap.lookup query t := by
  induction t with
  | nil => rfl
  | node binding left right ihl ihr =>
      by_cases ql : query < binding.1
      · have decoded : decode query < decode binding.1 := (compatible _ _).mp ql
        simp only [mapKeys_node, Search.OrderedMap.lookup, ite_eq_left ql,
          ite_eq_left decoded, ihl]
      · have decodedNot : ¬ decode query < decode binding.1 :=
          mt (compatible _ _).mpr ql
        by_cases qr : binding.1 < query
        · have decoded : decode binding.1 < decode query := (compatible _ _).mp qr
          simp only [mapKeys_node, Search.OrderedMap.lookup, ite_eq_right ql,
            ite_eq_right decodedNot, ite_eq_left qr, ite_eq_left decoded, ihr]
        · have decodedNotReverse : ¬ decode binding.1 < decode query :=
            mt (compatible _ _).mpr qr
          simp only [mapKeys_node, Search.OrderedMap.lookup, ite_eq_right ql,
            ite_eq_right decodedNot, ite_eq_right qr, ite_eq_right decodedNotReverse]

/-- Equality replacement maps the newly supplied key and payload. -/
theorem mapKeys_bind (decode : κ → Int)
    (compatible : ∀ a b : κ, a < b ↔ decode a < decode b)
    (key : κ) (value : ν) (t : BinaryTree (κ × ν)) :
    mapKeys decode (Search.OrderedMap.bind key value t) =
      Search.OrderedMap.bind (decode key) value (mapKeys decode t) := by
  induction t with
  | nil => rfl
  | node binding left right ihl ihr =>
      by_cases kl : key < binding.1
      · have decoded : decode key < decode binding.1 := (compatible _ _).mp kl
        simp only [mapKeys_node, Search.OrderedMap.bind, ite_eq_left kl,
          ite_eq_left decoded, ihl]
      · have decodedNot : ¬ decode key < decode binding.1 :=
          mt (compatible _ _).mpr kl
        by_cases kr : binding.1 < key
        · have decoded : decode binding.1 < decode key := (compatible _ _).mp kr
          simp only [mapKeys_node, Search.OrderedMap.bind, ite_eq_right kl,
            ite_eq_right decodedNot, ite_eq_left kr, ite_eq_left decoded, ihr]
        · have decodedNotReverse : ¬ decode binding.1 < decode key :=
            mt (compatible _ _).mpr kr
          simp only [mapKeys_node, Search.OrderedMap.bind, ite_eq_right kl,
            ite_eq_right decodedNot, ite_eq_right kr, ite_eq_right decodedNotReverse]

end Comparison

private abbrev booleanOrder (ltb : κ → κ → Bool) : LT κ :=
  ⟨fun a b => ltb a b = true⟩

private abbrev booleanDecision (ltb : κ → κ → Bool) :
    @DecidableLT κ (booleanOrder ltb) :=
  fun a b => inferInstanceAs (Decidable (ltb a b = true))

/-- The runtime operation receives no decoder, injection, or reflection proof. -/
def lookup? (ltb : κ → κ → Bool) (query : κ) (t : BinaryTree (κ × ν)) : Option ν :=
  @Search.OrderedMap.lookup κ ν (booleanOrder ltb) (booleanDecision ltb) query t

def lookup (ltb : κ → κ → Bool) (default : ν) (query : κ)
    (t : BinaryTree (κ × ν)) : ν := (lookup? ltb query t).getD default

def bound (ltb : κ → κ → Bool) (query : κ) (t : BinaryTree (κ × ν)) : Bool :=
  (lookup? ltb query t).isSome

def insert (ltb : κ → κ → Bool) (key : κ) (value : ν)
    (t : BinaryTree (κ × ν)) : BinaryTree (κ × ν) :=
  @Search.OrderedMap.bind κ ν (booleanOrder ltb) (booleanDecision ltb) key value t

def kvsInsert (ltb : κ → κ → Bool) (key : κ) (value : ν)
    (bindings : List (κ × ν)) : List (κ × ν) :=
  @Search.OrderedMap.kvsInsert κ ν (booleanOrder ltb) (booleanDecision ltb) key value bindings

@[simp] theorem lookup?_empty (ltb : κ → κ → Bool) (query : κ) :
    lookup? ltb query (.nil : BinaryTree (κ × ν)) = none := rfl

theorem lookup?_node (ltb : κ → κ → Bool) (query : κ) (binding : κ × ν)
    (left right : BinaryTree (κ × ν)) :
    lookup? ltb query (.node binding left right) =
      if ltb query binding.1 then lookup? ltb query left
      else if ltb binding.1 query then lookup? ltb query right
      else some binding.2 := rfl

@[simp] theorem lookup_empty (ltb : κ → κ → Bool) (default : ν) (query : κ) :
    lookup ltb default query .nil = default := rfl

theorem lookup_node (ltb : κ → κ → Bool) (default : ν) (query : κ) (binding : κ × ν)
    (left right : BinaryTree (κ × ν)) :
    lookup ltb default query (.node binding left right) =
      if ltb query binding.1 then lookup ltb default query left
      else if ltb binding.1 query then lookup ltb default query right
      else binding.2 := by
  unfold lookup
  rw [lookup?_node]
  split
  · rfl
  · split <;> rfl

@[simp] theorem insert_empty (ltb : κ → κ → Bool) (key : κ) (value : ν) :
    insert ltb key value .nil = .node (key, value) .nil .nil := rfl

theorem insert_node (ltb : κ → κ → Bool) (key : κ) (value : ν) (binding : κ × ν)
    (left right : BinaryTree (κ × ν)) :
    insert ltb key value (.node binding left right) =
      if ltb key binding.1 then .node binding (insert ltb key value left) right
      else if ltb binding.1 key then .node binding left (insert ltb key value right)
      else .node (key, value) left right := rfl

@[simp] theorem kvsInsert_empty (ltb : κ → κ → Bool) (key : κ) (value : ν) :
    kvsInsert ltb key value [] = [(key, value)] := rfl

theorem kvsInsert_cons (ltb : κ → κ → Bool) (key : κ) (value : ν)
    (binding : κ × ν) (rest : List (κ × ν)) :
    kvsInsert ltb key value (binding :: rest) =
      if ltb key binding.1 then (key, value) :: binding :: rest
      else if ltb binding.1 key then binding :: kvsInsert ltb key value rest
      else (key, value) :: rest := rfl

theorem lookup?_insert_self_of_irrefl (ltb : κ → κ → Bool)
    (irrefl : ∀ key : κ, ltb key key = false) (key : κ) (value : ν)
    (t : BinaryTree (κ × ν)) :
    lookup? ltb key (insert ltb key value t) = some value := by
  exact @Search.OrderedMap.lookup_bind_self_of_irrefl κ ν
    (booleanOrder ltb) (booleanDecision ltb)
    (fun key => by change ¬ ltb key key = true; simp [irrefl key]) key value t

theorem lookup_insert_self_of_irrefl (ltb : κ → κ → Bool)
    (irrefl : ∀ key : κ, ltb key key = false) (default : ν) (key : κ) (value : ν)
    (t : BinaryTree (κ × ν)) :
    lookup ltb default key (insert ltb key value t) = value :=
  congrArg (fun result => result.getD default)
    (lookup?_insert_self_of_irrefl ltb irrefl key value t)

theorem all_insert (ltb : κ → κ → Bool) {P : κ × ν → Prop}
    {t : BinaryTree (κ × ν)} (all : All P t) (key : κ) (value : ν)
    (new : P (key, value)) : All P (insert ltb key value t) :=
  @Search.OrderedMap.all_bind κ ν (booleanOrder ltb) (booleanDecision ltb)
    P t all key value new

@[simp] theorem bound_empty (ltb : κ → κ → Bool) (query : κ) :
    bound ltb query (.nil : BinaryTree (κ × ν)) = false := rfl

theorem bound_default (ltb : κ → κ → Bool) (default : ν) (query : κ)
    (t : BinaryTree (κ × ν)) (absent : bound ltb query t = false) :
    lookup ltb default query t = default := by
  cases found : lookup? ltb query t with
  | none => simp [lookup, found]
  | some value => simp [bound, found] at absent

/-- The same witness works for every caller default, in this quantifier order. -/
theorem bound_value (ltb : κ → κ → Bool) (query : κ) (t : BinaryTree (κ × ν))
    (present : bound ltb query t = true) :
    ∃ value : ν, ∀ default : ν, lookup ltb default query t = value := by
  cases found : lookup? ltb query t with
  | none => simp [bound, found] at present
  | some value => exact ⟨value, fun _ => by simp [lookup, found]⟩

section OperationCongruence
variable [LT κ] [DecidableLT κ]

theorem lookup?_eq_lookup (ltb : κ → κ → Bool)
    (compatible : ∀ a b, ltb a b = true ↔ a < b)
    (query : κ) (t : BinaryTree (κ × ν)) :
    lookup? ltb query t = Search.OrderedMap.lookup query t := by
  induction t with
  | nil => rfl
  | node binding left right ihl ihr =>
      simp only [lookup?_node, Search.OrderedMap.lookup, compatible, ihl, ihr]

theorem insert_eq_bind (ltb : κ → κ → Bool)
    (compatible : ∀ a b, ltb a b = true ↔ a < b)
    (key : κ) (value : ν) (t : BinaryTree (κ × ν)) :
    insert ltb key value t = Search.OrderedMap.bind key value t := by
  induction t with
  | nil => rfl
  | node binding left right ihl ihr =>
      simp only [insert_node, Search.OrderedMap.bind, compatible, ihl, ihr]

theorem kvsInsert_eq_ordered (ltb : κ → κ → Bool)
    (compatible : ∀ a b, ltb a b = true ↔ a < b)
    (key : κ) (value : ν) (bindings : List (κ × ν)) :
    kvsInsert ltb key value bindings = Search.OrderedMap.kvsInsert key value bindings := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      simp only [kvsInsert_cons, Search.OrderedMap.kvsInsert, compatible, ih]

end OperationCongruence

section StrictReflection
variable (decode : κ → Int) (ltb : κ → κ → Bool)
variable (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
include hlt

theorem lookup?_decode (query : κ) (t : BinaryTree (κ × ν)) :
    Search.OrderedMap.lookup (decode query) (mapKeys decode t) = lookup? ltb query t :=
  @lookup_mapKeys κ ν (booleanOrder ltb) (booleanDecision ltb) decode hlt query t

theorem lookup_decode (default : ν) (query : κ) (t : BinaryTree (κ × ν)) :
    (Search.OrderedMap.lookup (decode query) (mapKeys decode t)).getD default =
      lookup ltb default query t :=
  congrArg (fun result => result.getD default) (lookup?_decode decode ltb hlt query t)

theorem mapKeys_insert (key : κ) (value : ν) (t : BinaryTree (κ × ν)) :
    mapKeys decode (insert ltb key value t) =
      Search.OrderedMap.bind (decode key) value (mapKeys decode t) :=
  @mapKeys_bind κ ν (booleanOrder ltb) (booleanDecision ltb) decode hlt key value t

theorem lookup?_insert_eq (key : κ) (value : ν) (t : BinaryTree (κ × ν)) :
    lookup? ltb key (insert ltb key value t) = some value := by
  apply lookup?_insert_self_of_irrefl ltb
  intro same
  apply Bool.eq_false_iff.mpr
  intro comparison
  exact (lt_irrefl (decode same)) ((hlt same same).mp comparison)

theorem lookup_insert_eq (default : ν) (key : κ) (value : ν)
    (t : BinaryTree (κ × ν)) :
    lookup ltb default key (insert ltb key value t) = value :=
  congrArg (fun result => result.getD default)
    (lookup?_insert_eq decode ltb hlt key value t)

theorem bound_insert_eq (key : κ) (value : ν) (t : BinaryTree (κ × ν)) :
    bound ltb key (insert ltb key value t) = true :=
  congrArg Option.isSome (lookup?_insert_eq decode ltb hlt key value t)

theorem bst_insert {t : BinaryTree (κ × ν)} (valid : BST decode t)
    (key : κ) (value : ν) : BST decode (insert ltb key value t) := by
  apply (bst_iff_mapKeys decode _).mpr
  rw [mapKeys_insert decode ltb hlt]
  exact Search.OrderedMap.ordered_bind ((bst_iff_mapKeys decode t).mp valid)
    (decode key) value

end StrictReflection

/-- A direct use of the public suffix identity, independent of comparison. -/
theorem arbitrary_suffix_client (key : κ) (value : ν) (suffix : List (κ × ν)) :
    elementsAux (.node (key, value) .nil .nil) suffix = (key, value) :: suffix := rfl

/-- Distinct original keys can collide without decoder injectivity. -/
theorem colliding_keys_counterexample :
    lookup (fun _ _ : Bool => false) 0 false
        (insert (fun _ _ : Bool => false) true 2
          (insert (fun _ _ : Bool => false) false 1 .nil)) = 2 ∧
      lookup (fun _ _ : Bool => false) 0 false
        (insert (fun _ _ : Bool => false) false 1 .nil) = 1 := by
  constructor <;> rfl

theorem colliding_decode_reflects (a b : Bool) :
    (fun _ _ : Bool => false) a b = true ↔
      (fun _ : Bool => (0 : Int)) a < (fun _ : Bool => (0 : Int)) b := by
  simp

/-- The weak map equation still applies when original keys collide. -/
theorem colliding_decode_map (key : Bool) (value : ν) (t : BinaryTree (Bool × ν)) :
    mapKeys (fun _ : Bool => (0 : Int)) (insert (fun _ _ : Bool => false) key value t) =
      Search.OrderedMap.bind 0 value (mapKeys (fun _ : Bool => (0 : Int)) t) :=
  mapKeys_insert (fun _ : Bool => (0 : Int)) (fun _ _ : Bool => false)
    colliding_decode_reflects key value t

end Search.OrderedMap.DecodedKeys
