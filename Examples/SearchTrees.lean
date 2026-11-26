import Applications.Search.OrderedMap.Enumeration
import Applications.Search.OrderedMap.SourceModel
import Applications.Search.OrderedMap.TotalTable
import Examples.FunctionalMaps
import Examples.InsertionSorting

/-!
# VFA SearchTree: raw operations, enumeration and two abstractions

The source tree is the shared `BinaryTree` of key/value pairs. Raw directed
search and insertion satisfy update laws even on malformed trees. Enumeration
soundness and the independent whole-tree abstractions require the full strict
separator invariant. Default lookup, presence, list contents and raw tree shape
remain different observations.

Source: VFA 2.1 `SearchTree.v`, all 90 records and 35 exercises, including the
optional and advanced exercises. The single correspondence ledger is
`docs/research/vfa-coverage.md`; source MIT notice is in `docs/licenses/vfa-MIT.txt`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SearchTrees
open Search
universe u v
variable {V : Type u}

abbrev Key := Nat
abbrev Tree (V : Type u) := BinaryTree (Key × V)

def nil : Tree V := .nil
def node (left : Tree V) (k : Key) (value : V) (right : Tree V) : Tree V :=
  .node (k, value) left right

def emptyTree : Tree V := nil
def bound (k : Key) (t : Tree V) : Bool := (OrderedMap.lookup k t).isSome
def lookup (default : V) (k : Key) (t : Tree V) : V :=
  (OrderedMap.lookup k t).getD default
abbrev insert (k : Key) (value : V) (t : Tree V) : Tree V := OrderedMap.bind k value t

theorem bound_empty (k : Key) : bound k (emptyTree : Tree V) = false := rfl

theorem bound_node (k x : Key) (left right : Tree V) (value : V) :
    bound k (node left x value right) =
      if k < x then bound k left else if x < k then bound k right else true := by
  simp only [bound, node, OrderedMap.lookup]
  split
  · rfl
  · split <;> rfl

theorem lookup_node (default : V) (k x : Key) (left right : Tree V) (value : V) :
    lookup default k (node left x value right) =
      if k < x then lookup default k left
      else if x < k then lookup default k right else value := by
  simp only [lookup, node, OrderedMap.lookup]
  split
  · rfl
  · split <;> rfl

theorem insert_empty (k : Key) (value : V) :
    insert k value emptyTree = node nil k value nil := rfl

theorem insert_node (k x : Key) (value old : V) (left right : Tree V) :
    insert k value (node left x old right) =
      if k < x then node (insert k value left) x old right
      else if x < k then node left x old (insert k value right)
      else node left k value right := rfl

def exampleTree : Tree String := node (node nil 2 "two" nil) 4 "four" (node nil 5 "five" nil)

theorem insert_exampleTree :
    insert 5 "five" (insert 2 "two" (insert 4 "four" emptyTree)) = exampleTree := rfl

theorem lookup_exampleTree_present : lookup "" 5 exampleTree = "five" := rfl
theorem lookup_exampleTree_absent : lookup "" 3 exampleTree = "" := rfl
theorem bound_exampleTree_absent : bound 3 exampleTree = false := rfl

namespace Malformed
def exampleTree : Tree String := node (node nil 5 "five" nil) 4 "four" (node nil 2 "two" nil)
theorem lookup_hidden_key_misses : lookup "" 2 exampleTree ≠ "two" := by decide
end Malformed

abbrev ForallT (P : Key → V → Prop) (t : Tree V) : Prop :=
  OrderedTree.All (fun binding => P binding.1 binding.2) t
abbrev BST (t : Tree V) : Prop := OrderedTree.OrderedBy Prod.fst t

theorem forallT_node (P : Key → V → Prop) (left right : Tree V) (k : Key) (value : V) :
    ForallT P (node left k value right) ↔
      P k value ∧ ForallT P left ∧ ForallT P right := Iff.rfl

/-- The shared recursive invariant supplies the source constructor interface. -/
theorem bst_node (left right : Tree V) (k : Key) (value : V) :
    BST (node left k value right) ↔
      ForallT (fun q _ => q < k) left ∧ ForallT (fun q _ => k < q) right ∧
        BST left ∧ BST right := by
  simp only [BST, node, OrderedTree.OrderedBy, ForallT]
  tauto

/-- Induction on valid trees retains both all-descendant separator premises. -/
theorem bst_induction (P : Tree V → Prop) (base : P nil)
    (step : ∀ (left : Tree V) (k : Key) (value : V) (right : Tree V),
      ForallT (fun q _ => q < k) left → ForallT (fun q _ => k < q) right →
      BST left → BST right → P left → P right → P (node left k value right))
    (t : Tree V) (valid : BST t) : P t := by
  induction t with
  | nil => exact base
  | node binding left right ihl ihr =>
      exact step left binding.1 binding.2 right valid.2.2.1 valid.2.2.2
        valid.1 valid.2.1 (ihl valid.1) (ihr valid.2.1)

theorem bst_exampleTree : BST exampleTree := by
  norm_num [exampleTree, node, nil, BST, OrderedTree.OrderedBy, OrderedTree.All]
theorem Malformed.not_bst_exampleTree : ¬ BST Malformed.exampleTree := by
  norm_num [Malformed.exampleTree, node, nil, BST, OrderedTree.OrderedBy, OrderedTree.All]
theorem bst_emptyTree (V : Type u) : BST (emptyTree : Tree V) := trivial

theorem forallT_insert (P : Key → V → Prop) (t : Tree V) (all : ForallT P t)
    (k : Key) (value : V) (new : P k value) : ForallT P (insert k value t) :=
  OrderedMap.all_bind all k value new

theorem bst_insert (k : Key) (value : V) (t : Tree V) (valid : BST t) :
    BST (insert k value t) := OrderedMap.ordered_bind valid k value

theorem lookup_empty (V : Type u) (default : V) (k : Key) :
    lookup default k emptyTree = default := rfl

theorem lookup_insert (t : Tree V) (default : V) (k query : Key) (value : V) :
    lookup default query (insert k value t) =
      if query = k then value else lookup default query t := by
  simp only [lookup, insert, OrderedMap.lookup_bind]
  split <;> rfl

theorem lookup_insert_eq (t : Tree V) (default : V) (k : Key) (value : V) :
    lookup default k (insert k value t) = value := by
  simp [lookup_insert]

theorem lookup_insert_neq (t : Tree V) (default : V) (k query : Key) (value : V)
    (different : k ≠ query) :
    lookup default query (insert k value t) = lookup default query t := by
  rw [lookup_insert, ite_eq_right (Ne.symm different)]

theorem bound_insert_eq (t : Tree V) (k : Key) (value : V) :
    bound k (insert k value t) = true := by
  simp [bound, insert, OrderedMap.lookup_bind]

theorem bound_insert_neq (t : Tree V) (k query : Key) (value : V)
    (different : k ≠ query) : bound query (insert k value t) = bound query t := by
  simp only [bound, insert, OrderedMap.lookup_bind, ite_eq_right (Ne.symm different)]

theorem bound_default (k : Key) (default : V) (t : Tree V)
    (absent : bound k t = false) : lookup default k t = default := by
  cases found : OrderedMap.lookup k t with
  | none => simp [lookup, found]
  | some value => simp [bound, found] at absent

/-- These clients use the public raw laws and require no invariant. -/
theorem lookup_insert_shadow (t : Tree V) (value old default : V) (k query : Key) :
    lookup default query (insert k value (insert k old t)) =
      lookup default query (insert k value t) := by
  by_cases same : query = k <;> simp [lookup_insert, same]

theorem lookup_insert_same (k query : Key) (default : V) (t : Tree V) :
    lookup default query (insert k (lookup default k t) t) = lookup default query t := by
  by_cases same : query = k <;> simp [lookup_insert, same]

theorem lookup_insert_permute (value1 value2 default : V) (k1 k2 query : Key)
    (t : Tree V) (different : k1 ≠ k2) :
    lookup default query (insert k1 value1 (insert k2 value2 t)) =
      lookup default query (insert k2 value2 (insert k1 value1 t)) := by
  by_cases first : query = k1
  · subst query
    simp [lookup_insert, different]
  · by_cases second : query = k2
    · subst query
      simp [lookup_insert, Ne.symm different]
    · simp [lookup_insert, first, second]

theorem insert_shadow_equality (t : Tree V) (k : Key) (value old : V) :
    insert k value (insert k old t) = insert k value t :=
  OrderedMap.bind_shadow k old value t

/-- A missing key can acquire an explicit default-valued binding. -/
theorem insert_same_equality_breaks :
    ∃ (V : Type u) (default : V) (t : Tree V) (k : Key),
      insert k (lookup default k t) t ≠ t := by
  refine ⟨ULift.{u} Unit, ⟨()⟩, nil, 0, ?_⟩
  simp [insert, lookup, nil, OrderedMap.lookup, OrderedMap.bind]

/-- Opposite insertion orders give different roots even with equal payloads. -/
theorem insert_permute_equality_breaks :
    ∃ (V : Type u) (value1 value2 : V) (k1 k2 : Key) (t : Tree V),
      k1 ≠ k2 ∧ insert k1 value1 (insert k2 value2 t) ≠
        insert k2 value2 (insert k1 value1 t) := by
  refine ⟨ULift.{u} Unit, ⟨()⟩, ⟨()⟩, 0, 1, nil, by decide, ?_⟩
  simp [insert, nil, OrderedMap.bind]

abbrev elements (t : Tree V) : List (Key × V) := OrderedTree.entries t

theorem elements_node (left right : Tree V) (k : Key) (value : V) :
    elements (node left k value right) = elements left ++ ([(k, value)] ++ elements right) := rfl

theorem elements_exampleTree : elements exampleTree = [(2, "two"), (4, "four"), (5, "five")] := rfl

def DefaultLookupImpliesMembership : Prop :=
  ∀ (V : Type u) (k : Key) (value default : V) (t : Tree V),
    BST t → lookup default k t = value → (k, value) ∈ elements t

/-- The source's aborted specification already fails on the empty valid tree. -/
theorem not_defaultLookupImpliesMembership : ¬ DefaultLookupImpliesMembership.{u} := by
  intro claimed
  have impossible := claimed (ULift.{u} Unit) 0 ⟨()⟩ ⟨()⟩ nil trivial rfl
  exact List.not_mem_nil impossible

def ElementsComplete : Prop :=
  ∀ (V : Type u) (k : Key) (value default : V) (t : Tree V),
    bound k t = true → lookup default k t = value → (k, value) ∈ elements t

theorem elements_complete : ElementsComplete.{u} := by
  intro V k value default t present returned
  have found : OrderedMap.lookup k t = some value :=
    (OrderedMap.binding_iff default (OrderedMap.pathObserve t) k value).mpr ⟨present, returned⟩
  exact (OrderedTree.contains_iff_mem_entries _ _).mp (OrderedMap.lookup_some_contains found)

def ElementsCorrect : Prop :=
  ∀ (V : Type u) (k : Key) (value default : V) (t : Tree V),
    BST t → (k, value) ∈ elements t → bound k t = true ∧ lookup default k t = value

theorem elements_preserves_forall (P : Key → V → Prop) (t : Tree V)
    (all : ForallT P t) : ∀ binding ∈ elements t, P binding.1 binding.2 := by
  intro binding member
  exact all.of_contains ((OrderedTree.contains_iff_mem_entries _ _).mpr member)

theorem elements_preserves_relation (k other : Key) (value : V) (t : Tree V)
    (R : Key → Key → Prop) (all : ForallT (fun q _ => R q other) t)
    (member : (k, value) ∈ elements t) : R k other :=
  elements_preserves_forall (fun q _ => R q other) t all (k, value) member

theorem bound_value (k : Key) (t : Tree V) (present : bound k t = true) :
    ∃ value, ∀ default, lookup default k t = value := by
  cases found : OrderedMap.lookup k t with
  | none => simp [bound, found] at present
  | some value => exact ⟨value, fun default => by simp [lookup, found]⟩

theorem elements_correct_inverse (k : Key) (t : Tree V)
    (absent : ∀ value, (k, value) ∉ elements t) : bound k t = false := by
  cases present : bound k t with
  | false => rfl
  | true =>
      obtain ⟨value, returned⟩ := bound_value k t present
      exact False.elim (absent value (elements_complete V k value value t present (returned value)))

theorem elements_correct : ElementsCorrect.{u} := by
  intro V k value default t valid member
  have found := (OrderedMap.lookup_eq_some_iff_mem_entries valid k value).mpr member
  exact (OrderedMap.binding_iff default (OrderedMap.pathObserve t) k value).mp found

theorem elements_complete_inverse (k : Key) (value : V) (t : Tree V)
    (valid : BST t) (absent : bound k t = false) : (k, value) ∉ elements t := by
  intro member
  have present := (elements_correct V k value value t valid member).1
  simp only [absent, Bool.false_eq_true] at present

theorem sorted_app (left right : List Nat) (pivot : Nat)
    (hl : InsertionSorting.Sorted left) (hr : InsertionSorting.Sorted right)
    (lesser : ∀ n ∈ left, n < pivot) (greater : ∀ n ∈ right, pivot < n) :
    InsertionSorting.Sorted (left ++ pivot :: right) := by
  apply List.isChain_iff_pairwise.mpr
  refine List.pairwise_append.mpr ⟨List.isChain_iff_pairwise.mp hl,
    List.pairwise_cons.mpr ⟨fun n member => Nat.le_of_lt (greater n member),
      List.isChain_iff_pairwise.mp hr⟩, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.mp hb with same | member
  · simpa only [same] using Nat.le_of_lt (lesser a ha)
  · exact Nat.le_of_lt (Nat.lt_trans (lesser a ha) (greater b member))

def listKeys (bindings : List (Key × V)) : List Key := bindings.map Prod.fst

theorem sorted_elements (t : Tree V) (valid : BST t) :
    InsertionSorting.Sorted (listKeys (elements t)) :=
  List.isChain_iff_pairwise.mpr
    ((OrderedMap.ordered_entries_keys_pairwise valid).imp fun h => Nat.le_of_lt h)

def Disjoint {X : Type u} (left right : List X) : Prop :=
  ∀ x, x ∈ left → x ∉ right

theorem nodup_append {X : Type u} (left right : List X)
    (hl : left.Nodup) (hr : right.Nodup) (apart : Disjoint left right) :
    (left ++ right).Nodup := hl.append hr (fun x hx => apart x hx)

theorem elements_nodup_keys (t : Tree V) (valid : BST t) :
    (listKeys (elements t)).Nodup := OrderedMap.ordered_entries_keys_nodup valid

abbrev fastElementsAcc (t : Tree V) (suffix : List (Key × V)) : List (Key × V) :=
  OrderedMap.fastEntriesAcc t suffix
abbrev fastElements (t : Tree V) : List (Key × V) := OrderedMap.fastEntries t

theorem fastElementsAcc_node (left right : Tree V) (k : Key) (value : V)
    (suffix : List (Key × V)) :
    fastElementsAcc (node left k value right) suffix =
      fastElementsAcc left ((k, value) :: fastElementsAcc right suffix) := rfl

theorem fastElementsAcc_eq_append (t : Tree V) (suffix : List (Key × V)) :
    fastElementsAcc t suffix = elements t ++ suffix := OrderedMap.fastEntriesAcc_eq t suffix

theorem fastElements_eq_elements (t : Tree V) : fastElements t = elements t :=
  OrderedMap.fastEntries_eq t

/-- Correctness is transported through the public value equality. -/
theorem fastElements_correct (k : Key) (value default : V) (t : Tree V)
    (valid : BST t) (member : (k, value) ∈ fastElements t) :
    bound k t = true ∧ lookup default k t = value := by
  rw [fastElements_eq_elements] at member
  exact elements_correct V k value default t valid member

theorem fastElements_sorted (t : Tree V) (valid : BST t) :
    InsertionSorting.Sorted (listKeys (fastElements t)) := by
  rw [fastElements_eq_elements]
  exact sorted_elements t valid

theorem fast_nonempty_accumulator :
    fastElementsAcc exampleTree [(9, "tail")] =
      [(2, "two"), (4, "four"), (5, "five"), (9, "tail")] := by
  rw [fastElementsAcc_eq_append, elements_exampleTree]
  rfl

theorem elements_empty (V : Type u) : elements (emptyTree : Tree V) = [] := rfl

abbrev kvsInsert (k : Key) (value : V) (bindings : List (Key × V)) :=
  OrderedMap.kvsInsert k value bindings

theorem kvsInsert_split (value old : V) (left right : List (Key × V)) (k pivot : Key)
    (hl : ∀ binding ∈ left, binding.1 < pivot)
    (hr : ∀ binding ∈ right, pivot < binding.1) :
    kvsInsert k value (left ++ (pivot, old) :: right) =
      if k < pivot then kvsInsert k value left ++ (pivot, old) :: right
      else if pivot < k then left ++ (pivot, old) :: kvsInsert k value right
      else left ++ (k, value) :: right :=
  OrderedMap.kvsInsert_split k value pivot old left right hl hr

/-- The common split law applies even when the right suffix has no ordering invariant. -/
theorem kvsInsert_arbitrary_right (right : List (Key × V)) (value old small : V) :
    kvsInsert 7 value ((1, small) :: (5, old) :: right) =
      (1, small) :: (5, old) :: kvsInsert 7 value right := by
  simpa using OrderedMap.kvsInsert_split_of_left
    7 value 5 old [(1, small)] right (by simp)

/-- An unsorted, duplicate-bearing suffix violates the old extra premise but still splits. -/
theorem kvsInsert_arbitrary_right_witness :
    ¬ (∀ binding ∈ ([(0, 20), (5, 60), (0, 30)] : List (Key × Nat)), 5 < binding.1) ∧
      kvsInsert 7 70 [(1, 10), (5, 50), (0, 20), (5, 60), (0, 30)] =
        [(1, 10), (5, 50), (0, 20), (5, 60), (0, 30), (7, 70)] := by
  refine ⟨by decide, ?_⟩
  exact kvsInsert_arbitrary_right [(0, 20), (5, 60), (0, 30)] 70 50 10

/-- Dropping the left separator changes where the actual insertion stops. -/
theorem kvsInsert_left_separator_needed :
    kvsInsert 7 70 ([(9, 90)] ++ (5, 50) :: []) ≠
      [(9, 90)] ++ (5, 50) :: kvsInsert 7 70 [] := by decide

theorem kvsInsert_elements (t : Tree V) (valid : BST t) (k : Key) (value : V) :
    elements (insert k value t) = kvsInsert k value (elements t) :=
  OrderedMap.entries_bind valid k value

/-- An unreachable misplaced binding does not invalidate raw update algebra. -/
theorem malformed_update_still_observed : lookup "" 2 (insert 2 "new" Malformed.exampleTree) = "new" :=
  lookup_insert_eq Malformed.exampleTree "" 2 "new"

theorem explicit_default_and_absence :
    (∀ k, lookup false k (node nil 0 false nil) = lookup false k nil) ∧
      bound 0 (node nil 0 false nil) = true ∧ bound 0 (nil : Tree Bool) = false ∧
      elements (node nil 0 false nil) ≠ elements (nil : Tree Bool) := by
  refine ⟨?_, rfl, rfl, by decide⟩
  intro k
  change lookup false k (insert 0 false (nil : Tree Bool)) = lookup false k nil
  exact lookup_insert_same 0 k false nil

theorem bound_default_converse_fails :
    lookup false 0 (node nil 0 false nil) = false ∧ bound 0 (node nil 0 false nil) ≠ false := by
  exact ⟨rfl, by decide⟩

theorem key_zero_replacement (first last : V) :
    insert 0 last (insert 0 first emptyTree) = node nil 0 last nil := by
  rw [insert_shadow_equality]
  rfl

/-- The payload can itself be a function; no payload order or equality is used. -/
theorem function_payload (f : Unit → Nat) (t : Tree (Unit → Nat)) :
    lookup (fun _ => 0) 0 (insert 0 f t) = f := lookup_insert_eq t (fun _ => 0) 0 f

/-! ## The enumeration abstraction and its exact source specializations -/

abbrev mapOfList (bindings : List (Key × V)) : FunctionalMaps.PartialMap V :=
  OrderedMap.listObserve bindings
abbrev enumerationMeaning (t : Tree V) : FunctionalMaps.PartialMap V := OrderedMap.SourceModel.enumAbs t
abbrev find (default : V) (k : Key) (m : FunctionalMaps.PartialMap V) :=
  OrderedMap.withDefault default m k
abbrev mapBound (k : Key) (m : FunctionalMaps.PartialMap V) := OrderedMap.hasBinding m k

theorem mapOfList_empty : mapOfList ([] : List (Key × V)) = FunctionalMaps.empty := rfl

theorem mapOfList_cons (k : Key) (value : V) (rest : List (Key × V)) :
    mapOfList ((k, value) :: rest) = FunctionalMaps.update (mapOfList rest) k value := by
  rw [FunctionalMaps.update_eq_write]
  exact OrderedMap.SourceModel.listObserve_cons (k, value) rest

theorem in_fst {X : Type u} {Y : Type v} (bindings : List (X × Y)) (x : X) (y : Y)
    (member : (x, y) ∈ bindings) : x ∈ bindings.map Prod.fst :=
  OrderedMap.SourceModel.in_keys_of_mem member

theorem mapOfList_eq_some_of_mem (bindings : List (Key × V)) (k : Key) (value : V)
    (unique : (listKeys bindings).Nodup) (member : (k, value) ∈ bindings) :
    mapOfList bindings k = some value :=
  OrderedMap.SourceModel.listObserve_eq_some_of_mem unique member

theorem mapOfList_eq_none_of_not_mem (bindings : List (Key × V)) (k : Key)
    (absent : k ∉ listKeys bindings) : mapOfList bindings k = none :=
  OrderedMap.SourceModel.listObserve_none_of_not_mem absent

theorem enumerationMeaning_empty (V : Type u) : enumerationMeaning (emptyTree : Tree V) = FunctionalMaps.empty := rfl

theorem enumerationMeaning_bound (t : Tree V) (k : Key) (valid : BST t) :
    mapBound k (enumerationMeaning t) = bound k t := OrderedMap.SourceModel.enumAbs_bound valid k

theorem enumerationMeaning_lookup (t : Tree V) (default : V) (k : Key) (valid : BST t) :
    find default k (enumerationMeaning t) = lookup default k t :=
  OrderedMap.SourceModel.enumAbs_default valid default k

theorem enumerationMeaning_insert (t : Tree V) (k : Key) (value : V) (valid : BST t) :
    enumerationMeaning (insert k value t) = FunctionalMaps.update (enumerationMeaning t) k value := by
  rw [FunctionalMaps.update_eq_write]
  exact OrderedMap.SourceModel.enumAbs_bind valid k value

theorem mapOfList_elements (t : Tree V) (_valid : BST t) : mapOfList (elements t) = enumerationMeaning t := rfl

/-! ## The independent structural abstraction -/

abbrev collisionUnion (left right : FunctionalMaps.PartialMap V) : FunctionalMaps.PartialMap V :=
  OrderedMap.SourceModel.collisionUnion left right

theorem collisionUnion_left (left right : FunctionalMaps.PartialMap V) (k : Key)
    (absent : right k = none) : collisionUnion left right k = left k :=
  OrderedMap.SourceModel.collisionUnion_left left right k absent

theorem collisionUnion_right (left right : FunctionalMaps.PartialMap V) (k : Key)
    (absent : left k = none) : collisionUnion left right k = right k :=
  OrderedMap.SourceModel.collisionUnion_right left right k absent

theorem collisionUnion_both (left right : FunctionalMaps.PartialMap V) (k : Key) (a b : V)
    (hl : left k = some a) (hr : right k = some b) : collisionUnion left right k = none :=
  OrderedMap.SourceModel.collisionUnion_both left right k a b hl hr

theorem collisionUnion_update_right (left right : FunctionalMaps.PartialMap V) (k : Key) (value : V)
    (absent : left k = none) :
    FunctionalMaps.update (collisionUnion left right) k value =
      collisionUnion left (FunctionalMaps.update right k value) := by
  simp only [FunctionalMaps.update_eq_write]
  exact OrderedMap.SourceModel.collisionUnion_write_right left right k value absent

theorem collisionUnion_update_left (left right : FunctionalMaps.PartialMap V) (k : Key) (value : V)
    (absent : right k = none) :
    FunctionalMaps.update (collisionUnion left right) k value =
      collisionUnion (FunctionalMaps.update left k value) right := by
  simp only [FunctionalMaps.update_eq_write]
  exact OrderedMap.SourceModel.collisionUnion_write_left left right k value absent

abbrev mapOfTree (t : Tree V) : FunctionalMaps.PartialMap V := OrderedMap.SourceModel.mapOfTree t
abbrev structuralMeaning (t : Tree V) : FunctionalMaps.PartialMap V := mapOfTree t

theorem mapOfTree_node (left right : Tree V) (k : Key) (value : V) :
    mapOfTree (node left k value right) =
      FunctionalMaps.update (collisionUnion (mapOfTree left) (mapOfTree right)) k value := by
  rw [FunctionalMaps.update_eq_write]
  rfl

theorem mapOfTree_prop (P : Key → V → Prop) (t : Tree V) (all : ForallT P t)
    (k : Key) (value : V) (found : mapOfTree t k = some value) : P k value :=
  OrderedMap.SourceModel.mapOfTree_prop all k value found

theorem structuralMeaning_empty (V : Type u) : structuralMeaning (emptyTree : Tree V) = FunctionalMaps.empty := rfl

theorem structuralMeaning_bound (t : Tree V) (k : Key) (valid : BST t) :
    mapBound k (structuralMeaning t) = bound k t := OrderedMap.SourceModel.mapOfTree_bound valid k

theorem structuralMeaning_lookup (default : V) (t : Tree V) (k : Key) (valid : BST t) :
    find default k (structuralMeaning t) = lookup default k t :=
  OrderedMap.SourceModel.mapOfTree_default valid default k

theorem structuralMeaning_insert (k : Key) (value : V) (t : Tree V) (valid : BST t) :
    structuralMeaning (insert k value t) = FunctionalMaps.update (structuralMeaning t) k value := by
  rw [FunctionalMaps.update_eq_write]
  exact OrderedMap.SourceModel.mapOfTree_bind valid k value

theorem mapOfList_append (left right : List (Key × V))
    (apart : Disjoint (listKeys left) (listKeys right)) :
    mapOfList (left ++ right) = collisionUnion (mapOfList left) (mapOfList right) :=
  OrderedMap.SourceModel.listObserve_append_of_disjoint left right (fun k hk => apart k hk)

theorem mapOfList_elements_eq_structuralMeaning (t : Tree V) (valid : BST t) : mapOfList (elements t) = structuralMeaning t :=
  OrderedMap.SourceModel.enumAbs_eq_mapOfTree valid

theorem abstractions_agree (t : Tree V) (valid : BST t) : enumerationMeaning t = structuralMeaning t :=
  OrderedMap.SourceModel.enumAbs_eq_mapOfTree valid

theorem canonical_enumeration (left right : Tree V) (hl : BST left) (hr : BST right)
    (same : enumerationMeaning left = enumerationMeaning right) : elements left = elements right :=
  OrderedMap.SourceModel.entries_eq_of_enumAbs_eq hl hr same

theorem enumerated_finite_support (t : Tree V) :
    ∃ keys : List Key, ∀ k value, enumerationMeaning t k = some value → k ∈ keys :=
  OrderedMap.SourceModel.enumAbs_finite_support t

theorem structural_finite_support (t : Tree V) :
    ∃ keys : List Key, ∀ k value, structuralMeaning t k = some value → k ∈ keys :=
  OrderedMap.SourceModel.mapOfTree_finite_support t

/-! ## Separating clients of the two abstractions -/

theorem duplicate_member_is_shadowed :
    (0, "second") ∈ [(0, "first"), (0, "second")] ∧
      mapOfList [(0, "first"), (0, "second")] 0 = some "first" ∧
      mapOfList [(0, "first"), (0, "second")] 0 ≠ some "second" := by
  exact ⟨by simp, rfl, by decide⟩

def collisionTree : Tree String := node (node nil 0 "left" nil) 1 "root" (node nil 0 "right" nil)

theorem raw_abstractions_disagree :
    enumerationMeaning collisionTree 0 = some "left" ∧ structuralMeaning collisionTree 0 = none := ⟨rfl, rfl⟩

theorem not_bst_collisionTree : ¬ BST collisionTree := by
  norm_num [collisionTree, node, nil, BST, OrderedTree.OrderedBy, OrderedTree.All]

theorem collisionUnion_cases (value : V) :
    collisionUnion (fun _ => none) (fun _ => none) 0 = (none : Option V) ∧
      collisionUnion (fun _ => some value) (fun _ => none) 0 = some value ∧
      collisionUnion (fun _ => none) (fun _ => some value) 0 = some value ∧
      collisionUnion (fun _ => some value) (fun _ => some value) 0 = none := ⟨rfl, rfl, rfl, rfl⟩

/-- Absence of the other operand at the write key is a necessary premise. -/
theorem collisionUnion_update_without_absence_fails :
    FunctionalMaps.update
        (collisionUnion (FunctionalMaps.update FunctionalMaps.empty 0 "old") FunctionalMaps.empty)
        0 "new" ≠
      collisionUnion (FunctionalMaps.update FunctionalMaps.empty 0 "old")
        (FunctionalMaps.update FunctionalMaps.empty 0 "new") := by
  intro same
  have impossible : (some "new" : Option String) = none := congrFun same 0
  cases impossible

theorem collisionUnion_not_associative :
    collisionUnion (collisionUnion (fun _ => some (1 : Nat)) (fun _ => some 2)) (fun _ => some 3) ≠
      collisionUnion (fun _ => some (1 : Nat)) (collisionUnion (fun _ => some 2) (fun _ => some 3)) := by
  intro same
  have impossible : (some 3 : Option Nat) = some 1 := congrFun same 0
  cases impossible

/-- Repetition inside one operand is permitted by the disjoint-domain law. -/
theorem disjoint_append_with_internal_duplicates :
    mapOfList ([(0, "first"), (0, "shadowed")] ++ [(1, "right")]) =
      collisionUnion (mapOfList [(0, "first"), (0, "shadowed")]) (mapOfList [(1, "right")]) := by
  apply mapOfList_append
  intro k hk other
  have hk0 : k = 0 := by simpa [listKeys] using hk
  have hk1 : k = 1 := by simpa [listKeys] using other
  exact (by decide : (0 : Nat) ≠ 1) (hk0.symm.trans hk1)

theorem raw_partial_writes_commute (t : Tree V) (k1 k2 : Key) (a b : V)
    (different : k1 ≠ k2) :
    OrderedMap.pathObserve (insert k1 a (insert k2 b t)) =
      OrderedMap.pathObserve (insert k2 b (insert k1 a t)) := by
  simp only [insert, OrderedMap.pathObserve_bind]
  exact OrderedMap.write_comm (OrderedMap.pathObserve t) k2 k1 b a (Ne.symm different)

theorem opposite_inserts_same_elements (t : Tree V) (valid : BST t) (k1 k2 : Key)
    (a b : V) (different : k1 ≠ k2) :
    elements (insert k1 a (insert k2 b t)) = elements (insert k2 b (insert k1 a t)) := by
  apply OrderedMap.SourceModel.entries_eq_of_lookup_eq
    (bst_insert k1 a _ (bst_insert k2 b t valid))
    (bst_insert k2 b _ (bst_insert k1 a t valid))
  intro query
  exact congrFun (raw_partial_writes_commute t k1 k2 a b different) query

theorem distinct_shapes_same_canonical_list :
    insert 0 true (insert 1 false emptyTree) ≠ insert 1 false (insert 0 true emptyTree) ∧
      elements (insert 0 true (insert 1 false emptyTree)) =
        elements (insert 1 false (insert 0 true emptyTree)) := by
  refine ⟨by decide, ?_⟩
  exact opposite_inserts_same_elements emptyTree (bst_emptyTree Bool) 0 1 true false (by decide)

/-! ## The existing table client on raw search trees -/

/-- The chapter's total lookup forgets absence using its explicit default. -/
abbrev rawTable (default : V) : TotalTable.Ops Key V (Tree V) :=
  TotalTable.ofPartial (OrderedMap.rawTrees Key V) default

/-- Lookup/update algebra needs no BST assumption, even though the independent
whole-tree abstraction and enumeration correspondence do. -/
theorem rawTable_laws (default : V) :
    TotalTable.Laws (rawTable default) default (fun _ => True) :=
  TotalTable.ofPartial_unrestricted (OrderedMap.rawTrees_laws (κ := Key) (ν := V)) default

theorem rawTable_get (default : V) (k : Key) (t : Tree V) :
    (rawTable default).get k t = lookup default k t := rfl

theorem rawTable_set (default : V) (k : Key) (value : V) (t : Tree V) :
    (rawTable default).set k value t = insert k value t := rfl

/-- The previously integrated two-write client runs on arbitrary raw trees. -/
theorem rawTable_two_writes (default : V) (t : Tree V) (k1 k2 : Key) (a b : V) :
    TotalTable.observe (rawTable default)
        (TotalTable.setAll (rawTable default) [(k1, a), (k2, b)] t) =
      Function.update (Function.update (fun q => lookup default q t) k1 a) k2 b :=
  FunctionalMaps.table_two_writes (rawTable_laws default) k1 k2 a b trivial

/-- A complete write history agrees with the function-table implementation
when it starts from the tree's observed function. Raw states need not agree. -/
theorem rawTable_history_agrees (default : V) (t : Tree V) (writes : List (Key × V)) :
    TotalTable.observe (rawTable default) (TotalTable.setAll (rawTable default) writes t) =
      TotalTable.observe (TotalTable.functions default)
        (TotalTable.setAll (TotalTable.functions default) writes (fun q => lookup default q t)) :=
  TotalTable.Laws.setAll_agrees (rawTable_laws default)
    (TotalTable.functions_laws default) writes trivial trivial rfl

/-- The exact Maps example, including the stored default at key 1, executes
through the same total-table client on the source's tree representation. -/
theorem function_example_eq_tree_client :
    FunctionalMaps.exampleMap = TotalTable.observe (rawTable false)
      (TotalTable.setAll (rawTable false) [(1, false), (3, true)] emptyTree) := by
  rw [rawTable_history_agrees]
  rfl

theorem tree_client_agrees_with_list :
    TotalTable.observe (rawTable false)
        (TotalTable.setAll (rawTable false) [(1, false), (3, true)] emptyTree) =
      TotalTable.observe (TotalTable.ofPartial (OrderedMap.lists Nat Bool) false)
        (TotalTable.setAll (TotalTable.ofPartial (OrderedMap.lists Nat Bool) false)
          [(1, false), (3, true)] []) :=
  function_example_eq_tree_client.symm.trans FunctionalMaps.exampleMap_eq_list_client

/-- Empty source trees and their partial abstractions need no payload value. -/
theorem empty_payload (k : Key) :
    bound k (emptyTree : Tree Empty) = false ∧ enumerationMeaning (emptyTree : Tree Empty) k = none ∧
      structuralMeaning (emptyTree : Tree Empty) k = none := ⟨rfl, rfl, rfl⟩

/-- Values may live above the key universe without any ordering on values. -/
theorem high_universe_payload (payload : Type u) :
    OrderedMap.lookup 0 (insert 0 payload (emptyTree : Tree (Type u))) = some payload :=
  OrderedMap.lookup_bind 0 payload 0 emptyTree |>.trans (ite_eq_left rfl)

end Examples.SearchTrees
