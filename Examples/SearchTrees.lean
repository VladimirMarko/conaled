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

abbrev key := Nat
abbrev tree (V : Type u) := BinaryTree (key × V)

def E : tree V := .nil
def T (left : tree V) (k : key) (value : V) (right : tree V) : tree V :=
  .node (k, value) left right

def empty_tree : tree V := E
def bound (k : key) (t : tree V) : Bool := (OrderedMap.lookup k t).isSome
def lookup (default : V) (k : key) (t : tree V) : V :=
  (OrderedMap.lookup k t).getD default
abbrev insert (k : key) (value : V) (t : tree V) : tree V := OrderedMap.bind k value t

theorem bound_empty (k : key) : bound k (empty_tree : tree V) = false := rfl

theorem bound_node (k x : key) (left right : tree V) (value : V) :
    bound k (T left x value right) =
      if k < x then bound k left else if x < k then bound k right else true := by
  simp only [bound, T, OrderedMap.lookup]
  split
  · rfl
  · split <;> rfl

theorem lookup_node (default : V) (k x : key) (left right : tree V) (value : V) :
    lookup default k (T left x value right) =
      if k < x then lookup default k left
      else if x < k then lookup default k right else value := by
  simp only [lookup, T, OrderedMap.lookup]
  split
  · rfl
  · split <;> rfl

theorem insert_empty (k : key) (value : V) :
    insert k value empty_tree = T E k value E := rfl

theorem insert_node (k x : key) (value old : V) (left right : tree V) :
    insert k value (T left x old right) =
      if k < x then T (insert k value left) x old right
      else if x < k then T left x old (insert k value right)
      else T left k value right := rfl

def ex_tree : tree String := T (T E 2 "two" E) 4 "four" (T E 5 "five" E)

theorem bst_ex1 :
    insert 5 "five" (insert 2 "two" (insert 4 "four" empty_tree)) = ex_tree := rfl

theorem bst_ex2 : lookup "" 5 ex_tree = "five" := rfl
theorem bst_ex3 : lookup "" 3 ex_tree = "" := rfl
theorem bst_ex4 : bound 3 ex_tree = false := rfl

namespace NotBst
def t : tree String := T (T E 5 "five" E) 4 "four" (T E 2 "two" E)
theorem not_bst_lookup_wrong : lookup "" 2 t ≠ "two" := by decide
end NotBst

abbrev ForallT (P : key → V → Prop) (t : tree V) : Prop :=
  OrderedTree.All (fun binding => P binding.1 binding.2) t
abbrev BST (t : tree V) : Prop := OrderedTree.OrderedBy Prod.fst t

theorem forallT_node (P : key → V → Prop) (left right : tree V) (k : key) (value : V) :
    ForallT P (T left k value right) ↔
      P k value ∧ ForallT P left ∧ ForallT P right := Iff.rfl

/-- The shared recursive invariant supplies the source constructor interface. -/
theorem bst_node (left right : tree V) (k : key) (value : V) :
    BST (T left k value right) ↔
      ForallT (fun q _ => q < k) left ∧ ForallT (fun q _ => k < q) right ∧
        BST left ∧ BST right := by
  simp only [BST, T, OrderedTree.OrderedBy, ForallT]
  tauto

/-- Induction on valid trees retains both all-descendant separator premises. -/
theorem bst_induction (P : tree V → Prop) (base : P E)
    (step : ∀ (left : tree V) (k : key) (value : V) (right : tree V),
      ForallT (fun q _ => q < k) left → ForallT (fun q _ => k < q) right →
      BST left → BST right → P left → P right → P (T left k value right))
    (t : tree V) (valid : BST t) : P t := by
  induction t with
  | nil => exact base
  | node binding left right ihl ihr =>
      exact step left binding.1 binding.2 right valid.2.2.1 valid.2.2.2
        valid.1 valid.2.1 (ihl valid.1) (ihr valid.2.1)

theorem is_BST_ex : BST ex_tree := by
  norm_num [ex_tree, T, E, BST, OrderedTree.OrderedBy, OrderedTree.All]
theorem not_BST_ex : ¬ BST NotBst.t := by
  norm_num [NotBst.t, T, E, BST, OrderedTree.OrderedBy, OrderedTree.All]
theorem empty_tree_BST (V : Type u) : BST (empty_tree : tree V) := trivial

theorem ForallT_insert (P : key → V → Prop) (t : tree V) (all : ForallT P t)
    (k : key) (value : V) (new : P k value) : ForallT P (insert k value t) :=
  OrderedMap.all_bind all k value new

theorem insert_BST (k : key) (value : V) (t : tree V) (valid : BST t) :
    BST (insert k value t) := OrderedMap.ordered_bind valid k value

theorem lookup_empty (V : Type u) (default : V) (k : key) :
    lookup default k empty_tree = default := rfl

theorem lookup_insert (t : tree V) (default : V) (k query : key) (value : V) :
    lookup default query (insert k value t) =
      if query = k then value else lookup default query t := by
  simp only [lookup, insert, OrderedMap.lookup_bind]
  split <;> rfl

theorem lookup_insert_eq (t : tree V) (default : V) (k : key) (value : V) :
    lookup default k (insert k value t) = value := by
  simp [lookup_insert]

theorem lookup_insert_neq (t : tree V) (default : V) (k query : key) (value : V)
    (different : k ≠ query) :
    lookup default query (insert k value t) = lookup default query t := by
  rw [lookup_insert, ite_eq_right (Ne.symm different)]

theorem bound_insert_eq (t : tree V) (k : key) (value : V) :
    bound k (insert k value t) = true := by
  simp [bound, insert, OrderedMap.lookup_bind]

theorem bound_insert_neq (t : tree V) (k query : key) (value : V)
    (different : k ≠ query) : bound query (insert k value t) = bound query t := by
  simp only [bound, insert, OrderedMap.lookup_bind, ite_eq_right (Ne.symm different)]

theorem bound_default (k : key) (default : V) (t : tree V)
    (absent : bound k t = false) : lookup default k t = default := by
  cases found : OrderedMap.lookup k t with
  | none => simp [lookup, found]
  | some value => simp [bound, found] at absent

/-- These clients use the public raw laws and require no invariant. -/
theorem lookup_insert_shadow (t : tree V) (value old default : V) (k query : key) :
    lookup default query (insert k value (insert k old t)) =
      lookup default query (insert k value t) := by
  by_cases same : query = k <;> simp [lookup_insert, same]

theorem lookup_insert_same (k query : key) (default : V) (t : tree V) :
    lookup default query (insert k (lookup default k t) t) = lookup default query t := by
  by_cases same : query = k <;> simp [lookup_insert, same]

theorem lookup_insert_permute (value1 value2 default : V) (k1 k2 query : key)
    (t : tree V) (different : k1 ≠ k2) :
    lookup default query (insert k1 value1 (insert k2 value2 t)) =
      lookup default query (insert k2 value2 (insert k1 value1 t)) := by
  by_cases first : query = k1
  · subst query
    simp [lookup_insert, different]
  · by_cases second : query = k2
    · subst query
      simp [lookup_insert, Ne.symm different]
    · simp [lookup_insert, first, second]

theorem insert_shadow_equality (t : tree V) (k : key) (value old : V) :
    insert k value (insert k old t) = insert k value t :=
  OrderedMap.bind_shadow k old value t

/-- A missing key can acquire an explicit default-valued binding. -/
theorem insert_same_equality_breaks :
    ∃ (V : Type u) (default : V) (t : tree V) (k : key),
      insert k (lookup default k t) t ≠ t := by
  refine ⟨ULift.{u} Unit, ⟨()⟩, E, 0, ?_⟩
  simp [insert, lookup, E, OrderedMap.lookup, OrderedMap.bind]

/-- Opposite insertion orders give different roots even with equal payloads. -/
theorem insert_permute_equality_breaks :
    ∃ (V : Type u) (value1 value2 : V) (k1 k2 : key) (t : tree V),
      k1 ≠ k2 ∧ insert k1 value1 (insert k2 value2 t) ≠
        insert k2 value2 (insert k1 value1 t) := by
  refine ⟨ULift.{u} Unit, ⟨()⟩, ⟨()⟩, 0, 1, E, by decide, ?_⟩
  simp [insert, E, OrderedMap.bind]

abbrev elements (t : tree V) : List (key × V) := OrderedTree.entries t

theorem elements_node (left right : tree V) (k : key) (value : V) :
    elements (T left k value right) = elements left ++ ([(k, value)] ++ elements right) := rfl

theorem elements_ex : elements ex_tree = [(2, "two"), (4, "four"), (5, "five")] := rfl

def elements_complete_broken_spec : Prop :=
  ∀ (V : Type u) (k : key) (value default : V) (t : tree V),
    BST t → lookup default k t = value → (k, value) ∈ elements t

/-- The source's aborted specification already fails on the empty valid tree. -/
theorem elements_complete_broken : ¬ elements_complete_broken_spec.{u} := by
  intro claimed
  have impossible := claimed (ULift.{u} Unit) 0 ⟨()⟩ ⟨()⟩ E trivial rfl
  exact List.not_mem_nil impossible

def elements_complete_spec : Prop :=
  ∀ (V : Type u) (k : key) (value default : V) (t : tree V),
    bound k t = true → lookup default k t = value → (k, value) ∈ elements t

theorem elements_complete : elements_complete_spec.{u} := by
  intro V k value default t present returned
  have found : OrderedMap.lookup k t = some value :=
    (OrderedMap.binding_iff default (OrderedMap.pathObserve t) k value).mpr ⟨present, returned⟩
  exact (OrderedTree.contains_iff_mem_entries _ _).mp (OrderedMap.lookup_some_contains found)

def elements_correct_spec : Prop :=
  ∀ (V : Type u) (k : key) (value default : V) (t : tree V),
    BST t → (k, value) ∈ elements t → bound k t = true ∧ lookup default k t = value

theorem elements_preserves_forall (P : key → V → Prop) (t : tree V)
    (all : ForallT P t) : ∀ binding ∈ elements t, P binding.1 binding.2 := by
  intro binding member
  exact all.of_contains ((OrderedTree.contains_iff_mem_entries _ _).mpr member)

theorem elements_preserves_relation (k other : key) (value : V) (t : tree V)
    (R : key → key → Prop) (all : ForallT (fun q _ => R q other) t)
    (member : (k, value) ∈ elements t) : R k other :=
  elements_preserves_forall (fun q _ => R q other) t all (k, value) member

theorem bound_value (k : key) (t : tree V) (present : bound k t = true) :
    ∃ value, ∀ default, lookup default k t = value := by
  cases found : OrderedMap.lookup k t with
  | none => simp [bound, found] at present
  | some value => exact ⟨value, fun default => by simp [lookup, found]⟩

theorem elements_correct_inverse (k : key) (t : tree V)
    (absent : ∀ value, (k, value) ∉ elements t) : bound k t = false := by
  cases present : bound k t with
  | false => rfl
  | true =>
      obtain ⟨value, returned⟩ := bound_value k t present
      exact False.elim (absent value (elements_complete V k value value t present (returned value)))

theorem elements_correct : elements_correct_spec.{u} := by
  intro V k value default t valid member
  have found := (OrderedMap.lookup_eq_some_iff_mem_entries valid k value).mpr member
  exact (OrderedMap.binding_iff default (OrderedMap.pathObserve t) k value).mp found

theorem elements_complete_inverse (k : key) (value : V) (t : tree V)
    (valid : BST t) (absent : bound k t = false) : (k, value) ∉ elements t := by
  intro member
  have present := (elements_correct V k value value t valid member).1
  simp only [absent, Bool.false_eq_true] at present

theorem sorted_app (left right : List Nat) (pivot : Nat)
    (hl : InsertionSorting.sorted left) (hr : InsertionSorting.sorted right)
    (lesser : ∀ n ∈ left, n < pivot) (greater : ∀ n ∈ right, pivot < n) :
    InsertionSorting.sorted (left ++ pivot :: right) := by
  apply List.isChain_iff_pairwise.mpr
  refine List.pairwise_append.mpr ⟨List.isChain_iff_pairwise.mp hl,
    List.pairwise_cons.mpr ⟨fun n member => Nat.le_of_lt (greater n member),
      List.isChain_iff_pairwise.mp hr⟩, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.mp hb with same | member
  · simpa only [same] using Nat.le_of_lt (lesser a ha)
  · exact Nat.le_of_lt (Nat.lt_trans (lesser a ha) (greater b member))

def list_keys (bindings : List (key × V)) : List key := bindings.map Prod.fst

theorem sorted_elements (t : tree V) (valid : BST t) :
    InsertionSorting.sorted (list_keys (elements t)) :=
  List.isChain_iff_pairwise.mpr
    ((OrderedMap.ordered_entries_keys_pairwise valid).imp fun h => Nat.le_of_lt h)

def disjoint {X : Type u} (left right : List X) : Prop :=
  ∀ x, x ∈ left → x ∉ right

theorem NoDup_append {X : Type u} (left right : List X)
    (hl : left.Nodup) (hr : right.Nodup) (apart : disjoint left right) :
    (left ++ right).Nodup := hl.append hr (fun x hx => apart x hx)

theorem elements_nodup_keys (t : tree V) (valid : BST t) :
    (list_keys (elements t)).Nodup := OrderedMap.ordered_entries_keys_nodup valid

abbrev fast_elements_tr (t : tree V) (suffix : List (key × V)) : List (key × V) :=
  OrderedMap.fastEntriesAcc t suffix
abbrev fast_elements (t : tree V) : List (key × V) := OrderedMap.fastEntries t

theorem fast_elements_tr_node (left right : tree V) (k : key) (value : V)
    (suffix : List (key × V)) :
    fast_elements_tr (T left k value right) suffix =
      fast_elements_tr left ((k, value) :: fast_elements_tr right suffix) := rfl

theorem fast_elements_tr_helper (t : tree V) (suffix : List (key × V)) :
    fast_elements_tr t suffix = elements t ++ suffix := OrderedMap.fastEntriesAcc_eq t suffix

theorem fast_elements_eq_elements (t : tree V) : fast_elements t = elements t :=
  OrderedMap.fastEntries_eq t

/-- Correctness is transported through the public value equality. -/
theorem fast_elements_correct (k : key) (value default : V) (t : tree V)
    (valid : BST t) (member : (k, value) ∈ fast_elements t) :
    bound k t = true ∧ lookup default k t = value := by
  rw [fast_elements_eq_elements] at member
  exact elements_correct V k value default t valid member

theorem fast_elements_sorted (t : tree V) (valid : BST t) :
    InsertionSorting.sorted (list_keys (fast_elements t)) := by
  rw [fast_elements_eq_elements]
  exact sorted_elements t valid

theorem fast_nonempty_accumulator :
    fast_elements_tr ex_tree [(9, "tail")] =
      [(2, "two"), (4, "four"), (5, "five"), (9, "tail")] := by
  rw [fast_elements_tr_helper, elements_ex]
  rfl

theorem elements_empty (V : Type u) : elements (empty_tree : tree V) = [] := rfl

abbrev kvs_insert (k : key) (value : V) (bindings : List (key × V)) :=
  OrderedMap.kvsInsert k value bindings

theorem kvs_insert_split (value old : V) (left right : List (key × V)) (k pivot : key)
    (hl : ∀ binding ∈ left, binding.1 < pivot)
    (hr : ∀ binding ∈ right, pivot < binding.1) :
    kvs_insert k value (left ++ (pivot, old) :: right) =
      if k < pivot then kvs_insert k value left ++ (pivot, old) :: right
      else if pivot < k then left ++ (pivot, old) :: kvs_insert k value right
      else left ++ (k, value) :: right :=
  OrderedMap.kvsInsert_split k value pivot old left right hl hr

/-- The common split law applies even when the right suffix has no ordering invariant. -/
theorem kvs_insert_arbitrary_right (right : List (key × V)) (value old small : V) :
    kvs_insert 7 value ((1, small) :: (5, old) :: right) =
      (1, small) :: (5, old) :: kvs_insert 7 value right := by
  simpa using OrderedMap.kvsInsert_split_of_left
    7 value 5 old [(1, small)] right (by simp)

/-- An unsorted, duplicate-bearing suffix violates the old extra premise but still splits. -/
theorem kvs_insert_arbitrary_right_witness :
    ¬ (∀ binding ∈ ([(0, 20), (5, 60), (0, 30)] : List (key × Nat)), 5 < binding.1) ∧
      kvs_insert 7 70 [(1, 10), (5, 50), (0, 20), (5, 60), (0, 30)] =
        [(1, 10), (5, 50), (0, 20), (5, 60), (0, 30), (7, 70)] := by
  refine ⟨by decide, ?_⟩
  exact kvs_insert_arbitrary_right [(0, 20), (5, 60), (0, 30)] 70 50 10

/-- Dropping the left separator changes where the actual insertion stops. -/
theorem kvs_insert_left_separator_needed :
    kvs_insert 7 70 ([(9, 90)] ++ (5, 50) :: []) ≠
      [(9, 90)] ++ (5, 50) :: kvs_insert 7 70 [] := by decide

theorem kvs_insert_elements (t : tree V) (valid : BST t) (k : key) (value : V) :
    elements (insert k value t) = kvs_insert k value (elements t) :=
  OrderedMap.entries_bind valid k value

/-- An unreachable misplaced binding does not invalidate raw update algebra. -/
theorem malformed_update_still_observed : lookup "" 2 (insert 2 "new" NotBst.t) = "new" :=
  lookup_insert_eq NotBst.t "" 2 "new"

theorem explicit_default_and_absence :
    (∀ k, lookup false k (T E 0 false E) = lookup false k E) ∧
      bound 0 (T E 0 false E) = true ∧ bound 0 (E : tree Bool) = false ∧
      elements (T E 0 false E) ≠ elements (E : tree Bool) := by
  refine ⟨?_, rfl, rfl, by decide⟩
  intro k
  change lookup false k (insert 0 false (E : tree Bool)) = lookup false k E
  exact lookup_insert_same 0 k false E

theorem bound_default_converse_fails :
    lookup false 0 (T E 0 false E) = false ∧ bound 0 (T E 0 false E) ≠ false := by
  exact ⟨rfl, by decide⟩

theorem key_zero_replacement (first last : V) :
    insert 0 last (insert 0 first empty_tree) = T E 0 last E := by
  rw [insert_shadow_equality]
  rfl

/-- The payload can itself be a function; no payload order or equality is used. -/
theorem function_payload (f : Unit → Nat) (t : tree (Unit → Nat)) :
    lookup (fun _ => 0) 0 (insert 0 f t) = f := lookup_insert_eq t (fun _ => 0) 0 f

/-! ## The enumeration abstraction and its exact source specializations -/

abbrev map_of_list (bindings : List (key × V)) : FunctionalMaps.partial_map V :=
  OrderedMap.listObserve bindings
abbrev Abs (t : tree V) : FunctionalMaps.partial_map V := OrderedMap.SourceModel.enumAbs t
abbrev find (default : V) (k : key) (m : FunctionalMaps.partial_map V) :=
  OrderedMap.withDefault default m k
abbrev map_bound (k : key) (m : FunctionalMaps.partial_map V) := OrderedMap.hasBinding m k

theorem map_of_list_empty : map_of_list ([] : List (key × V)) = FunctionalMaps.empty := rfl

theorem map_of_list_cons (k : key) (value : V) (rest : List (key × V)) :
    map_of_list ((k, value) :: rest) = FunctionalMaps.update (map_of_list rest) k value := by
  rw [FunctionalMaps.update_eq_write]
  exact OrderedMap.SourceModel.listObserve_cons (k, value) rest

theorem in_fst {X : Type u} {Y : Type v} (bindings : List (X × Y)) (x : X) (y : Y)
    (member : (x, y) ∈ bindings) : x ∈ bindings.map Prod.fst :=
  OrderedMap.SourceModel.in_keys_of_mem member

theorem in_map_of_list (bindings : List (key × V)) (k : key) (value : V)
    (unique : (list_keys bindings).Nodup) (member : (k, value) ∈ bindings) :
    map_of_list bindings k = some value :=
  OrderedMap.SourceModel.listObserve_eq_some_of_mem unique member

theorem not_in_map_of_list (bindings : List (key × V)) (k : key)
    (absent : k ∉ list_keys bindings) : map_of_list bindings k = none :=
  OrderedMap.SourceModel.listObserve_none_of_not_mem absent

theorem empty_relate (V : Type u) : Abs (empty_tree : tree V) = FunctionalMaps.empty := rfl

theorem bound_relate (t : tree V) (k : key) (valid : BST t) :
    map_bound k (Abs t) = bound k t := OrderedMap.SourceModel.enumAbs_bound valid k

theorem lookup_relate (t : tree V) (default : V) (k : key) (valid : BST t) :
    find default k (Abs t) = lookup default k t :=
  OrderedMap.SourceModel.enumAbs_default valid default k

theorem insert_relate (t : tree V) (k : key) (value : V) (valid : BST t) :
    Abs (insert k value t) = FunctionalMaps.update (Abs t) k value := by
  rw [FunctionalMaps.update_eq_write]
  exact OrderedMap.SourceModel.enumAbs_bind valid k value

theorem elements_relate (t : tree V) (_valid : BST t) : map_of_list (elements t) = Abs t := rfl

/-! ## The independent structural abstraction -/

abbrev union (left right : FunctionalMaps.partial_map V) : FunctionalMaps.partial_map V :=
  OrderedMap.SourceModel.collisionUnion left right

theorem union_left (left right : FunctionalMaps.partial_map V) (k : key)
    (absent : right k = none) : union left right k = left k :=
  OrderedMap.SourceModel.collisionUnion_left left right k absent

theorem union_right (left right : FunctionalMaps.partial_map V) (k : key)
    (absent : left k = none) : union left right k = right k :=
  OrderedMap.SourceModel.collisionUnion_right left right k absent

theorem union_both (left right : FunctionalMaps.partial_map V) (k : key) (a b : V)
    (hl : left k = some a) (hr : right k = some b) : union left right k = none :=
  OrderedMap.SourceModel.collisionUnion_both left right k a b hl hr

theorem union_update_right (left right : FunctionalMaps.partial_map V) (k : key) (value : V)
    (absent : left k = none) :
    FunctionalMaps.update (union left right) k value =
      union left (FunctionalMaps.update right k value) := by
  simp only [FunctionalMaps.update_eq_write]
  exact OrderedMap.SourceModel.collisionUnion_write_right left right k value absent

theorem union_update_left (left right : FunctionalMaps.partial_map V) (k : key) (value : V)
    (absent : right k = none) :
    FunctionalMaps.update (union left right) k value =
      union (FunctionalMaps.update left k value) right := by
  simp only [FunctionalMaps.update_eq_write]
  exact OrderedMap.SourceModel.collisionUnion_write_left left right k value absent

abbrev map_of_tree (t : tree V) : FunctionalMaps.partial_map V := OrderedMap.SourceModel.mapOfTree t
abbrev Abs' (t : tree V) : FunctionalMaps.partial_map V := map_of_tree t

theorem map_of_tree_node (left right : tree V) (k : key) (value : V) :
    map_of_tree (T left k value right) =
      FunctionalMaps.update (union (map_of_tree left) (map_of_tree right)) k value := by
  rw [FunctionalMaps.update_eq_write]
  rfl

theorem map_of_tree_prop (P : key → V → Prop) (t : tree V) (all : ForallT P t)
    (k : key) (value : V) (found : map_of_tree t k = some value) : P k value :=
  OrderedMap.SourceModel.mapOfTree_prop all k value found

theorem empty_relate' (V : Type u) : Abs' (empty_tree : tree V) = FunctionalMaps.empty := rfl

theorem bound_relate' (t : tree V) (k : key) (valid : BST t) :
    map_bound k (Abs' t) = bound k t := OrderedMap.SourceModel.mapOfTree_bound valid k

theorem lookup_relate' (default : V) (t : tree V) (k : key) (valid : BST t) :
    find default k (Abs' t) = lookup default k t :=
  OrderedMap.SourceModel.mapOfTree_default valid default k

theorem insert_relate' (k : key) (value : V) (t : tree V) (valid : BST t) :
    Abs' (insert k value t) = FunctionalMaps.update (Abs' t) k value := by
  rw [FunctionalMaps.update_eq_write]
  exact OrderedMap.SourceModel.mapOfTree_bind valid k value

theorem map_of_list_app (left right : List (key × V))
    (apart : disjoint (list_keys left) (list_keys right)) :
    map_of_list (left ++ right) = union (map_of_list left) (map_of_list right) :=
  OrderedMap.SourceModel.listObserve_append_of_disjoint left right (fun k hk => apart k hk)

theorem elements_relate' (t : tree V) (valid : BST t) : map_of_list (elements t) = Abs' t :=
  OrderedMap.SourceModel.enumAbs_eq_mapOfTree valid

theorem abstractions_agree (t : tree V) (valid : BST t) : Abs t = Abs' t :=
  OrderedMap.SourceModel.enumAbs_eq_mapOfTree valid

theorem canonical_enumeration (left right : tree V) (hl : BST left) (hr : BST right)
    (same : Abs left = Abs right) : elements left = elements right :=
  OrderedMap.SourceModel.entries_eq_of_enumAbs_eq hl hr same

theorem enumerated_finite_support (t : tree V) :
    ∃ keys : List key, ∀ k value, Abs t k = some value → k ∈ keys :=
  OrderedMap.SourceModel.enumAbs_finite_support t

theorem structural_finite_support (t : tree V) :
    ∃ keys : List key, ∀ k value, Abs' t k = some value → k ∈ keys :=
  OrderedMap.SourceModel.mapOfTree_finite_support t

/-! ## Separating clients of the two abstractions -/

theorem duplicate_member_is_shadowed :
    (0, "second") ∈ [(0, "first"), (0, "second")] ∧
      map_of_list [(0, "first"), (0, "second")] 0 = some "first" ∧
      map_of_list [(0, "first"), (0, "second")] 0 ≠ some "second" := by
  exact ⟨by simp, rfl, by decide⟩

def collision_tree : tree String := T (T E 0 "left" E) 1 "root" (T E 0 "right" E)

theorem raw_abstractions_disagree :
    Abs collision_tree 0 = some "left" ∧ Abs' collision_tree 0 = none := ⟨rfl, rfl⟩

theorem collision_tree_not_BST : ¬ BST collision_tree := by
  norm_num [collision_tree, T, E, BST, OrderedTree.OrderedBy, OrderedTree.All]

theorem all_union_branches (value : V) :
    union (fun _ => none) (fun _ => none) 0 = (none : Option V) ∧
      union (fun _ => some value) (fun _ => none) 0 = some value ∧
      union (fun _ => none) (fun _ => some value) 0 = some value ∧
      union (fun _ => some value) (fun _ => some value) 0 = none := ⟨rfl, rfl, rfl, rfl⟩

/-- Absence of the other operand at the write key is a necessary premise. -/
theorem union_update_without_absence_fails :
    FunctionalMaps.update
        (union (FunctionalMaps.update FunctionalMaps.empty 0 "old") FunctionalMaps.empty)
        0 "new" ≠
      union (FunctionalMaps.update FunctionalMaps.empty 0 "old")
        (FunctionalMaps.update FunctionalMaps.empty 0 "new") := by
  intro same
  have impossible : (some "new" : Option String) = none := congrFun same 0
  cases impossible

theorem union_not_associative :
    union (union (fun _ => some (1 : Nat)) (fun _ => some 2)) (fun _ => some 3) ≠
      union (fun _ => some (1 : Nat)) (union (fun _ => some 2) (fun _ => some 3)) := by
  intro same
  have impossible : (some 3 : Option Nat) = some 1 := congrFun same 0
  cases impossible

/-- Repetition inside one operand is permitted by the disjoint-domain law. -/
theorem disjoint_append_with_internal_duplicates :
    map_of_list ([(0, "first"), (0, "shadowed")] ++ [(1, "right")]) =
      union (map_of_list [(0, "first"), (0, "shadowed")]) (map_of_list [(1, "right")]) := by
  apply map_of_list_app
  intro k hk other
  have hk0 : k = 0 := by simpa [list_keys] using hk
  have hk1 : k = 1 := by simpa [list_keys] using other
  exact (by decide : (0 : Nat) ≠ 1) (hk0.symm.trans hk1)

theorem raw_partial_writes_commute (t : tree V) (k1 k2 : key) (a b : V)
    (different : k1 ≠ k2) :
    OrderedMap.pathObserve (insert k1 a (insert k2 b t)) =
      OrderedMap.pathObserve (insert k2 b (insert k1 a t)) := by
  simp only [insert, OrderedMap.pathObserve_bind]
  exact OrderedMap.write_comm (OrderedMap.pathObserve t) k2 k1 b a (Ne.symm different)

theorem opposite_inserts_same_elements (t : tree V) (valid : BST t) (k1 k2 : key)
    (a b : V) (different : k1 ≠ k2) :
    elements (insert k1 a (insert k2 b t)) = elements (insert k2 b (insert k1 a t)) := by
  apply OrderedMap.SourceModel.entries_eq_of_lookup_eq
    (insert_BST k1 a _ (insert_BST k2 b t valid))
    (insert_BST k2 b _ (insert_BST k1 a t valid))
  intro query
  exact congrFun (raw_partial_writes_commute t k1 k2 a b different) query

theorem distinct_shapes_same_canonical_list :
    insert 0 true (insert 1 false empty_tree) ≠ insert 1 false (insert 0 true empty_tree) ∧
      elements (insert 0 true (insert 1 false empty_tree)) =
        elements (insert 1 false (insert 0 true empty_tree)) := by
  refine ⟨by decide, ?_⟩
  exact opposite_inserts_same_elements empty_tree (empty_tree_BST Bool) 0 1 true false (by decide)

/-! ## The existing table client on raw search trees -/

/-- The chapter's total lookup forgets absence using its explicit default. -/
abbrev rawTable (default : V) : TotalTable.Ops key V (tree V) :=
  TotalTable.ofPartial (OrderedMap.rawTrees key V) default

/-- Lookup/update algebra needs no BST assumption, even though the independent
whole-tree abstraction and enumeration correspondence do. -/
theorem rawTable_laws (default : V) :
    TotalTable.Laws (rawTable default) default (fun _ => True) :=
  TotalTable.ofPartial_unrestricted (OrderedMap.rawTrees_laws (κ := key) (ν := V)) default

theorem rawTable_get (default : V) (k : key) (t : tree V) :
    (rawTable default).get k t = lookup default k t := rfl

theorem rawTable_set (default : V) (k : key) (value : V) (t : tree V) :
    (rawTable default).set k value t = insert k value t := rfl

/-- The previously integrated two-write client runs on arbitrary raw trees. -/
theorem rawTable_two_writes (default : V) (t : tree V) (k1 k2 : key) (a b : V) :
    TotalTable.observe (rawTable default)
        (TotalTable.setAll (rawTable default) [(k1, a), (k2, b)] t) =
      Function.update (Function.update (fun q => lookup default q t) k1 a) k2 b :=
  FunctionalMaps.table_two_writes (rawTable_laws default) k1 k2 a b trivial

/-- A complete write history agrees with the function-table implementation
when it starts from the tree's observed function. Raw states need not agree. -/
theorem rawTable_history_agrees (default : V) (t : tree V) (writes : List (key × V)) :
    TotalTable.observe (rawTable default) (TotalTable.setAll (rawTable default) writes t) =
      TotalTable.observe (TotalTable.functions default)
        (TotalTable.setAll (TotalTable.functions default) writes (fun q => lookup default q t)) :=
  TotalTable.Laws.setAll_agrees (rawTable_laws default)
    (TotalTable.functions_laws default) writes trivial trivial rfl

/-- The exact Maps example, including the stored default at key 1, executes
through the same total-table client on the source's tree representation. -/
theorem examplemap_eq_tree_client :
    FunctionalMaps.examplemap = TotalTable.observe (rawTable false)
      (TotalTable.setAll (rawTable false) [(1, false), (3, true)] empty_tree) := by
  rw [rawTable_history_agrees]
  rfl

theorem tree_client_agrees_with_list :
    TotalTable.observe (rawTable false)
        (TotalTable.setAll (rawTable false) [(1, false), (3, true)] empty_tree) =
      TotalTable.observe (TotalTable.ofPartial (OrderedMap.lists Nat Bool) false)
        (TotalTable.setAll (TotalTable.ofPartial (OrderedMap.lists Nat Bool) false)
          [(1, false), (3, true)] []) :=
  examplemap_eq_tree_client.symm.trans FunctionalMaps.examplemap_eq_list_client

/-- Empty source trees and their partial abstractions need no payload value. -/
theorem empty_payload (k : key) :
    bound k (empty_tree : tree Empty) = false ∧ Abs (empty_tree : tree Empty) k = none ∧
      Abs' (empty_tree : tree Empty) k = none := ⟨rfl, rfl, rfl⟩

/-- Values may live above the key universe without any ordering on values. -/
theorem high_universe_payload (payload : Type u) :
    OrderedMap.lookup 0 (insert 0 payload (empty_tree : tree (Type u))) = some payload :=
  OrderedMap.lookup_bind 0 payload 0 empty_tree |>.trans (ite_eq_left rfl)

end Examples.SearchTrees
