import Examples.SearchTrees
import Applications.Sequences.SourceQueue
import Applications.Search.OrderedMap.EnumeratedTable

/-!
# VFA ADT: abstract clients and source representations

The source's module signatures are explicit operation parameters and proved
laws. Generic clients use those laws without inspecting a representation.
Concrete Lean definitions remain transparent: namespaces and structures do not
reproduce Rocq module sealing. The checked elaboration boundaries below state
which type equalities and data eliminations the generic Lean context exposes.

Source: VFA 2.1 `ADT.v`, including every optional and advanced exercise.
The complete correspondence is in `docs/research/vfa-coverage.md`; the source
MIT notice is retained in `docs/licenses/vfa-MIT.txt`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.AbstractDataTypes
open Search
universe u v w

abbrev Table (V : Type v) (T : Type w) := TotalTable.Ops Nat V T
abbrev TableLaws {V : Type v} {T : Type w} (table : Table V T) (d : V) :=
  TotalTable.Laws table d (fun _ => True)

abbrev FunTable {V : Type v} (d : V) : Table V (Nat → V) := TotalTable.functions d
abbrev ListsTable {V : Type v} (d : V) : Table V (List (Nat × V)) :=
  TotalTable.ofPartial (OrderedMap.lists Nat V) d
abbrev TreeTable {V : Type v} (d : V) : Table V (SearchTrees.Tree V) :=
  TotalTable.ofPartial (OrderedMap.rawTrees Nat V) d

theorem FunTable_laws {V : Type v} (d : V) : TableLaws (FunTable d) d :=
  TotalTable.functions_laws d

theorem ListsTable_laws {V : Type v} (d : V) : TableLaws (ListsTable d) d :=
  TotalTable.ofPartial_unrestricted OrderedMap.lists_laws d

theorem TreeTable_laws {V : Type v} (d : V) : TableLaws (TreeTable d) d :=
  TotalTable.ofPartial_unrestricted OrderedMap.rawTrees_laws d

theorem function_set_source {V : Type v} (d value : V) (k : Nat) (t : Nat → V) :
    (FunTable d).set k value t = fun q => if k == q then value else t q :=
  OrderedMap.update_nat_source t k value

theorem lists_set_source {V : Type v} (d value : V) (k : Nat)
    (t : List (Nat × V)) : (ListsTable d).set k value t = (k, value) :: t := rfl

theorem tree_set_source {V : Type v} (d value : V) (k : Nat)
    (t : SearchTrees.Tree V) : (TreeTable d).set k value t = SearchTrees.insert k value t := rfl

/-! ## The concrete String and optional Nat clients -/

namespace StringVal
abbrev V := String
def default : V := ""
end StringVal

abbrev StringFunTable := FunTable StringVal.default

theorem function_ex1 : StringFunTable.get 0 StringFunTable.empty = "" :=
  (FunTable_laws "").get_empty 0

theorem function_ex2 :
    StringFunTable.get 0 (StringFunTable.set 0 "A" StringFunTable.empty) = "A" :=
  (FunTable_laws "").get_set_same 0 "A" _ trivial

theorem function_ex3 :
    StringFunTable.get 1 (StringFunTable.set 0 "A" StringFunTable.empty) = "" :=
  ((FunTable_laws "").get_set_other 0 1 "A" _ (by decide) trivial).trans
    ((FunTable_laws "").get_empty 1)

abbrev NatFunTable := FunTable (0 : Nat)

theorem nat_function_empty : NatFunTable.get 7 NatFunTable.empty = 0 :=
  (FunTable_laws 0).get_empty 7

theorem nat_function_same :
    NatFunTable.get 7 (NatFunTable.set 7 11 NatFunTable.empty) = 11 :=
  (FunTable_laws 0).get_set_same 7 11 _ trivial

theorem nat_function_other :
    NatFunTable.get 8 (NatFunTable.set 7 11 NatFunTable.empty) = 0 := by
  rw [(FunTable_laws 0).get_set_other 7 8 11 _ (by decide) trivial]
  exact (FunTable_laws 0).get_empty 8

theorem nat_function_repeated :
    NatFunTable.get 7 (NatFunTable.set 7 0 (NatFunTable.set 7 11 NatFunTable.empty)) = 0 :=
  (FunTable_laws 0).get_set_same 7 0 _ trivial

abbrev StringListsTable := ListsTable StringVal.default

theorem lists_ex1 : StringListsTable.get 0 StringListsTable.empty = "" :=
  (ListsTable_laws "").get_empty 0

theorem lists_ex2 :
    StringListsTable.get 0 (StringListsTable.set 0 "A" StringListsTable.empty) = "A" :=
  (ListsTable_laws "").get_set_same 0 "A" _ trivial

theorem lists_ex3 :
    StringListsTable.get 1 (StringListsTable.set 0 "A" StringListsTable.empty) = "" :=
  ((ListsTable_laws "").get_set_other 0 1 "A" _ (by decide) trivial).trans
    ((ListsTable_laws "").get_empty 1)

theorem lists_repeated_raw_shape :
    StringListsTable.set 0 "B" (StringListsTable.set 0 "A" StringListsTable.empty) =
      [(0, "B"), (0, "A")] := rfl

theorem lists_repeated_lookup :
    StringListsTable.get 0 [(0, "B"), (0, "A")] = "B" :=
  (ListsTable_laws "").get_set_same 0 "B" [(0, "A")] trivial

theorem exposed_trees_ex :
    (TreeTable "").get 0 (SearchTrees.node SearchTrees.nil 0 "A" SearchTrees.nil) = "A" := rfl

/-! ## One chronological client on the three raw representations -/

/-- This source-Table client uses the established two-write theorem. It is
unconditional on raw states because Table's laws use the True predicate. -/
theorem table_two_writes {V : Type v} {T : Type w} (table : Table V T) (d : V)
    (law : TableLaws table d) (first second : Nat) (a b : V) (t : T) :
    TotalTable.observe table (TotalTable.setAll table [(first, a), (second, b)] t) =
      Function.update (Function.update (TotalTable.observe table t) first a) second b :=
  FunctionalMaps.table_two_writes law first second a b trivial

/-- An arbitrary complete history, including repeated keys, is shared with
the function implementation from the same initial observation. -/
theorem table_history_function {V : Type v} {T : Type w} (table : Table V T) (d : V)
    (law : TableLaws table d) (writes : List (Nat × V)) (t : T) :
    TotalTable.observe table (TotalTable.setAll table writes t) =
      TotalTable.observe (FunTable d)
        (TotalTable.setAll (FunTable d) writes (TotalTable.observe table t)) :=
  TotalTable.Laws.setAll_agrees law (FunTable_laws d) writes trivial trivial rfl

theorem table_history_empty {V : Type v} {T : Type w} (table : Table V T) (d : V)
    (law : TableLaws table d) (writes : List (Nat × V)) :
    TotalTable.observe table (TotalTable.setAll table writes table.empty) =
      TotalTable.observe (FunTable d)
        (TotalTable.setAll (FunTable d) writes (FunTable d).empty) := by
  apply TotalTable.Laws.setAll_agrees law (FunTable_laws d) writes trivial trivial
  funext key
  exact law.get_empty key

theorem three_raw_histories {V : Type v} (d : V) (writes : List (Nat × V)) :
    TotalTable.observe (ListsTable d)
        (TotalTable.setAll (ListsTable d) writes (ListsTable d).empty) =
      TotalTable.observe (FunTable d)
        (TotalTable.setAll (FunTable d) writes (FunTable d).empty) ∧
    TotalTable.observe (TreeTable d)
        (TotalTable.setAll (TreeTable d) writes (TreeTable d).empty) =
      TotalTable.observe (FunTable d)
        (TotalTable.setAll (FunTable d) writes (FunTable d).empty) :=
  ⟨table_history_empty _ d (ListsTable_laws d) writes,
   table_history_empty _ d (TreeTable_laws d) writes⟩

def clientWrites : List (Nat × String) := [(1, "B"), (0, "A"), (0, "")]

def clientResult {T : Type w} (table : Table String T) : List String :=
  let result := TotalTable.setAll table clientWrites table.empty
  [table.get 0 result, table.get 1 result, table.get 2 result]

theorem clientResult_correct {T : Type w} (table : Table String T)
    (law : TableLaws table "") : clientResult table = ["", "B", ""] := by
  have history := table_history_empty table "" law clientWrites
  have zero := congrFun history 0
  have one := congrFun history 1
  have two := congrFun history 2
  change table.get 0 (TotalTable.setAll table clientWrites table.empty) = "" at zero
  change table.get 1 (TotalTable.setAll table clientWrites table.empty) = "B" at one
  change table.get 2 (TotalTable.setAll table clientWrites table.empty) = "" at two
  simp only [clientResult, zero, one, two]

theorem raw_client_results :
    clientResult StringFunTable = ["", "B", ""] ∧
      clientResult StringListsTable = ["", "B", ""] ∧
      clientResult (TreeTable "") = ["", "B", ""] :=
  ⟨clientResult_correct _ (FunTable_laws ""),
    clientResult_correct _ (ListsTable_laws ""),
    clientResult_correct _ (TreeTable_laws "")⟩

/-- The all-raw-state table law continues to apply to the malformed source
tree, independently of the enumeration invariant. -/
theorem malformed_table_update :
    (TreeTable "").get 2 ((TreeTable "").set 2 "new" SearchTrees.Malformed.exampleTree) = "new" :=
  (TreeTable_laws "").get_set_same 2 "new" _ trivial

/-- The attempted raw-tree membership soundness fails at an actual member. -/
theorem malformed_tree_member :
    (2, "two") ∈ SearchTrees.elements SearchTrees.Malformed.exampleTree ∧
      SearchTrees.bound 2 SearchTrees.Malformed.exampleTree = false ∧
      (TreeTable "").get 2 SearchTrees.Malformed.exampleTree = "" := by decide

/-- Default-valued get does not recover the presence bit or elements. -/
theorem table_default_forgets_presence :
    TotalTable.observe (TreeTable false) (SearchTrees.node SearchTrees.nil 0 false SearchTrees.nil) =
      TotalTable.observe (TreeTable false) SearchTrees.nil ∧
    SearchTrees.bound 0 (SearchTrees.node SearchTrees.nil 0 false SearchTrees.nil) = true ∧
    SearchTrees.bound 0 (SearchTrees.nil : SearchTrees.Tree Bool) = false := by
  obtain ⟨same, bound, absent, _⟩ := SearchTrees.explicit_default_and_absence
  exact ⟨funext same, bound, absent⟩

/-! ## Corrected enumeration and both source abstraction routes -/

namespace TreeETable
abbrev table (V : Type v) := SearchTrees.Tree V
abbrev observations (V : Type v) :=
  OrderedMap.EnumeratedTable.rawTreeObservations (κ := Nat) (ν := V)
abbrev rep_ok {V : Type v} (t : table V) := SearchTrees.BST t
abbrev bound {V : Type v} (key : Nat) (t : table V) := SearchTrees.bound key t
abbrev elements {V : Type v} (t : table V) := SearchTrees.elements t

theorem laws {V : Type v} (d : V) :
    OrderedMap.EnumeratedTable.Laws (TreeTable d) (observations V) d rep_ok :=
  OrderedMap.EnumeratedTable.rawTree_laws d

theorem empty_ok {V : Type v} (d : V) : rep_ok (TreeTable d).empty :=
  (laws d).empty_valid

theorem set_ok {V : Type v} (d value : V) (key : Nat) (t : table V)
    (valid : rep_ok t) : rep_ok ((TreeTable d).set key value t) :=
  (laws d).set_valid key value t valid

theorem bound_empty {V : Type v} (d : V) (key : Nat) :
    bound key (TreeTable d).empty = false := (laws d).bound_empty key

theorem bound_set_same {V : Type v} (d value : V) (key : Nat) (t : table V) :
    bound key ((TreeTable d).set key value t) = true := (laws d).bound_set_same key value t

theorem bound_set_other {V : Type v} (d value : V) (key query : Nat) (t : table V)
    (different : key ≠ query) :
    bound query ((TreeTable d).set key value t) = bound query t :=
  (laws d).bound_set_other key query value t different

theorem elements_complete_raw {V : Type v} (d value : V) (key : Nat) (t : table V)
    (present : bound key t = true) (found : (TreeTable d).get key t = value) :
    (key, value) ∈ elements t :=
  OrderedMap.EnumeratedTable.rawTree_elements_complete d key value t present found

theorem elements_complete {V : Type v} (d value : V) (key : Nat) (t : table V)
    (valid : rep_ok t) (present : bound key t = true) (found : (TreeTable d).get key t = value) :
    (key, value) ∈ elements t := (laws d).elements_complete key value t valid present found

theorem elements_correct {V : Type v} (d value : V) (key : Nat) (t : table V)
    (valid : rep_ok t) (member : (key, value) ∈ elements t) :
    bound key t = true ∧ (TreeTable d).get key t = value :=
  (laws d).elements_correct key value t valid member

theorem strong {V : Type v} :
    OrderedMap.EnumeratedTable.StrongElements (observations V) rep_ok :=
  OrderedMap.EnumeratedTable.rawTree_strong
end TreeETable

/-- This is the exact source membership example proved through interface laws. -/
theorem string_tree_elements_example :
    (0, "A") ∈ TreeETable.elements
      ((TreeTable "").set 0 "A" ((TreeTable "").set 1 "B" (TreeTable "").empty)) :=
  (TreeETable.laws "").mem_elements_set 0 "A"
    ((TreeETable.laws "").set_valid 1 "B" _ (TreeETable.laws "").empty_valid)

theorem raw_tree_first_attempt_fails :
    ¬ OrderedMap.EnumeratedTable.UnrestrictedEnumerationLaws (TreeTable "")
      (TreeETable.observations String) "" := by
  intro law
  have present := (law.elements_correct 2 "two" SearchTrees.Malformed.exampleTree malformed_tree_member.1).1
  have impossible : (false : Bool) = true := present
  cases impossible

/-- Strong enumeration is consumed through the additional abstract law record.
Its unconditional absence converse remains a separate field. -/
theorem strong_elements_client {V : Type v} {T : Type w}
    (obs : OrderedMap.EnumeratedTable.Observations Nat V T) (Valid : T → Prop)
    (law : OrderedMap.EnumeratedTable.StrongElements obs Valid)
    (key : Nat) (value : V) (t : T) (valid : Valid t) :
    (obs.bound key t = false → (key, value) ∉ obs.elements t) ∧
      InsertionSorting.sorted ((obs.elements t).map Prod.fst) ∧
      ((obs.elements t).map Prod.fst).Nodup :=
  ⟨fun absent => law.absent_no_entry key t valid absent value,
    List.isChain_iff_pairwise.mpr ((law.keys_sorted t valid).imp fun h => Nat.le_of_lt h),
    law.keys_nodup t valid⟩

theorem strong_elements_inverse_raw {V : Type v} {T : Type w}
    (obs : OrderedMap.EnumeratedTable.Observations Nat V T) (Valid : T → Prop)
    (law : OrderedMap.EnumeratedTable.StrongElements obs Valid) (key : Nat) (t : T)
    (absent : ∀ value, (key, value) ∉ obs.elements t) : obs.bound key t = false :=
  law.no_entry_absent key t absent

theorem elements_spec {V : Type v} (key : Nat) (value : V) (t : SearchTrees.Tree V)
    (valid : SearchTrees.BST t) :
    (SearchTrees.bound key t = false → (key, value) ∉ SearchTrees.elements t) ∧
      InsertionSorting.sorted ((SearchTrees.elements t).map Prod.fst) ∧
      ((SearchTrees.elements t).map Prod.fst).Nodup :=
  strong_elements_client (TreeETable.observations V) TreeETable.rep_ok
    TreeETable.strong key value t valid

abbrev map_update {V : Type v} (key : Nat) (value : V) (m : Nat → Option V) :=
  OrderedMap.write key value m
def map_find {V : Type v} (default : V) (key : Nat) (m : Nat → Option V) : V :=
  (m key).getD default
def empty_map {V : Type v} : Nat → Option V := fun _ => none

namespace ListETableAbs
abbrev table (V : Type v) := List (Nat × V)
def empty {V : Type v} : table V := []
def get {V : Type v} (default : V) (key : Nat) (t : table V) : V :=
  (ListsTable default).get key t
def set {V : Type v} (key : Nat) (value : V) (t : table V) : table V := (key, value) :: t
def bound {V : Type v} (key : Nat) (t : table V) : Bool := (OrderedMap.listLookup key t).isSome
def elements {V : Type v} (t : table V) : List (Nat × V) := t
def Abs {V : Type v} (t : table V) : Nat → Option V := OrderedMap.listObserve t
def rep_ok {V : Type v} (_ : table V) : Prop := True

theorem laws {V : Type v} (default : V) :
    OrderedMap.EnumeratedTable.ModelLaws (ListsTable default)
      OrderedMap.EnumeratedTable.rawListObservations default rep_ok Abs :=
  OrderedMap.EnumeratedTable.rawList_model default

theorem empty_ok {V : Type v} : rep_ok (empty : table V) := trivial

theorem set_ok {V : Type v} (key : Nat) (value : V) (t : table V)
    (valid : rep_ok t) : rep_ok (set key value t) :=
  (laws value).set_valid key value t valid

theorem empty_relate (V : Type v) : Abs (empty : table V) = empty_map := rfl

theorem bound_relate {V : Type v} (default : V) (t : table V) (key : Nat)
    (valid : rep_ok t) : SearchTrees.mapBound key (Abs t) = bound key t :=
  (laws default).bound t key valid

theorem lookup_relate {V : Type v} (default : V) (t : table V) (key : Nat)
    (valid : rep_ok t) : map_find default key (Abs t) = get default key t :=
  (laws default).get t key valid

theorem insert_relate {V : Type v} (default : V) (t : table V) (key : Nat) (value : V)
    (valid : rep_ok t) : map_update key value (Abs t) = Abs (set key value t) :=
  (laws default).set t key value valid

theorem elements_relate {V : Type v} (default : V) (t : table V) (valid : rep_ok t) :
    Abs t = SearchTrees.mapOfList (elements t) := (laws default).elements t valid
end ListETableAbs

/-- Both optional model exercises realize every field of the seven-law contract. -/
theorem TreeTableModel {V : Type v} (default : V) :
    OrderedMap.EnumeratedTable.ModelLaws (TreeTable default) (TreeETable.observations V)
      default TreeETable.rep_ok SearchTrees.enumerationMeaning :=
  OrderedMap.EnumeratedTable.rawTree_model_enum default

theorem TreeTableModel' {V : Type v} (default : V) :
    OrderedMap.EnumeratedTable.ModelLaws (TreeTable default) (TreeETable.observations V)
      default TreeETable.rep_ok SearchTrees.structuralMeaning :=
  OrderedMap.EnumeratedTable.rawTree_model_structural default

theorem both_tree_model_histories {V : Type v} (default : V)
    (writes : List (Nat × V)) (t : SearchTrees.Tree V) (valid : SearchTrees.BST t) :
    SearchTrees.enumerationMeaning (TotalTable.setAll (TreeTable default) writes t) =
        OrderedMap.writeAll writes (SearchTrees.enumerationMeaning t) ∧
      SearchTrees.structuralMeaning (TotalTable.setAll (TreeTable default) writes t) =
        OrderedMap.writeAll writes (SearchTrees.structuralMeaning t) :=
  ⟨(TreeTableModel default).setAll writes valid,
    (TreeTableModel' default).setAll writes valid⟩

theorem raw_list_model_history {V : Type v} (default : V)
    (writes : List (Nat × V)) (t : List (Nat × V)) :
    ListETableAbs.Abs (TotalTable.setAll (ListsTable default) writes t) =
      OrderedMap.writeAll writes (ListETableAbs.Abs t) :=
  (ListETableAbs.laws default).setAll writes trivial

theorem raw_list_shadowed_entry :
    ListETableAbs.rep_ok [(0, "new"), (0, "old")] ∧
      (0, "old") ∈ ListETableAbs.elements [(0, "new"), (0, "old")] ∧
      ListETableAbs.get "" 0 [(0, "new"), (0, "old")] ≠ "old" := by
  change True ∧ _ ∧ _
  decide

theorem raw_list_model_not_sound :
    ¬ OrderedMap.EnumeratedTable.UnrestrictedEnumerationLaws (ListsTable "")
      OrderedMap.EnumeratedTable.rawListObservations "" := by
  intro law
  have found := (law.elements_correct 0 "old" [(0, "new"), (0, "old")]
    raw_list_shadowed_entry.2.1).2
  exact raw_list_shadowed_entry.2.2 found

theorem tree_models_agree_on_valid {V : Type v} (t : SearchTrees.Tree V)
    (valid : SearchTrees.BST t) : SearchTrees.enumerationMeaning t = SearchTrees.structuralMeaning t :=
  SearchTrees.abstractions_agree t valid

theorem tree_models_differ_on_raw :
    SearchTrees.enumerationMeaning SearchTrees.collisionTree 0 = some "left" ∧
      SearchTrees.structuralMeaning SearchTrees.collisionTree 0 = none :=
  SearchTrees.raw_abstractions_disagree

/-! ## What an abstract client can see

The reduced teaching signature contains types and a supplied value only.
Its three presentations expose progressively more information through ordinary
Lean parameters. The concrete packages are transparent, while generic clients
do not receive their implementation equations.
-/

structure SimpleTable where
  key : Type u
  V : Type v
  default : V
  table : Type w

def simpleStringTable1 : SimpleTable.{0, 0, 0} :=
  ⟨Nat, String, "", SearchTrees.Tree String⟩

def simpleStringTable2 (key : Type u) (table : Type w) (default : String) :
    SimpleTable.{u, 0, w} := ⟨key, String, default, table⟩

def simpleStringTable3 (key : Type u) (table : Type w) :
    SimpleTable.{u, 0, w} := ⟨key, String, "", table⟩

theorem simpleStringTable2_value (key : Type u) (table : Type w) (default : String) :
    (simpleStringTable2 key table default).V = String := rfl

theorem simpleStringTable2_default (key : Type u) (table : Type w) (default : String) :
    (simpleStringTable2 key table default).default = default := rfl

theorem simpleStringTable3_default (key : Type u) (table : Type w) :
    (simpleStringTable3 key table).default = "" := rfl

/-- The literal has no supplied conversion to arbitrary `V`. The empty lookup
result instead follows from the exposed law, with no representation reduction. -/
theorem abstract_empty_client {V : Type v} {T : Type w} (d : V)
    (table : Table V T) (law : TableLaws table d) (key : Nat) :
    table.get key table.empty = d := by
  fail_if_success have _ : V := ""
  fail_if_success exact rfl
  exact law.get_empty key

/-- Exposing String does not identify an arbitrary supplied default with `""`. -/
theorem string_abstract_default_client {T : Type w} (d : String)
    (table : Table String T) (law : TableLaws table d) :
    table.get 0 table.empty = d := by
  fail_if_success have _ : d = "" := rfl
  exact law.get_empty 0

/-- The carrier stays abstract even when payload and default are exposed. -/
theorem nicely_encapsulated_client {T : Type w}
    (table : Table String T) (law : TableLaws table "") :
    table.get 0 table.empty = "" := by
  fail_if_success have _ : T := SearchTrees.node SearchTrees.nil 0 "A" SearchTrees.nil
  fail_if_success exact rfl
  exact law.get_empty 0

theorem nicely_encapsulated_tree : (TreeTable "").get 0 (TreeTable "").empty = "" :=
  nicely_encapsulated_client (TreeTable "") (TreeTable_laws "")

/-! ## Constructive subtypes and the source's stored-length vectors -/

abbrev even_nat := {n : Nat // Even n}

theorem Even2 : Even (2 : Nat) := ⟨1, rfl⟩

def two : even_nat := ⟨2, Even2⟩

def two' : even_nat := by
  fail_if_success exact 2
  exact ⟨2, ⟨1, rfl⟩⟩

theorem two_data : two.val = 2 := rfl
theorem two'_data : two'.val = 2 := rfl
theorem plus_two : 1 + two.val = 3 := by
  fail_if_success have _ : 1 + two = 3 := rfl
  rfl

/-- Lean permits the standard subtype-to-Nat coercion when the Nat addition
is fixed explicitly; this is a language difference from the source command. -/
theorem plus_two_coercion : (1 : Nat) + two = 3 := rfl

theorem Even2' : Even (2 : Nat) := two.property

namespace SigSandbox
abbrev sig {A : Type u} (P : A → Prop) := Subtype P
abbrev ex {A : Type u} (P : A → Prop) := Exists P

def exist {A : Type u} (P : A → Prop) (x : A) (proof : P x) : sig P := ⟨x, proof⟩

theorem ex_intro {A : Type u} (P : A → Prop) (x : A) (proof : P x) : ex P :=
  ⟨x, proof⟩

def proj1_sig {A : Type u} {P : A → Prop} (e : sig P) : A := e.val
theorem proj2_sig {A : Type u} {P : A → Prop} (e : sig P) : P (proj1_sig e) := e.property

/-- Propositional existence supports propositional elimination, while the
attempted executable witness projection is rejected in this generic context. -/
theorem exists_propositional_elimination {A : Type u} {P : A → Prop} {R : Prop}
    (e : ex P) (consequence : ∀ x, P x → R) : R := by
  fail_if_success
    have _ : A := match e with | ⟨x, _⟩ => x
  exact Exists.elim e consequence
end SigSandbox

abbrev vector (X : Type u) := {p : List X × Nat // p.1.length = p.2}

def a_vector : vector Nat := ⟨([3, 1, 4], 3), rfl⟩

def vector_cons {X : Type u} (x : X) (v : vector X) : vector X :=
  ⟨(x :: v.val.1, v.val.2 + 1), by simp only [List.length_cons, v.property]⟩

def list_of_vector {X : Type u} (v : vector X) : List X := v.val.1

theorem vector_cons_correct (X : Type u) (x : X) (v : vector X) :
    list_of_vector (vector_cons x v) = x :: list_of_vector v := rfl

theorem vector_cons_length {X : Type u} (x : X) (v : vector X) :
    (vector_cons x v).val.2 = v.val.2 + 1 := rfl

def vector_app {X : Type u} (first second : vector X) : vector X :=
  ⟨(first.val.1 ++ second.val.1, first.val.2 + second.val.2), by
    simp only [List.length_append, first.property, second.property]⟩

theorem vector_app_correct (X : Type u) (first second : vector X) :
    list_of_vector (vector_app first second) =
      list_of_vector first ++ list_of_vector second := rfl

theorem vector_app_length {X : Type u} (first second : vector X) :
    (vector_app first second).val.2 = first.val.2 + second.val.2 := rfl

theorem vector_representation {X : Type u} (v : vector X) :
    (list_of_vector v).length = v.val.2 := v.property

theorem vector_concrete_data :
    list_of_vector (vector_app (vector_cons 2 a_vector) a_vector) = [2, 3, 1, 4, 3, 1, 4] :=
  by rw [vector_app_correct, vector_cons_correct]; rfl

theorem vector_concrete_length :
    (vector_app (vector_cons 2 a_vector) a_vector).val.2 = 7 :=
  by rw [vector_app_length, vector_cons_length]; rfl

/-! ## The source's Nat queue modules and shared FIFO client -/

abbrev Queue (V : Type v) (Q : Type w) := Sequences.SourceQueue.Ops V Q
abbrev QueueLaws {V : Type v} {Q : Type w} (ops : Queue V Q) :=
  Sequences.SourceQueue.Laws ops
abbrev QueueAbsLaws {V : Type v} {Q : Type w} (ops : Queue V Q) (Abs : Q → List V) :=
  Sequences.SourceQueue.AbsLaws ops Abs

namespace ListQueue
abbrev V := Nat
abbrev queue := List V
abbrev ops := Sequences.SourceQueue.lists V
def empty : queue := ops.empty
def is_empty (q : queue) : Bool := ops.isEmpty q
def enq (q : queue) (value : V) : queue := ops.enqueue q value
def deq (q : queue) : queue := ops.dequeue q
def peek (default : V) (q : queue) : V := ops.peek default q

theorem is_empty_empty : is_empty empty = true :=
  (Sequences.SourceQueue.lists_laws V).isEmpty_empty

theorem is_empty_nonempty (q : queue) (value : V) : is_empty (enq q value) = false :=
  (Sequences.SourceQueue.lists_laws V).isEmpty_enqueue q value

theorem peek_empty (default : V) : peek default empty = default :=
  (Sequences.SourceQueue.lists_laws V).peek_empty default

theorem peek_nonempty (default : V) (q : queue) (value : V) :
    peek default (enq q value) = peek value q :=
  (Sequences.SourceQueue.lists_laws V).peek_enqueue default q value

theorem deq_empty : deq empty = empty :=
  (Sequences.SourceQueue.lists_laws V).dequeue_empty

theorem deq_nonempty (q : queue) (value : V) :
    deq (enq q value) = if is_empty q then q else enq (deq q) value :=
  (Sequences.SourceQueue.lists_laws V).dequeue_enqueue q value

theorem source_operations (default value : V) (q : queue) :
    empty = [] ∧ is_empty q = q.isEmpty ∧ enq q value = q ++ [value] ∧
      deq q = q.tail ∧ peek default q = q.headD default :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
end ListQueue

namespace TwoListQueueAbs
abbrev V := Nat
abbrev queue := Sequences.SourceQueue.TwoList V
abbrev ops := Sequences.SourceQueue.twoLists V
def empty : queue := ops.empty
def is_empty (q : queue) : Bool := ops.isEmpty q
def enq (q : queue) (value : V) : queue := ops.enqueue q value
def deq (q : queue) : queue := ops.dequeue q
def peek (default : V) (q : queue) : V := ops.peek default q
def Abs (q : queue) : List V := Sequences.SourceQueue.twoListDecode q

theorem empty_relate : Abs empty = [] :=
  (Sequences.SourceQueue.twoLists_absLaws V).empty

theorem enq_relate (q : queue) (value : V) : Abs (enq q value) = Abs q ++ [value] :=
  (Sequences.SourceQueue.twoLists_absLaws V).enqueue q value

theorem peek_relate (default : V) (q : queue) : peek default q = (Abs q).headD default :=
  (Sequences.SourceQueue.twoLists_absLaws V).peek default q

theorem deq_relate (q : queue) : Abs (deq q) = (Abs q).tail :=
  (Sequences.SourceQueue.twoLists_absLaws V).dequeue q

/-- This concrete theorem is additional to the four-law QueueAbs signature. -/
theorem is_empty_relate (q : queue) : is_empty q = (Abs q).isEmpty :=
  Sequences.SourceQueue.twoListIsEmpty_decode q
end TwoListQueueAbs

def queueCommands : List (Sequences.AbstractFIFO.Command Nat) :=
  [.enqueue 7, .enqueue 8, .delete, .enqueue 9]

theorem queue_source_client :
    Sequences.AbstractFIFO.client (Sequences.SourceQueue.twoListFIFO Nat)
      queueCommands TwoListQueueAbs.empty = some 8 :=
  Sequences.SourceQueue.twoList_client_empty queueCommands

theorem queue_source_peek_client :
    TwoListQueueAbs.peek 0
      (Sequences.AbstractFIFO.run (Sequences.SourceQueue.twoListFIFO Nat)
        queueCommands TwoListQueueAbs.empty) = 8 := by
  exact Sequences.SourceQueue.twoList_peek_run 0 queueCommands TwoListQueueAbs.empty

theorem queue_branches :
    TwoListQueueAbs.peek 99 ([], []) = 99 ∧
      TwoListQueueAbs.peek 99 ([], [2, 1]) = 1 ∧
      TwoListQueueAbs.deq ([], [2, 1]) = ([2], []) ∧
      TwoListQueueAbs.peek 99 ([1], [2]) = 1 ∧
      TwoListQueueAbs.deq ([1], [2]) = ([], [2]) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem queue_abs_does_not_imply_raw_laws :
    QueueAbsLaws TwoListQueueAbs.ops TwoListQueueAbs.Abs ∧
      ¬ QueueLaws TwoListQueueAbs.ops :=
  ⟨Sequences.SourceQueue.twoLists_absLaws Nat, Sequences.SourceQueue.twoLists_not_laws⟩

theorem queue_abs_does_not_constrain_empty_test :
    QueueAbsLaws { ListQueue.ops with isEmpty := fun _ => false } id ∧
      ({ ListQueue.ops with isEmpty := fun _ => false } : Queue Nat (List Nat)).isEmpty [] = false :=
  Sequences.SourceQueue.model_empty_test_unconstrained Nat

/-- The generic table operations need no equality or order on stored types. -/
theorem type_valued_table (default value : Type u) (key : Nat) :
    (FunTable default).get key ((FunTable default).set key value (FunTable default).empty) = value :=
  (FunTable_laws default).get_set_same key value _ trivial

/-! ## Validity carried by tree and unique-list subtypes -/

namespace TreeETableSubset
abbrev table (V : Type v) := OrderedMap.Tree Nat V
abbrev ops {V : Type v} (default : V) := OrderedMap.EnumeratedTable.treeTable (κ := Nat) default
def empty {V : Type v} : table V := (OrderedMap.trees Nat V).empty
def get {V : Type v} (default : V) (key : Nat) (t : table V) : V :=
  (ops default).get key t
def set {V : Type v} (key : Nat) (value : V) (t : table V) : table V :=
  (OrderedMap.trees Nat V).bind key value t
def bound {V : Type v} (key : Nat) (t : table V) : Bool :=
  OrderedMap.EnumeratedTable.treeObservations.bound key t
def elements {V : Type v} (t : table V) : List (Nat × V) :=
  OrderedMap.EnumeratedTable.treeObservations.elements t

theorem laws {V : Type v} (default : V) :
    OrderedMap.EnumeratedTable.SubsetLaws (ops default)
      OrderedMap.EnumeratedTable.treeObservations default :=
  OrderedMap.EnumeratedTable.tree_laws default

theorem get_empty_default {V : Type v} (default : V) (key : Nat) :
    get default key empty = default := (laws default).table_laws.get_empty key

theorem get_set_same {V : Type v} (default value : V) (key : Nat) (t : table V) :
    get default key (set key value t) = value :=
  (laws default).table_laws.get_set_same key value t trivial

theorem get_set_other {V : Type v} (default value : V) (key query : Nat) (t : table V)
    (different : key ≠ query) : get default query (set key value t) = get default query t :=
  (laws default).table_laws.get_set_other key query value t different trivial

theorem bound_empty {V : Type v} (key : Nat) : bound key (empty : table V) = false := by
  rfl

theorem bound_set_same {V : Type v} (key : Nat) (value : V) (t : table V) :
    bound key (set key value t) = true := (laws value).bound_set_same key value t

theorem bound_set_other {V : Type v} (key query : Nat) (value : V) (t : table V)
    (different : key ≠ query) : bound query (set key value t) = bound query t :=
  (laws value).bound_set_other key query value t different

theorem elements_complete {V : Type v} (default value : V) (key : Nat) (t : table V)
    (present : bound key t = true) (found : get default key t = value) :
    (key, value) ∈ elements t :=
  (laws default).elements_complete key value t trivial present found

theorem elements_correct {V : Type v} (default value : V) (key : Nat) (t : table V)
    (member : (key, value) ∈ elements t) :
    bound key t = true ∧ get default key t = value :=
  (laws default).elements_correct key value t trivial member

theorem elements_source {V : Type v} (t : table V) :
    elements t = SearchTrees.elements t.val := rfl

theorem first_attempt_realized {V : Type v} (default : V) :
    OrderedMap.EnumeratedTable.UnrestrictedEnumerationLaws (ops default)
      OrderedMap.EnumeratedTable.treeObservations default := (laws default).unrestrictedEnumerationLaws
end TreeETableSubset

namespace ListsETable
abbrev table (V : Type v) := OrderedMap.AssociationListEnumeration.UniqueList Nat V
abbrev ops {V : Type v} (default : V) :=
  OrderedMap.EnumeratedTable.uniqueListTable (κ := Nat) default
def empty {V : Type v} : table V := OrderedMap.AssociationListEnumeration.empty
def get {V : Type v} (default : V) (key : Nat) (t : table V) : V := (ops default).get key t
def set {V : Type v} (key : Nat) (value : V) (t : table V) : table V :=
  OrderedMap.AssociationListEnumeration.set key value t
def bound {V : Type v} (key : Nat) (t : table V) : Bool :=
  OrderedMap.EnumeratedTable.uniqueListObservations.bound key t
def elements {V : Type v} (t : table V) : List (Nat × V) := t.val

theorem laws {V : Type v} (default : V) :
    OrderedMap.EnumeratedTable.SubsetLaws (ops default)
      OrderedMap.EnumeratedTable.uniqueListObservations default :=
  OrderedMap.EnumeratedTable.uniqueList_laws default

theorem elements_identity {V : Type v} (t : table V) : elements t = t.val := rfl

theorem elements_set {V : Type v} (key : Nat) (value : V) (t : table V) :
    elements (set key value t) =
      (key, value) :: t.val.eraseP (fun binding => decide (key = binding.1)) :=
  OrderedMap.AssociationListEnumeration.set_entries key value t

theorem first_attempt_realized {V : Type v} (default : V) :
    OrderedMap.EnumeratedTable.UnrestrictedEnumerationLaws (ops default)
      OrderedMap.EnumeratedTable.uniqueListObservations default := (laws default).unrestrictedEnumerationLaws

theorem complete {V : Type v} (default value : V) (key : Nat) (t : table V)
    (present : bound key t = true) (found : get default key t = value) :
    (key, value) ∈ elements t :=
  (laws default).elements_complete key value t trivial present found

theorem correct {V : Type v} (default value : V) (key : Nat) (t : table V)
    (member : (key, value) ∈ elements t) :
    bound key t = true ∧ get default key t = value :=
  (laws default).elements_correct key value t trivial member
end ListsETable

def uniqueUnsorted : ListsETable.table String :=
  ⟨[(2, "two"), (0, "zero"), (1, "one")], by decide⟩

theorem unique_unsorted_is_legal :
    (ListsETable.elements uniqueUnsorted).map Prod.fst = [2, 0, 1] ∧
      ((ListsETable.elements uniqueUnsorted).map Prod.fst).Nodup ∧
      ¬ ((ListsETable.elements uniqueUnsorted).map Prod.fst).Pairwise (· < ·) :=
  ⟨rfl, uniqueUnsorted.property, by decide⟩

theorem unique_replacement_entries :
    ListsETable.elements (ListsETable.set 0 "new" uniqueUnsorted) =
      [(0, "new"), (2, "two"), (1, "one")] := by
  rw [ListsETable.elements_set]
  rfl

theorem unique_replacement_lookup :
    ListsETable.get "" 0 (ListsETable.set 0 "new" uniqueUnsorted) = "new" :=
  (ListsETable.laws "").table_laws.get_set_same 0 "new" uniqueUnsorted trivial

theorem unique_other_lookup :
    ListsETable.get "" 1 (ListsETable.set 0 "new" uniqueUnsorted) = "one" :=
  (ListsETable.laws "").table_laws.get_set_other 0 1 "new" uniqueUnsorted (by decide) trivial

/-- The stored pair list is connected to the existing AList operation itself. -/
theorem unique_update_aList_bridge :
    OrderedMap.AssociationListEnumeration.toAList (ListsETable.set 0 "new" uniqueUnsorted) =
      AList.insert 0 "new" (OrderedMap.AssociationListEnumeration.toAList uniqueUnsorted) :=
  OrderedMap.AssociationListEnumeration.toAList_set 0 "new" uniqueUnsorted

theorem unique_lookup_aList_bridge :
    AList.lookup 1 (OrderedMap.AssociationListEnumeration.toAList uniqueUnsorted) = some "one" :=
  OrderedMap.AssociationListEnumeration.lookup_toAList 1 uniqueUnsorted

theorem unique_aList_roundtrip :
    OrderedMap.AssociationListEnumeration.ofAList
      (OrderedMap.AssociationListEnumeration.aListEquiv uniqueUnsorted) = uniqueUnsorted :=
  OrderedMap.AssociationListEnumeration.ofAList_toAList uniqueUnsorted

theorem unique_repeated_write {V : Type v} (key : Nat) (first last : V)
    (t : ListsETable.table V) :
    ListsETable.set key last (ListsETable.set key first t) = ListsETable.set key last t :=
  OrderedMap.AssociationListEnumeration.set_shadow key first last t

theorem subset_client_results :
    clientResult (TreeETableSubset.ops "") = ["", "B", ""] ∧
      clientResult (ListsETable.ops "") = ["", "B", ""] :=
  ⟨clientResult_correct _ (TreeETableSubset.laws "").table_laws,
    clientResult_correct _ (ListsETable.laws "").table_laws⟩

theorem tree_subset_source_member :
    (0, "A") ∈ TreeETableSubset.elements
      (TreeETableSubset.set 0 "A" (TreeETableSubset.set 1 "B" TreeETableSubset.empty)) :=
  (TreeETableSubset.laws "").mem_elements_set 0 "A" trivial

theorem model_repeated_history_checked :
    ListETableAbs.Abs (TotalTable.setAll (ListsTable "") clientWrites [(0, "old")]) =
        OrderedMap.writeAll clientWrites (ListETableAbs.Abs [(0, "old")]) ∧
      SearchTrees.enumerationMeaning (TotalTable.setAll (TreeTable "") clientWrites (TreeTable "").empty) =
        OrderedMap.writeAll clientWrites (SearchTrees.enumerationMeaning (TreeTable "").empty) ∧
      SearchTrees.structuralMeaning (TotalTable.setAll (TreeTable "") clientWrites (TreeTable "").empty) =
        OrderedMap.writeAll clientWrites (SearchTrees.structuralMeaning (TreeTable "").empty) :=
  ⟨raw_list_model_history "" clientWrites [(0, "old")],
    both_tree_model_histories "" clientWrites _ (TreeETable.empty_ok "")⟩

end Examples.AbstractDataTypes
