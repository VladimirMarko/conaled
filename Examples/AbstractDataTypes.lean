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

abbrev functionTable {V : Type v} (d : V) : Table V (Nat → V) := TotalTable.functions d
abbrev listTable {V : Type v} (d : V) : Table V (List (Nat × V)) :=
  TotalTable.ofPartial (OrderedMap.lists Nat V) d
abbrev treeTable {V : Type v} (d : V) : Table V (SearchTrees.Tree V) :=
  TotalTable.ofPartial (OrderedMap.rawTrees Nat V) d

theorem functionTable_laws {V : Type v} (d : V) : TableLaws (functionTable d) d :=
  TotalTable.functions_laws d

theorem listTable_laws {V : Type v} (d : V) : TableLaws (listTable d) d :=
  TotalTable.ofPartial_unrestricted OrderedMap.lists_laws d

theorem treeTable_laws {V : Type v} (d : V) : TableLaws (treeTable d) d :=
  TotalTable.ofPartial_unrestricted OrderedMap.rawTrees_laws d

theorem functionTable_set_source {V : Type v} (d value : V) (k : Nat) (t : Nat → V) :
    (functionTable d).set k value t = fun q => if k == q then value else t q :=
  OrderedMap.update_nat_source t k value

theorem listTable_set_source {V : Type v} (d value : V) (k : Nat)
    (t : List (Nat × V)) : (listTable d).set k value t = (k, value) :: t := rfl

theorem treeTable_set_source {V : Type v} (d value : V) (k : Nat)
    (t : SearchTrees.Tree V) : (treeTable d).set k value t = SearchTrees.insert k value t := rfl

/-! ## The concrete String and optional Nat clients -/

namespace StringPayload
abbrev Value := String
def default : Value := ""
end StringPayload

abbrev stringFunctionTable := functionTable StringPayload.default

theorem stringFunctionTable_empty : stringFunctionTable.get 0 stringFunctionTable.empty = "" :=
  (functionTable_laws "").get_empty 0

theorem stringFunctionTable_same_key :
    stringFunctionTable.get 0 (stringFunctionTable.set 0 "A" stringFunctionTable.empty) = "A" :=
  (functionTable_laws "").get_set_same 0 "A" _ trivial

theorem stringFunctionTable_other_key :
    stringFunctionTable.get 1 (stringFunctionTable.set 0 "A" stringFunctionTable.empty) = "" :=
  ((functionTable_laws "").get_set_other 0 1 "A" _ (by decide) trivial).trans
    ((functionTable_laws "").get_empty 1)

abbrev natFunctionTable := functionTable (0 : Nat)

theorem natFunctionTable_empty : natFunctionTable.get 7 natFunctionTable.empty = 0 :=
  (functionTable_laws 0).get_empty 7

theorem natFunctionTable_same_key :
    natFunctionTable.get 7 (natFunctionTable.set 7 11 natFunctionTable.empty) = 11 :=
  (functionTable_laws 0).get_set_same 7 11 _ trivial

theorem natFunctionTable_other_key :
    natFunctionTable.get 8 (natFunctionTable.set 7 11 natFunctionTable.empty) = 0 := by
  rw [(functionTable_laws 0).get_set_other 7 8 11 _ (by decide) trivial]
  exact (functionTable_laws 0).get_empty 8

theorem natFunctionTable_repeated_write :
    natFunctionTable.get 7 (natFunctionTable.set 7 0 (natFunctionTable.set 7 11 natFunctionTable.empty)) = 0 :=
  (functionTable_laws 0).get_set_same 7 0 _ trivial

abbrev stringListTable := listTable StringPayload.default

theorem stringListTable_empty : stringListTable.get 0 stringListTable.empty = "" :=
  (listTable_laws "").get_empty 0

theorem stringListTable_same_key :
    stringListTable.get 0 (stringListTable.set 0 "A" stringListTable.empty) = "A" :=
  (listTable_laws "").get_set_same 0 "A" _ trivial

theorem stringListTable_other_key :
    stringListTable.get 1 (stringListTable.set 0 "A" stringListTable.empty) = "" :=
  ((listTable_laws "").get_set_other 0 1 "A" _ (by decide) trivial).trans
    ((listTable_laws "").get_empty 1)

theorem stringListTable_repeated_raw_shape :
    stringListTable.set 0 "B" (stringListTable.set 0 "A" stringListTable.empty) =
      [(0, "B"), (0, "A")] := rfl

theorem stringListTable_repeated_lookup :
    stringListTable.get 0 [(0, "B"), (0, "A")] = "B" :=
  (listTable_laws "").get_set_same 0 "B" [(0, "A")] trivial

theorem treeTable_singleton_lookup :
    (treeTable "").get 0 (SearchTrees.node SearchTrees.nil 0 "A" SearchTrees.nil) = "A" := rfl

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
      TotalTable.observe (functionTable d)
        (TotalTable.setAll (functionTable d) writes (TotalTable.observe table t)) :=
  TotalTable.Laws.setAll_agrees law (functionTable_laws d) writes trivial trivial rfl

theorem table_history_empty {V : Type v} {T : Type w} (table : Table V T) (d : V)
    (law : TableLaws table d) (writes : List (Nat × V)) :
    TotalTable.observe table (TotalTable.setAll table writes table.empty) =
      TotalTable.observe (functionTable d)
        (TotalTable.setAll (functionTable d) writes (functionTable d).empty) := by
  apply TotalTable.Laws.setAll_agrees law (functionTable_laws d) writes trivial trivial
  funext key
  exact law.get_empty key

theorem three_raw_histories {V : Type v} (d : V) (writes : List (Nat × V)) :
    TotalTable.observe (listTable d)
        (TotalTable.setAll (listTable d) writes (listTable d).empty) =
      TotalTable.observe (functionTable d)
        (TotalTable.setAll (functionTable d) writes (functionTable d).empty) ∧
    TotalTable.observe (treeTable d)
        (TotalTable.setAll (treeTable d) writes (treeTable d).empty) =
      TotalTable.observe (functionTable d)
        (TotalTable.setAll (functionTable d) writes (functionTable d).empty) :=
  ⟨table_history_empty _ d (listTable_laws d) writes,
   table_history_empty _ d (treeTable_laws d) writes⟩

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
    clientResult stringFunctionTable = ["", "B", ""] ∧
      clientResult stringListTable = ["", "B", ""] ∧
      clientResult (treeTable "") = ["", "B", ""] :=
  ⟨clientResult_correct _ (functionTable_laws ""),
    clientResult_correct _ (listTable_laws ""),
    clientResult_correct _ (treeTable_laws "")⟩

/-- The all-raw-state table law continues to apply to the malformed source
tree, independently of the enumeration invariant. -/
theorem malformed_table_update :
    (treeTable "").get 2 ((treeTable "").set 2 "new" SearchTrees.Malformed.exampleTree) = "new" :=
  (treeTable_laws "").get_set_same 2 "new" _ trivial

/-- The attempted raw-tree membership soundness fails at an actual member. -/
theorem malformed_tree_member :
    (2, "two") ∈ SearchTrees.elements SearchTrees.Malformed.exampleTree ∧
      SearchTrees.bound 2 SearchTrees.Malformed.exampleTree = false ∧
      (treeTable "").get 2 SearchTrees.Malformed.exampleTree = "" := by decide

/-- Default-valued get does not recover the presence bit or elements. -/
theorem table_default_forgets_presence :
    TotalTable.observe (treeTable false) (SearchTrees.node SearchTrees.nil 0 false SearchTrees.nil) =
      TotalTable.observe (treeTable false) SearchTrees.nil ∧
    SearchTrees.bound 0 (SearchTrees.node SearchTrees.nil 0 false SearchTrees.nil) = true ∧
    SearchTrees.bound 0 (SearchTrees.nil : SearchTrees.Tree Bool) = false := by
  obtain ⟨same, bound, absent, _⟩ := SearchTrees.explicit_default_and_absence
  exact ⟨funext same, bound, absent⟩

/-! ## Corrected enumeration and both source abstraction routes -/

namespace RawTreeTable
abbrev Carrier (V : Type v) := SearchTrees.Tree V
abbrev observations (V : Type v) :=
  OrderedMap.EnumeratedTable.rawTreeObservations (κ := Nat) (ν := V)
abbrev Valid {V : Type v} (t : Carrier V) := SearchTrees.BST t
abbrev bound {V : Type v} (key : Nat) (t : Carrier V) := SearchTrees.bound key t
abbrev elements {V : Type v} (t : Carrier V) := SearchTrees.elements t

theorem laws {V : Type v} (d : V) :
    OrderedMap.EnumeratedTable.Laws (treeTable d) (observations V) d Valid :=
  OrderedMap.EnumeratedTable.rawTree_laws d

theorem empty_valid {V : Type v} (d : V) : Valid (treeTable d).empty :=
  (laws d).empty_valid

theorem set_valid {V : Type v} (d value : V) (key : Nat) (t : Carrier V)
    (valid : Valid t) : Valid ((treeTable d).set key value t) :=
  (laws d).set_valid key value t valid

theorem bound_empty {V : Type v} (d : V) (key : Nat) :
    bound key (treeTable d).empty = false := (laws d).bound_empty key

theorem bound_set_same {V : Type v} (d value : V) (key : Nat) (t : Carrier V) :
    bound key ((treeTable d).set key value t) = true := (laws d).bound_set_same key value t

theorem bound_set_other {V : Type v} (d value : V) (key query : Nat) (t : Carrier V)
    (different : key ≠ query) :
    bound query ((treeTable d).set key value t) = bound query t :=
  (laws d).bound_set_other key query value t different

theorem elements_complete_raw {V : Type v} (d value : V) (key : Nat) (t : Carrier V)
    (present : bound key t = true) (found : (treeTable d).get key t = value) :
    (key, value) ∈ elements t :=
  OrderedMap.EnumeratedTable.rawTree_elements_complete d key value t present found

theorem elements_complete {V : Type v} (d value : V) (key : Nat) (t : Carrier V)
    (valid : Valid t) (present : bound key t = true) (found : (treeTable d).get key t = value) :
    (key, value) ∈ elements t := (laws d).elements_complete key value t valid present found

theorem elements_correct {V : Type v} (d value : V) (key : Nat) (t : Carrier V)
    (valid : Valid t) (member : (key, value) ∈ elements t) :
    bound key t = true ∧ (treeTable d).get key t = value :=
  (laws d).elements_correct key value t valid member

theorem strong {V : Type v} :
    OrderedMap.EnumeratedTable.StrongElements (observations V) Valid :=
  OrderedMap.EnumeratedTable.rawTree_strong
end RawTreeTable

/-- This is the exact source membership example proved through interface laws. -/
theorem string_tree_elements_example :
    (0, "A") ∈ RawTreeTable.elements
      ((treeTable "").set 0 "A" ((treeTable "").set 1 "B" (treeTable "").empty)) :=
  (RawTreeTable.laws "").mem_elements_set 0 "A"
    ((RawTreeTable.laws "").set_valid 1 "B" _ (RawTreeTable.laws "").empty_valid)

theorem raw_tree_unrestricted_enumeration_fails :
    ¬ OrderedMap.EnumeratedTable.UnrestrictedEnumerationLaws (treeTable "")
      (RawTreeTable.observations String) "" := by
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
      InsertionSorting.Sorted ((obs.elements t).map Prod.fst) ∧
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
      InsertionSorting.Sorted ((SearchTrees.elements t).map Prod.fst) ∧
      ((SearchTrees.elements t).map Prod.fst).Nodup :=
  strong_elements_client (RawTreeTable.observations V) RawTreeTable.Valid
    RawTreeTable.strong key value t valid

abbrev mapUpdate {V : Type v} (key : Nat) (value : V) (m : Nat → Option V) :=
  OrderedMap.write key value m
def mapFind {V : Type v} (default : V) (key : Nat) (m : Nat → Option V) : V :=
  (m key).getD default
def emptyMap {V : Type v} : Nat → Option V := fun _ => none

namespace ShadowingListModel
abbrev Carrier (V : Type v) := List (Nat × V)
def empty {V : Type v} : Carrier V := []
def get {V : Type v} (default : V) (key : Nat) (t : Carrier V) : V :=
  (listTable default).get key t
def set {V : Type v} (key : Nat) (value : V) (t : Carrier V) : Carrier V := (key, value) :: t
def bound {V : Type v} (key : Nat) (t : Carrier V) : Bool := (OrderedMap.listLookup key t).isSome
def elements {V : Type v} (t : Carrier V) : List (Nat × V) := t
def meaning {V : Type v} (t : Carrier V) : Nat → Option V := OrderedMap.listObserve t
def Valid {V : Type v} (_ : Carrier V) : Prop := True

theorem laws {V : Type v} (default : V) :
    OrderedMap.EnumeratedTable.ModelLaws (listTable default)
      OrderedMap.EnumeratedTable.rawListObservations default Valid meaning :=
  OrderedMap.EnumeratedTable.rawList_model default

theorem empty_valid {V : Type v} : Valid (empty : Carrier V) := trivial

theorem set_valid {V : Type v} (key : Nat) (value : V) (t : Carrier V)
    (valid : Valid t) : Valid (set key value t) :=
  (laws value).set_valid key value t valid

theorem meaning_empty (V : Type v) : meaning (empty : Carrier V) = emptyMap := rfl

theorem meaning_bound {V : Type v} (default : V) (t : Carrier V) (key : Nat)
    (valid : Valid t) : SearchTrees.mapBound key (meaning t) = bound key t :=
  (laws default).bound t key valid

theorem meaning_lookup {V : Type v} (default : V) (t : Carrier V) (key : Nat)
    (valid : Valid t) : mapFind default key (meaning t) = get default key t :=
  (laws default).get t key valid

theorem meaning_set {V : Type v} (default : V) (t : Carrier V) (key : Nat) (value : V)
    (valid : Valid t) : mapUpdate key value (meaning t) = meaning (set key value t) :=
  (laws default).set t key value valid

theorem meaning_elements {V : Type v} (default : V) (t : Carrier V) (valid : Valid t) :
    meaning t = SearchTrees.mapOfList (elements t) := (laws default).elements t valid
end ShadowingListModel

/-- Both optional model exercises realize every field of the seven-law contract. -/
theorem treeTable_enumeration_model {V : Type v} (default : V) :
    OrderedMap.EnumeratedTable.ModelLaws (treeTable default) (RawTreeTable.observations V)
      default RawTreeTable.Valid SearchTrees.enumerationMeaning :=
  OrderedMap.EnumeratedTable.rawTree_model_enum default

theorem treeTable_structural_model {V : Type v} (default : V) :
    OrderedMap.EnumeratedTable.ModelLaws (treeTable default) (RawTreeTable.observations V)
      default RawTreeTable.Valid SearchTrees.structuralMeaning :=
  OrderedMap.EnumeratedTable.rawTree_model_structural default

theorem both_tree_model_histories {V : Type v} (default : V)
    (writes : List (Nat × V)) (t : SearchTrees.Tree V) (valid : SearchTrees.BST t) :
    SearchTrees.enumerationMeaning (TotalTable.setAll (treeTable default) writes t) =
        OrderedMap.writeAll writes (SearchTrees.enumerationMeaning t) ∧
      SearchTrees.structuralMeaning (TotalTable.setAll (treeTable default) writes t) =
        OrderedMap.writeAll writes (SearchTrees.structuralMeaning t) :=
  ⟨(treeTable_enumeration_model default).setAll writes valid,
    (treeTable_structural_model default).setAll writes valid⟩

theorem raw_list_model_history {V : Type v} (default : V)
    (writes : List (Nat × V)) (t : List (Nat × V)) :
    ShadowingListModel.meaning (TotalTable.setAll (listTable default) writes t) =
      OrderedMap.writeAll writes (ShadowingListModel.meaning t) :=
  (ShadowingListModel.laws default).setAll writes trivial

theorem raw_list_shadowed_entry :
    ShadowingListModel.Valid [(0, "new"), (0, "old")] ∧
      (0, "old") ∈ ShadowingListModel.elements [(0, "new"), (0, "old")] ∧
      ShadowingListModel.get "" 0 [(0, "new"), (0, "old")] ≠ "old" := by
  change True ∧ _ ∧ _
  decide

theorem raw_list_unrestricted_enumeration_fails :
    ¬ OrderedMap.EnumeratedTable.UnrestrictedEnumerationLaws (listTable "")
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

structure TableSignature where
  Key : Type u
  Payload : Type v
  default : Payload
  Carrier : Type w

def stringTreeSignature : TableSignature.{0, 0, 0} :=
  ⟨Nat, String, "", SearchTrees.Tree String⟩

def stringSignature (key : Type u) (table : Type w) (default : String) :
    TableSignature.{u, 0, w} := ⟨key, String, default, table⟩

def emptyStringSignature (key : Type u) (table : Type w) :
    TableSignature.{u, 0, w} := ⟨key, String, "", table⟩

theorem stringSignature_payload (key : Type u) (table : Type w) (default : String) :
    (stringSignature key table default).Payload = String := rfl

theorem stringSignature_default (key : Type u) (table : Type w) (default : String) :
    (stringSignature key table default).default = default := rfl

theorem emptyStringSignature_default (key : Type u) (table : Type w) :
    (emptyStringSignature key table).default = "" := rfl

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
theorem abstract_carrier_empty_lookup {T : Type w}
    (table : Table String T) (law : TableLaws table "") :
    table.get 0 table.empty = "" := by
  fail_if_success have _ : T := SearchTrees.node SearchTrees.nil 0 "A" SearchTrees.nil
  fail_if_success exact rfl
  exact law.get_empty 0

theorem treeTable_empty_lookup : (treeTable "").get 0 (treeTable "").empty = "" :=
  abstract_carrier_empty_lookup (treeTable "") (treeTable_laws "")

/-! ## Constructive subtypes and the source's stored-length vectors -/

abbrev EvenNat := {n : Nat // Even n}

theorem even_two : Even (2 : Nat) := ⟨1, rfl⟩

def two : EvenNat := ⟨2, even_two⟩

def twoInline : EvenNat := by
  fail_if_success exact 2
  exact ⟨2, ⟨1, rfl⟩⟩

theorem two_data : two.val = 2 := rfl
theorem twoInline_data : twoInline.val = 2 := rfl
theorem plus_two : 1 + two.val = 3 := by
  fail_if_success have _ : 1 + two = 3 := rfl
  rfl

/-- Lean permits the standard subtype-to-Nat coercion when the Nat addition
is fixed explicitly; this is a language difference from the source command. -/
theorem plus_two_coercion : (1 : Nat) + two = 3 := rfl

theorem even_two_from_subtype : Even (2 : Nat) := two.property

namespace SubtypeExamples
abbrev Refinement {A : Type u} (P : A → Prop) := Subtype P
abbrev WitnessExists {A : Type u} (P : A → Prop) := Exists P

def pack {A : Type u} (P : A → Prop) (x : A) (proof : P x) : Refinement P := ⟨x, proof⟩

theorem witnessExists_intro {A : Type u} (P : A → Prop) (x : A) (proof : P x) : WitnessExists P :=
  ⟨x, proof⟩

def value {A : Type u} {P : A → Prop} (e : Refinement P) : A := e.val
theorem property {A : Type u} {P : A → Prop} (e : Refinement P) : P (value e) := e.property

/-- Propositional existence supports propositional elimination, while the
attempted executable witness projection is rejected in this generic context. -/
theorem exists_propositional_elimination {A : Type u} {P : A → Prop} {R : Prop}
    (e : WitnessExists P) (consequence : ∀ x, P x → R) : R := by
  fail_if_success
    have _ : A := match e with | ⟨x, _⟩ => x
  exact Exists.elim e consequence
end SubtypeExamples

abbrev StoredLengthVector (X : Type u) := {p : List X × Nat // p.1.length = p.2}

def exampleVector : StoredLengthVector Nat := ⟨([3, 1, 4], 3), rfl⟩

def vectorCons {X : Type u} (x : X) (v : StoredLengthVector X) : StoredLengthVector X :=
  ⟨(x :: v.val.1, v.val.2 + 1), by simp only [List.length_cons, v.property]⟩

def vectorToList {X : Type u} (v : StoredLengthVector X) : List X := v.val.1

theorem vectorToList_vectorCons (X : Type u) (x : X) (v : StoredLengthVector X) :
    vectorToList (vectorCons x v) = x :: vectorToList v := rfl

theorem vectorCons_length {X : Type u} (x : X) (v : StoredLengthVector X) :
    (vectorCons x v).val.2 = v.val.2 + 1 := rfl

def vectorAppend {X : Type u} (first second : StoredLengthVector X) : StoredLengthVector X :=
  ⟨(first.val.1 ++ second.val.1, first.val.2 + second.val.2), by
    simp only [List.length_append, first.property, second.property]⟩

theorem vectorToList_vectorAppend (X : Type u) (first second : StoredLengthVector X) :
    vectorToList (vectorAppend first second) =
      vectorToList first ++ vectorToList second := rfl

theorem vectorAppend_length {X : Type u} (first second : StoredLengthVector X) :
    (vectorAppend first second).val.2 = first.val.2 + second.val.2 := rfl

theorem vectorToList_length {X : Type u} (v : StoredLengthVector X) :
    (vectorToList v).length = v.val.2 := v.property

theorem exampleVector_append_data :
    vectorToList (vectorAppend (vectorCons 2 exampleVector) exampleVector) = [2, 3, 1, 4, 3, 1, 4] :=
  by rw [vectorToList_vectorAppend, vectorToList_vectorCons]; rfl

theorem exampleVector_append_length :
    (vectorAppend (vectorCons 2 exampleVector) exampleVector).val.2 = 7 :=
  by rw [vectorAppend_length, vectorCons_length]; rfl

/-! ## The source's Nat queue modules and shared FIFO client -/

abbrev Queue (V : Type v) (Q : Type w) := Sequences.SourceQueue.Ops V Q
abbrev QueueLaws {V : Type v} {Q : Type w} (ops : Queue V Q) :=
  Sequences.SourceQueue.Laws ops
abbrev QueueAbsLaws {V : Type v} {Q : Type w} (ops : Queue V Q) (Abs : Q → List V) :=
  Sequences.SourceQueue.AbsLaws ops Abs

namespace ListQueue
abbrev Value := Nat
abbrev Carrier := List Value
abbrev ops := Sequences.SourceQueue.lists Value
def empty : Carrier := ops.empty
def isEmpty (q : Carrier) : Bool := ops.isEmpty q
def enqueue (q : Carrier) (value : Value) : Carrier := ops.enqueue q value
def dequeue (q : Carrier) : Carrier := ops.dequeue q
def peek (default : Value) (q : Carrier) : Value := ops.peek default q

theorem isEmpty_empty : isEmpty empty = true :=
  (Sequences.SourceQueue.lists_laws Value).isEmpty_empty

theorem isEmpty_enqueue (q : Carrier) (value : Value) : isEmpty (enqueue q value) = false :=
  (Sequences.SourceQueue.lists_laws Value).isEmpty_enqueue q value

theorem peek_empty (default : Value) : peek default empty = default :=
  (Sequences.SourceQueue.lists_laws Value).peek_empty default

theorem peek_enqueue (default : Value) (q : Carrier) (value : Value) :
    peek default (enqueue q value) = peek value q :=
  (Sequences.SourceQueue.lists_laws Value).peek_enqueue default q value

theorem dequeue_empty : dequeue empty = empty :=
  (Sequences.SourceQueue.lists_laws Value).dequeue_empty

theorem dequeue_enqueue (q : Carrier) (value : Value) :
    dequeue (enqueue q value) = if isEmpty q then q else enqueue (dequeue q) value :=
  (Sequences.SourceQueue.lists_laws Value).dequeue_enqueue q value

theorem source_operations (default value : Value) (q : Carrier) :
    empty = [] ∧ isEmpty q = q.isEmpty ∧ enqueue q value = q ++ [value] ∧
      dequeue q = q.tail ∧ peek default q = q.headD default :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
end ListQueue

namespace TwoListQueue
abbrev Value := Nat
abbrev Carrier := Sequences.SourceQueue.TwoList Value
abbrev ops := Sequences.SourceQueue.twoLists Value
def empty : Carrier := ops.empty
def isEmpty (q : Carrier) : Bool := ops.isEmpty q
def enqueue (q : Carrier) (value : Value) : Carrier := ops.enqueue q value
def dequeue (q : Carrier) : Carrier := ops.dequeue q
def peek (default : Value) (q : Carrier) : Value := ops.peek default q
def decode (q : Carrier) : List Value := Sequences.SourceQueue.twoListDecode q

theorem decode_empty : decode empty = [] :=
  (Sequences.SourceQueue.twoLists_absLaws Value).empty

theorem decode_enqueue (q : Carrier) (value : Value) : decode (enqueue q value) = decode q ++ [value] :=
  (Sequences.SourceQueue.twoLists_absLaws Value).enqueue q value

theorem peek_eq_headD_decode (default : Value) (q : Carrier) : peek default q = (decode q).headD default :=
  (Sequences.SourceQueue.twoLists_absLaws Value).peek default q

theorem decode_dequeue (q : Carrier) : decode (dequeue q) = (decode q).tail :=
  (Sequences.SourceQueue.twoLists_absLaws Value).dequeue q

/-- This concrete theorem is additional to the four-law QueueAbs signature. -/
theorem isEmpty_eq_isEmpty_decode (q : Carrier) : isEmpty q = (decode q).isEmpty :=
  Sequences.SourceQueue.twoListIsEmpty_decode q
end TwoListQueue

def queueCommands : List (Sequences.AbstractFIFO.Command Nat) :=
  [.enqueue 7, .enqueue 8, .delete, .enqueue 9]

theorem queue_source_client :
    Sequences.AbstractFIFO.client (Sequences.SourceQueue.twoListFIFO Nat)
      queueCommands TwoListQueue.empty = some 8 :=
  Sequences.SourceQueue.twoList_client_empty queueCommands

theorem queue_source_peek_client :
    TwoListQueue.peek 0
      (Sequences.AbstractFIFO.run (Sequences.SourceQueue.twoListFIFO Nat)
        queueCommands TwoListQueue.empty) = 8 := by
  exact Sequences.SourceQueue.twoList_peek_run 0 queueCommands TwoListQueue.empty

theorem queue_branches :
    TwoListQueue.peek 99 ([], []) = 99 ∧
      TwoListQueue.peek 99 ([], [2, 1]) = 1 ∧
      TwoListQueue.dequeue ([], [2, 1]) = ([2], []) ∧
      TwoListQueue.peek 99 ([1], [2]) = 1 ∧
      TwoListQueue.dequeue ([1], [2]) = ([], [2]) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem queue_abs_does_not_imply_raw_laws :
    QueueAbsLaws TwoListQueue.ops TwoListQueue.decode ∧
      ¬ QueueLaws TwoListQueue.ops :=
  ⟨Sequences.SourceQueue.twoLists_absLaws Nat, Sequences.SourceQueue.twoLists_not_laws⟩

theorem queue_abs_does_not_constrain_empty_test :
    QueueAbsLaws { ListQueue.ops with isEmpty := fun _ => false } id ∧
      ({ ListQueue.ops with isEmpty := fun _ => false } : Queue Nat (List Nat)).isEmpty [] = false :=
  Sequences.SourceQueue.model_empty_test_unconstrained Nat

/-- The generic table operations need no equality or order on stored types. -/
theorem type_valued_table (default value : Type u) (key : Nat) :
    (functionTable default).get key ((functionTable default).set key value (functionTable default).empty) = value :=
  (functionTable_laws default).get_set_same key value _ trivial

/-! ## Validity carried by tree and unique-list subtypes -/

namespace ValidTreeTable
abbrev Carrier (V : Type v) := OrderedMap.Tree Nat V
abbrev ops {V : Type v} (default : V) := OrderedMap.EnumeratedTable.treeTable (κ := Nat) default
def empty {V : Type v} : Carrier V := (OrderedMap.trees Nat V).empty
def get {V : Type v} (default : V) (key : Nat) (t : Carrier V) : V :=
  (ops default).get key t
def set {V : Type v} (key : Nat) (value : V) (t : Carrier V) : Carrier V :=
  (OrderedMap.trees Nat V).bind key value t
def bound {V : Type v} (key : Nat) (t : Carrier V) : Bool :=
  OrderedMap.EnumeratedTable.treeObservations.bound key t
def elements {V : Type v} (t : Carrier V) : List (Nat × V) :=
  OrderedMap.EnumeratedTable.treeObservations.elements t

theorem laws {V : Type v} (default : V) :
    OrderedMap.EnumeratedTable.SubsetLaws (ops default)
      OrderedMap.EnumeratedTable.treeObservations default :=
  OrderedMap.EnumeratedTable.tree_laws default

theorem get_empty_default {V : Type v} (default : V) (key : Nat) :
    get default key empty = default := (laws default).table_laws.get_empty key

theorem get_set_same {V : Type v} (default value : V) (key : Nat) (t : Carrier V) :
    get default key (set key value t) = value :=
  (laws default).table_laws.get_set_same key value t trivial

theorem get_set_other {V : Type v} (default value : V) (key query : Nat) (t : Carrier V)
    (different : key ≠ query) : get default query (set key value t) = get default query t :=
  (laws default).table_laws.get_set_other key query value t different trivial

theorem bound_empty {V : Type v} (key : Nat) : bound key (empty : Carrier V) = false := by
  rfl

theorem bound_set_same {V : Type v} (key : Nat) (value : V) (t : Carrier V) :
    bound key (set key value t) = true := (laws value).bound_set_same key value t

theorem bound_set_other {V : Type v} (key query : Nat) (value : V) (t : Carrier V)
    (different : key ≠ query) : bound query (set key value t) = bound query t :=
  (laws value).bound_set_other key query value t different

theorem elements_complete {V : Type v} (default value : V) (key : Nat) (t : Carrier V)
    (present : bound key t = true) (found : get default key t = value) :
    (key, value) ∈ elements t :=
  (laws default).elements_complete key value t trivial present found

theorem elements_correct {V : Type v} (default value : V) (key : Nat) (t : Carrier V)
    (member : (key, value) ∈ elements t) :
    bound key t = true ∧ get default key t = value :=
  (laws default).elements_correct key value t trivial member

theorem elements_source {V : Type v} (t : Carrier V) :
    elements t = SearchTrees.elements t.val := rfl

theorem unrestricted_enumeration_laws {V : Type v} (default : V) :
    OrderedMap.EnumeratedTable.UnrestrictedEnumerationLaws (ops default)
      OrderedMap.EnumeratedTable.treeObservations default := (laws default).unrestrictedEnumerationLaws
end ValidTreeTable

namespace UniqueListTable
abbrev Carrier (V : Type v) := OrderedMap.AssociationListEnumeration.UniqueList Nat V
abbrev ops {V : Type v} (default : V) :=
  OrderedMap.EnumeratedTable.uniqueListTable (κ := Nat) default
def empty {V : Type v} : Carrier V := OrderedMap.AssociationListEnumeration.empty
def get {V : Type v} (default : V) (key : Nat) (t : Carrier V) : V := (ops default).get key t
def set {V : Type v} (key : Nat) (value : V) (t : Carrier V) : Carrier V :=
  OrderedMap.AssociationListEnumeration.set key value t
def bound {V : Type v} (key : Nat) (t : Carrier V) : Bool :=
  OrderedMap.EnumeratedTable.uniqueListObservations.bound key t
def elements {V : Type v} (t : Carrier V) : List (Nat × V) := t.val

theorem laws {V : Type v} (default : V) :
    OrderedMap.EnumeratedTable.SubsetLaws (ops default)
      OrderedMap.EnumeratedTable.uniqueListObservations default :=
  OrderedMap.EnumeratedTable.uniqueList_laws default

theorem elements_identity {V : Type v} (t : Carrier V) : elements t = t.val := rfl

theorem elements_set {V : Type v} (key : Nat) (value : V) (t : Carrier V) :
    elements (set key value t) =
      (key, value) :: t.val.eraseP (fun binding => decide (key = binding.1)) :=
  OrderedMap.AssociationListEnumeration.set_entries key value t

theorem unrestricted_enumeration_laws {V : Type v} (default : V) :
    OrderedMap.EnumeratedTable.UnrestrictedEnumerationLaws (ops default)
      OrderedMap.EnumeratedTable.uniqueListObservations default := (laws default).unrestrictedEnumerationLaws

theorem complete {V : Type v} (default value : V) (key : Nat) (t : Carrier V)
    (present : bound key t = true) (found : get default key t = value) :
    (key, value) ∈ elements t :=
  (laws default).elements_complete key value t trivial present found

theorem correct {V : Type v} (default value : V) (key : Nat) (t : Carrier V)
    (member : (key, value) ∈ elements t) :
    bound key t = true ∧ get default key t = value :=
  (laws default).elements_correct key value t trivial member
end UniqueListTable

def uniqueUnsorted : UniqueListTable.Carrier String :=
  ⟨[(2, "two"), (0, "zero"), (1, "one")], by decide⟩

theorem unique_unsorted_is_legal :
    (UniqueListTable.elements uniqueUnsorted).map Prod.fst = [2, 0, 1] ∧
      ((UniqueListTable.elements uniqueUnsorted).map Prod.fst).Nodup ∧
      ¬ ((UniqueListTable.elements uniqueUnsorted).map Prod.fst).Pairwise (· < ·) :=
  ⟨rfl, uniqueUnsorted.property, by decide⟩

theorem unique_replacement_entries :
    UniqueListTable.elements (UniqueListTable.set 0 "new" uniqueUnsorted) =
      [(0, "new"), (2, "two"), (1, "one")] := by
  rw [UniqueListTable.elements_set]
  rfl

theorem unique_replacement_lookup :
    UniqueListTable.get "" 0 (UniqueListTable.set 0 "new" uniqueUnsorted) = "new" :=
  (UniqueListTable.laws "").table_laws.get_set_same 0 "new" uniqueUnsorted trivial

theorem unique_other_lookup :
    UniqueListTable.get "" 1 (UniqueListTable.set 0 "new" uniqueUnsorted) = "one" :=
  (UniqueListTable.laws "").table_laws.get_set_other 0 1 "new" uniqueUnsorted (by decide) trivial

/-- The stored pair list is connected to the existing AList operation itself. -/
theorem unique_update_aList_bridge :
    OrderedMap.AssociationListEnumeration.toAList (UniqueListTable.set 0 "new" uniqueUnsorted) =
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
    (t : UniqueListTable.Carrier V) :
    UniqueListTable.set key last (UniqueListTable.set key first t) = UniqueListTable.set key last t :=
  OrderedMap.AssociationListEnumeration.set_shadow key first last t

theorem subset_client_results :
    clientResult (ValidTreeTable.ops "") = ["", "B", ""] ∧
      clientResult (UniqueListTable.ops "") = ["", "B", ""] :=
  ⟨clientResult_correct _ (ValidTreeTable.laws "").table_laws,
    clientResult_correct _ (UniqueListTable.laws "").table_laws⟩

theorem tree_subset_source_member :
    (0, "A") ∈ ValidTreeTable.elements
      (ValidTreeTable.set 0 "A" (ValidTreeTable.set 1 "B" ValidTreeTable.empty)) :=
  (ValidTreeTable.laws "").mem_elements_set 0 "A" trivial

theorem model_repeated_history_checked :
    ShadowingListModel.meaning (TotalTable.setAll (listTable "") clientWrites [(0, "old")]) =
        OrderedMap.writeAll clientWrites (ShadowingListModel.meaning [(0, "old")]) ∧
      SearchTrees.enumerationMeaning (TotalTable.setAll (treeTable "") clientWrites (treeTable "").empty) =
        OrderedMap.writeAll clientWrites (SearchTrees.enumerationMeaning (treeTable "").empty) ∧
      SearchTrees.structuralMeaning (TotalTable.setAll (treeTable "") clientWrites (treeTable "").empty) =
        OrderedMap.writeAll clientWrites (SearchTrees.structuralMeaning (treeTable "").empty) :=
  ⟨raw_list_model_history "" clientWrites [(0, "old")],
    both_tree_model_histories "" clientWrites _ (RawTreeTable.empty_valid "")⟩

end Examples.AbstractDataTypes
