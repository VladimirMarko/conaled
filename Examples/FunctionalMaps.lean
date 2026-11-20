import Applications.Search.OrderedMap.FunctionUpdate
import Applications.Search.OrderedMap.TotalTable
import Applications.Search.OrderedMap.AssociationList
import Applications.Dijkstra.Store

/-!
# Total and partial function maps

These are the exact Nat-key function spaces and statements of VFA 2.1 Maps.
The total update algebra comes from `Function.update`; the partial laws
specialize it at `Option` values. Both spaces admit arbitrary functions,
without a finite-support condition. Lookup is function application, and
extensional equality is a proof principle, not a map-equality algorithm.

The final clients retain the source example's write of the default at key 1,
separate absence from a stored default, and connect function updates to total
tables and Dijkstra's finite Vector store. These observation equalities make
no claim about evaluation cost or equality of raw representations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FunctionalMaps

universe u v w

abbrev total_map (A : Type v) := Nat → A

def t_empty {A : Type v} (value : A) : total_map A := fun _ => value

abbrev t_update {A : Type v} (m : total_map A) (x : Nat) (value : A) : total_map A :=
  Function.update m x value

/-- The exact Boolean branch in the source uses written key, then query. -/
theorem t_update_source {A : Type v} (m : total_map A) (x : Nat) (value : A) :
    t_update m x value = fun query => if x == query then value else m query :=
  Search.OrderedMap.update_nat_source m x value

def examplemap : total_map Bool :=
  t_update (t_update (t_empty false) 1 false) 3 true

/- The six standard source exercises retain their original quantifier and
key/value order. No order or equality on payloads is assumed. -/
theorem t_apply_empty (A : Type v) (x : Nat) (value : A) :
    t_empty value x = value := rfl

theorem t_update_eq (A : Type v) (m : total_map A) (x : Nat) (value : A) :
    t_update m x value x = value :=
  Function.update_self x value m

theorem t_update_neq (X : Type v) (value : X) (x₁ x₂ : Nat) (m : total_map X)
    (different : x₁ ≠ x₂) : t_update m x₁ value x₂ = m x₂ :=
  Function.update_of_ne (Ne.symm different) value m

theorem t_update_shadow (A : Type v) (m : total_map A) (first last : A) (x : Nat) :
    t_update (t_update m x first) x last = t_update m x last :=
  Function.update_idem first last m

theorem t_update_same (X : Type v) (x : Nat) (m : total_map X) :
    t_update m x (m x) = m :=
  Function.update_eq_self x m

theorem t_update_permute (X : Type v) (v₁ v₂ : X) (x₁ x₂ : Nat) (m : total_map X)
    (different : x₂ ≠ x₁) :
    t_update (t_update m x₂ v₂) x₁ v₁ = t_update (t_update m x₁ v₁) x₂ v₂ :=
  Function.update_comm different v₂ v₁ m

theorem update_example1 : examplemap 0 = false := by
  unfold examplemap
  rw [t_update_neq Bool true 3 0 _ (by decide),
    t_update_neq Bool false 1 0 _ (by decide)]
  exact t_apply_empty Bool 0 false

theorem update_example2 : examplemap 1 = false := by
  unfold examplemap
  rw [t_update_neq Bool true 3 1 _ (by decide)]
  exact t_update_eq Bool (t_empty false) 1 false

theorem update_example3 : examplemap 2 = false := by
  unfold examplemap
  rw [t_update_neq Bool true 3 2 _ (by decide),
    t_update_neq Bool false 1 2 _ (by decide)]
  exact t_apply_empty Bool 2 false

theorem update_example4 : examplemap 3 = true :=
  t_update_eq Bool (t_update (t_empty false) 1 false) 3 true

abbrev partial_map (A : Type v) := total_map (Option A)

def empty {A : Type v} : partial_map A := t_empty none

abbrev update {A : Type v} (m : partial_map A) (x : Nat) (value : A) : partial_map A :=
  t_update m x (some value)

theorem update_eq_write {A : Type v} (m : partial_map A) (x : Nat) (value : A) :
    update m x value = Search.OrderedMap.write x value m :=
  (Search.OrderedMap.write_eq_update x value m).symm

theorem apply_empty (A : Type v) (x : Nat) : (empty : partial_map A) x = none :=
  t_apply_empty (Option A) x none

theorem update_eq (A : Type v) (m : partial_map A) (x : Nat) (value : A) :
    update m x value x = some value :=
  t_update_eq (Option A) m x (some value)

/-- In this source statement the written key is `x₂` and the query is `x₁`. -/
theorem update_neq (X : Type v) (value : X) (x₁ x₂ : Nat) (m : partial_map X)
    (different : x₂ ≠ x₁) : update m x₂ value x₁ = m x₁ :=
  t_update_neq (Option X) (some value) x₂ x₁ m different

theorem update_shadow (A : Type v) (m : partial_map A) (first last : A) (x : Nat) :
    update (update m x first) x last = update m x last :=
  t_update_shadow (Option A) m (some first) (some last) x

theorem update_same (X : Type v) (value : X) (x : Nat) (m : partial_map X)
    (bound : m x = some value) : update m x value = m := by
  change t_update m x (some value) = m
  rw [← bound]
  exact t_update_same (Option X) x m

theorem update_permute (X : Type v) (v₁ v₂ : X) (x₁ x₂ : Nat) (m : partial_map X)
    (different : x₂ ≠ x₁) :
    update (update m x₂ v₂) x₁ v₁ = update (update m x₁ v₁) x₂ v₂ :=
  t_update_permute (Option X) (some v₁) (some v₂) x₁ x₂ m different

/-! ## Boundary and observation clients -/

/-- The commutation premise is material: two different values at one key
leave different observations when their write order is reversed. -/
theorem same_key_different_writes (m : total_map Bool) (key : Nat) :
    t_update (t_update m key false) key true ≠
      t_update (t_update m key true) key false := by
  intro same
  have impossible : (true : Bool) = false := by
    simpa only [t_update_eq] using congrFun same key
  contradiction

theorem partial_repeated_write {A : Type v} (m : partial_map A) (key : Nat)
    (first last : A) : update (update m key first) key last = update m key last := by
  simpa only [update_eq_write] using
    Search.OrderedMap.write_shadow m key first last

/-- Bool keys need only their computable equality, and values remain arbitrary. -/
theorem bool_key_writes_commute {A : Type v} (m : Bool → Option A) (a b : A) :
    Search.OrderedMap.write true b (Search.OrderedMap.write false a m) =
      Search.OrderedMap.write false a (Search.OrderedMap.write true b m) :=
  Search.OrderedMap.write_comm m false true a b (by decide)

def storedDefault : partial_map Bool := update empty 3 false

theorem storedDefault_ne_empty : storedDefault ≠ (empty : partial_map Bool) := by
  intro same
  have bound : (empty : partial_map Bool) 3 = some false :=
    (Search.OrderedMap.write_eq_self_iff empty 3 false).mp
      (by simpa only [storedDefault, update_eq_write] using same)
  rw [apply_empty Bool 3] at bound
  contradiction

theorem storedDefault_same_total_observation :
    Search.OrderedMap.withDefault false storedDefault =
      Search.OrderedMap.withDefault false (empty : partial_map Bool) := by
  change Search.OrderedMap.withDefault false (Function.update empty 3 (some false)) = _
  rw [Search.OrderedMap.withDefault_update]
  exact Function.update_eq_self 3 (Search.OrderedMap.withDefault false empty)

theorem storedDefault_presence :
    Search.OrderedMap.hasBinding storedDefault 3 = true ∧
      Search.OrderedMap.hasBinding (empty : partial_map Bool) 3 = false := by
  constructor
  · change Search.OrderedMap.hasBinding (update empty 3 false) 3 = true
    rw [update_eq_write, Search.OrderedMap.hasBinding_write, Function.update_self]
  · rfl

/-- Empty partial maps do not require an inhabited payload type. -/
theorem empty_payload (key : Nat) : (empty : partial_map Empty) key = none :=
  apply_empty Empty key

/-- A payload may itself be optional: a stored `none` remains a present binding. -/
theorem optional_payload : update (empty : partial_map (Option Nat)) 5 none 5 = some none :=
  update_eq (Option Nat) empty 5 none

/-- The source carrier accepts functions bound at every Nat key. -/
theorem unrestricted_partial_function (query : Nat) :
    (fun key => some key : partial_map Nat) query = some query := rfl

/-! ## Existing total-table and finite-store compositions -/

theorem examplemap_eq_table_client :
    examplemap = Search.TotalTable.setAll (Search.TotalTable.functions false)
      [(1, false), (3, true)] (Search.TotalTable.functions false).empty := rfl

/-- The same two-write client uses the existing total-table law at an arbitrary
valid initial state. The representation and its validity predicate stay explicit. -/
theorem table_two_writes {κ : Type u} {A : Type v} {T : Type w} [DecidableEq κ]
    {ops : Search.TotalTable.Ops κ A T} {default : A} {Valid : T → Prop}
    (law : Search.TotalTable.Laws ops default Valid) (k₁ k₂ : κ) (v₁ v₂ : A)
    {t : T} (valid : Valid t) :
    Search.TotalTable.observe ops (Search.TotalTable.setAll ops [(k₁, v₁), (k₂, v₂)] t) =
      Function.update (Function.update (Search.TotalTable.observe ops t) k₁ v₁) k₂ v₂ :=
  law.observe_setAll [(k₁, v₁), (k₂, v₂)] valid

/-- First-binding association lists and the source function have the same
total observation after the exact source history, including its default write. -/
theorem examplemap_eq_list_client :
    examplemap = Search.TotalTable.observe
      (Search.TotalTable.ofPartial (Search.OrderedMap.lists Nat Bool) false)
      (Search.TotalTable.setAll
        (Search.TotalTable.ofPartial (Search.OrderedMap.lists Nat Bool) false)
        [(1, false), (3, true)] []) := by
  have h := Search.TotalTable.Laws.setAll_agrees
    (Search.TotalTable.functions_laws (κ := Nat) false)
    (Search.TotalTable.ofPartial_unrestricted
      (Search.OrderedMap.lists_laws (κ := Nat) (ν := Bool)) false)
    [(1, false), (3, true)] (t := t_empty false) (s := [])
    trivial trivial (by rfl)
  exact h

/-- The finite Vector carrier decodes to a function on `Fin n`; this does not
identify it with the unrestricted Nat-key source carrier. -/
theorem store_write_decode {A : Type v} {n : Nat} (a : Dijkstra.Store.Store n A)
    (key : Fin n) (value : A) :
    (fun query => Dijkstra.Store.lookup (Dijkstra.Store.write a key value) query) =
      Function.update (fun query => Dijkstra.Store.lookup a query) key value := by
  funext query
  rw [Dijkstra.Store.lookup_write, Search.OrderedMap.update_apply_written]

theorem store_write_shadow {A : Type v} {n : Nat} (a : Dijkstra.Store.Store n A)
    (key : Fin n) (first last : A) :
    (fun query => Dijkstra.Store.lookup
      (Dijkstra.Store.write (Dijkstra.Store.write a key first) key last) query) =
      (fun query => Dijkstra.Store.lookup (Dijkstra.Store.write a key last) query) := by
  simp only [store_write_decode]
  exact Function.update_idem first last (fun query => Dijkstra.Store.lookup a query)

theorem store_distinct_writes {A : Type v} {n : Nat} (a : Dijkstra.Store.Store n A)
    (first second : Fin n) (x y : A) (different : first ≠ second) :
    (fun query => Dijkstra.Store.lookup
      (Dijkstra.Store.write (Dijkstra.Store.write a first x) second y) query) =
      (fun query => Dijkstra.Store.lookup
        (Dijkstra.Store.write (Dijkstra.Store.write a second y) first x) query) := by
  simp only [store_write_decode]
  exact Function.update_comm different x y (fun query => Dijkstra.Store.lookup a query)

def storeSample : Dijkstra.Store.Store 3 Nat := ⟨#[10, 20, 30], rfl⟩

theorem store_sample_written :
    Dijkstra.Store.lookup
      (Dijkstra.Store.write (Dijkstra.Store.write storeSample 1 99) 1 7) 1 = 7 := by
  have shadow := congrFun (store_write_shadow storeSample 1 99 7) 1
  have observed := congrFun (store_write_decode storeSample 1 7) 1
  exact shadow.trans (observed.trans (Function.update_self 1 7 _))

theorem store_sample_unchanged :
    Dijkstra.Store.lookup
      (Dijkstra.Store.write (Dijkstra.Store.write storeSample 1 99) 1 7) 0 = 10 := by
  have shadow := congrFun (store_write_shadow storeSample 1 99 7) 0
  have observed := congrFun (store_write_decode storeSample 1 7) 0
  calc
    _ = Function.update (fun query => Dijkstra.Store.lookup storeSample query) 1 7 0 :=
      shadow.trans observed
    _ = Dijkstra.Store.lookup storeSample 0 :=
      Function.update_of_ne (by decide) 7 _
    _ = 10 := rfl

end Examples.FunctionalMaps
