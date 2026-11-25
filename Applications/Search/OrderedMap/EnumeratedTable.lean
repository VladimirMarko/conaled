import Applications.Search.OrderedMap.TotalTable
import Applications.Search.OrderedMap.SourceModel
import Applications.Search.OrderedMap.AssociationListEnumeration

/-!
# Enumerated tables with algebraic and model contracts

VFA ADT distinguishes unconditional total-table and presence laws from
validity-dependent enumeration. Its model-only interface has seven separate
laws and admits raw lists containing shadowed entries. The final subset
interface puts validity in the carrier. None of these contracts identifies an
absent binding with an explicitly stored default.

The realizations reuse the existing function, association-list and search-tree
operations. Both independently proved SearchTree abstraction routes are kept.
Abstract clients consume operation and law parameters; a Lean namespace does
not assert Rocq module sealing.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap.EnumeratedTable

universe u v w
variable {κ : Type u} {ν : Type v} {T : Type w}

/-- Additional observations do not duplicate the existing total-table operations. -/
structure Observations (κ : Type u) (ν : Type v) (T : Type w) where
  bound : κ → T → Bool
  elements : T → List (κ × ν)

/-- The initial source signature is realizable by valid carriers, although the
attempted unrestricted raw-tree realization cannot supply its soundness field. -/
structure UnrestrictedEnumerationLaws (table : TotalTable.Ops κ ν T)
    (obs : Observations κ ν T) (default : ν) : Prop where
  table_laws : TotalTable.Laws table default (fun _ => True)
  elements_complete : ∀ key value t, obs.bound key t = true → table.get key t = value →
    (key, value) ∈ obs.elements t
  elements_correct : ∀ key value t, (key, value) ∈ obs.elements t →
    obs.bound key t = true ∧ table.get key t = value

/-- Only enumeration uses `Valid`; every base-table and bound law is raw. -/
structure Laws (table : TotalTable.Ops κ ν T) (obs : Observations κ ν T)
    (default : ν) (Valid : T → Prop) : Prop where
  table_laws : TotalTable.Laws table default (fun _ => True)
  empty_valid : Valid table.empty
  set_valid : ∀ key value t, Valid t → Valid (table.set key value t)
  bound_empty : ∀ key, obs.bound key table.empty = false
  bound_set_same : ∀ key value t, obs.bound key (table.set key value t) = true
  bound_set_other : ∀ key query value t, key ≠ query →
    obs.bound query (table.set key value t) = obs.bound query t
  elements_complete : ∀ key value t, Valid t → obs.bound key t = true →
    table.get key t = value → (key, value) ∈ obs.elements t
  elements_correct : ∀ key value t, Valid t → (key, value) ∈ obs.elements t →
    obs.bound key t = true ∧ table.get key t = value

/-- No public representation predicate remains when validity is in the carrier. -/
abbrev SubsetLaws (table : TotalTable.Ops κ ν T) (obs : Observations κ ν T)
    (default : ν) := Laws table obs default (fun _ => True)

theorem SubsetLaws.unrestrictedEnumerationLaws {table : TotalTable.Ops κ ν T}
    {obs : Observations κ ν T} {default : ν} (h : SubsetLaws table obs default) :
    UnrestrictedEnumerationLaws table obs default where
  table_laws := h.table_laws
  elements_complete key value t := h.elements_complete key value t trivial
  elements_correct key value t := h.elements_correct key value t trivial

/-- The optional strengthening retains the stronger raw inverse-correctness
scope. Uniqueness concerns projected keys, and order compares only keys. -/
structure StrongElements [LT κ] (obs : Observations κ ν T) (Valid : T → Prop) : Prop where
  absent_no_entry : ∀ key t, Valid t → obs.bound key t = false →
    ∀ value, (key, value) ∉ obs.elements t
  no_entry_absent : ∀ key t, (∀ value, (key, value) ∉ obs.elements t) →
    obs.bound key t = false
  keys_sorted : ∀ t, Valid t → ((obs.elements t).map Prod.fst).Pairwise (· < ·)
  keys_nodup : ∀ t, Valid t → ((obs.elements t).map Prod.fst).Nodup

/-- This is the source's distinct seven-law model contract. In particular it
does not imply that every shadowed raw entry is a successful lookup. -/
structure ModelLaws [DecidableEq κ] (table : TotalTable.Ops κ ν T)
    (obs : Observations κ ν T) (default : ν) (Valid : T → Prop)
    (Abs : T → Meaning κ ν) : Prop where
  empty_valid : Valid table.empty
  set_valid : ∀ key value t, Valid t → Valid (table.set key value t)
  empty : Abs table.empty = fun _ => none
  bound : ∀ t key, Valid t → hasBinding (Abs t) key = obs.bound key t
  get : ∀ t key, Valid t → withDefault default (Abs t) key = table.get key t
  set : ∀ t key value, Valid t → write key value (Abs t) = Abs (table.set key value t)
  elements : ∀ t, Valid t → Abs t = listObserve (obs.elements t)

theorem Laws.mem_elements_set {table : TotalTable.Ops κ ν T}
    {obs : Observations κ ν T} {default : ν} {Valid : T → Prop}
    (h : Laws table obs default Valid) (key : κ) (value : ν) {t : T} (valid : Valid t) :
    (key, value) ∈ obs.elements (table.set key value t) :=
  h.elements_complete key value _ (h.set_valid key value t valid)
    (h.bound_set_same key value t) (h.table_laws.get_set_same key value t trivial)

theorem Laws.absent_no_entry {table : TotalTable.Ops κ ν T}
    {obs : Observations κ ν T} {default : ν} {Valid : T → Prop}
    (h : Laws table obs default Valid) (key : κ) {t : T} (valid : Valid t)
    (absent : obs.bound key t = false) (value : ν) : (key, value) ∉ obs.elements t := by
  intro member
  have present := (h.elements_correct key value t valid member).1
  rw [absent] at present
  cases present

section DecidableKeys
variable [DecidableEq κ]

theorem ModelLaws.totalTable_laws {table : TotalTable.Ops κ ν T}
    {obs : Observations κ ν T} {default : ν} {Valid : T → Prop}
    {Abs : T → Meaning κ ν} (h : ModelLaws table obs default Valid Abs) :
    TotalTable.Laws table default Valid where
  empty_valid := h.empty_valid
  set_valid := h.set_valid
  get_empty key := by
    rw [← h.get table.empty key h.empty_valid, h.empty]
    rfl
  get_set_same key value t valid := by
    rw [← h.get _ key (h.set_valid key value t valid), ← h.set t key value valid]
    simp [withDefault, write]
  get_set_other key query value t different valid := by
    rw [← h.get _ query (h.set_valid key value t valid), ← h.set t key value valid,
      ← h.get t query valid]
    simp [withDefault, write, Ne.symm different]

/-- The existing chronological client transports the exact partial model,
including presence; it does not merely identify default-valued observations. -/
theorem ModelLaws.setAll {table : TotalTable.Ops κ ν T}
    {obs : Observations κ ν T} {default : ν} {Valid : T → Prop}
    {Abs : T → Meaning κ ν} (h : ModelLaws table obs default Valid Abs)
    (writes : List (κ × ν)) {t : T} (valid : Valid t) :
    Abs (TotalTable.setAll table writes t) = writeAll writes (Abs t) := by
  induction writes generalizing t with
  | nil => rfl
  | cons binding rest ih =>
      rw [TotalTable.setAll, writeAll, ih (h.set_valid binding.1 binding.2 t valid),
        ← h.set t binding.1 binding.2 valid]

/-- Finiteness follows for each valid represented state. The ambient meaning
type still contains arbitrary partial functions and is not restricted. -/
theorem ModelLaws.finite_support {table : TotalTable.Ops κ ν T}
    {obs : Observations κ ν T} {default : ν} {Valid : T → Prop}
    {Abs : T → Meaning κ ν} (h : ModelLaws table obs default Valid Abs)
    {t : T} (valid : Valid t) :
    ∃ keys : List κ, ∀ key value, Abs t key = some value → key ∈ keys := by
  rw [h.elements t valid]
  exact SourceModel.listObserve_finite_support (obs.elements t)

def observationsOfPartial (ops : OrderedMap.Ops κ ν T)
    (elements : T → List (κ × ν)) : Observations κ ν T where
  bound key t := (ops.lookup key t).isSome
  elements := elements

/-- Reuse one partial-map algebra for the unconditional base and presence
laws; enumeration gets exactly its independently supplied premises. -/
theorem Laws.ofPartial (ops : OrderedMap.Ops κ ν T) (meaning : T → Meaning κ ν)
    (elements : T → List (κ × ν)) (default : ν) (Valid : T → Prop)
    (mapLaws : OrderedMap.Laws ops meaning)
    (empty_valid : Valid ops.empty)
    (set_valid : ∀ key value t, Valid t → Valid (ops.bind key value t))
    (complete : ∀ key value t, Valid t → ops.lookup key t = some value →
      (key, value) ∈ elements t)
    (correct : ∀ key value t, Valid t → (key, value) ∈ elements t →
      ops.lookup key t = some value) :
    Laws (TotalTable.ofPartial ops default) (observationsOfPartial ops elements) default Valid where
  table_laws := TotalTable.ofPartial_unrestricted mapLaws default
  empty_valid := empty_valid
  set_valid := set_valid
  bound_empty key := by
    change (ops.lookup key ops.empty).isSome = false
    rw [mapLaws.lookup, mapLaws.empty]
    rfl
  bound_set_same key value t := by
    change (ops.lookup key (ops.bind key value t)).isSome = true
    rw [mapLaws.lookup, mapLaws.bind]
    simp [write]
  bound_set_other key query value t different := by
    change (ops.lookup query (ops.bind key value t)).isSome = (ops.lookup query t).isSome
    rw [mapLaws.lookup, mapLaws.bind, mapLaws.lookup]
    simp [write, Ne.symm different]
  elements_complete key value t valid bound found :=
    complete key value t valid
      ((binding_iff default (fun query => ops.lookup query t) key value).mpr ⟨bound, found⟩)
  elements_correct key value t valid member :=
    (binding_iff default (fun query => ops.lookup query t) key value).mp
      (correct key value t valid member)

def rawListTable (default : ν) : TotalTable.Ops κ ν (List (κ × ν)) :=
  TotalTable.ofPartial (lists κ ν) default

def rawListObservations : Observations κ ν (List (κ × ν)) :=
  observationsOfPartial (lists κ ν) id

theorem rawList_table_laws (default : ν) :
    TotalTable.Laws (rawListTable (κ := κ) default) default (fun _ => True) :=
  TotalTable.ofPartial_unrestricted lists_laws default

theorem rawList_model (default : ν) :
    ModelLaws (rawListTable (κ := κ) default) rawListObservations default
      (fun _ => True) listObserve where
  empty_valid := trivial
  set_valid _ _ _ _ := trivial
  empty := rfl
  bound _ _ _ := rfl
  get _ _ _ := rfl
  set t key value _ := (lists_laws.bind key value t).symm
  elements _ _ := rfl

def uniqueListTable (default : ν) :
    TotalTable.Ops κ ν (AssociationListEnumeration.UniqueList κ ν) :=
  TotalTable.ofPartial AssociationListEnumeration.partialOps default

def uniqueListObservations :
    Observations κ ν (AssociationListEnumeration.UniqueList κ ν) :=
  observationsOfPartial AssociationListEnumeration.partialOps Subtype.val

theorem uniqueList_laws (default : ν) :
    SubsetLaws (uniqueListTable (κ := κ) default) uniqueListObservations default :=
  Laws.ofPartial AssociationListEnumeration.partialOps (fun t => listObserve t.1)
    Subtype.val default (fun _ => True) AssociationListEnumeration.partial_laws
    trivial (fun _ _ _ _ => trivial)
    (fun key value t _ found =>
      (AssociationListEnumeration.lookup_eq_some_iff_mem t key value).mp found)
    (fun key value t _ member =>
      (AssociationListEnumeration.lookup_eq_some_iff_mem t key value).mpr member)

theorem uniqueList_model (default : ν) :
    ModelLaws (uniqueListTable (κ := κ) default) uniqueListObservations default
      (fun _ => True) (fun t => listObserve t.1) where
  empty_valid := trivial
  set_valid _ _ _ _ := trivial
  empty := rfl
  bound _ _ _ := rfl
  get _ _ _ := rfl
  set t key value _ := (AssociationListEnumeration.partial_laws.bind key value t).symm
  elements _ _ := rfl

end DecidableKeys

section LinearOrder
variable [LinearOrder κ]

open Search.OrderedTree (OrderedBy entries)

def rawTreeTable (default : ν) : TotalTable.Ops κ ν (BinaryTree (κ × ν)) :=
  TotalTable.ofPartial (rawTrees κ ν) default

def rawTreeObservations : Observations κ ν (BinaryTree (κ × ν)) :=
  observationsOfPartial (rawTrees κ ν) entries

/-- The first attempted realization's completeness theorem is valid for every
raw tree; it never required the invariant that its soundness theorem needs. -/
theorem rawTree_elements_complete (default : ν) (key : κ) (value : ν)
    (t : BinaryTree (κ × ν)) (bound : rawTreeObservations.bound key t = true)
    (found : (rawTreeTable default).get key t = value) :
    (key, value) ∈ rawTreeObservations.elements t :=
  mem_entries_of_lookup ((binding_iff default (pathObserve t) key value).mpr ⟨bound, found⟩)

theorem rawTree_laws (default : ν) :
    Laws (rawTreeTable (κ := κ) default) rawTreeObservations default (OrderedBy Prod.fst) :=
  Laws.ofPartial (rawTrees κ ν) pathObserve entries default (OrderedBy Prod.fst)
    rawTrees_laws trivial (fun key value _ ordered => ordered_bind ordered key value)
    (fun _ _ _ _ found => mem_entries_of_lookup found)
    (fun key value _ ordered member =>
      (lookup_eq_some_iff_mem_entries ordered key value).mpr member)

theorem rawTree_strong :
    StrongElements (rawTreeObservations : Observations κ ν _) (OrderedBy Prod.fst) where
  absent_no_entry key t ordered absent value member := by
    have found := (lookup_eq_some_iff_mem_entries ordered key value).mpr member
    change (lookup key t).isSome = false at absent
    rw [found] at absent
    cases absent
  no_entry_absent key t absent := by
    change (lookup key t).isSome = false
    cases found : lookup key t with
    | none => rfl
    | some value => exact False.elim (absent value (mem_entries_of_lookup found))
  keys_sorted _ ordered := ordered_entries_keys_pairwise ordered
  keys_nodup _ ordered := ordered_entries_keys_nodup ordered

theorem rawTree_model_enum (default : ν) :
    ModelLaws (rawTreeTable (κ := κ) default) rawTreeObservations default
      (OrderedBy Prod.fst) SourceModel.enumAbs where
  empty_valid := trivial
  set_valid key value _ ordered := ordered_bind ordered key value
  empty := rfl
  bound _ key ordered := SourceModel.enumAbs_bound ordered key
  get _ key ordered := SourceModel.enumAbs_default ordered default key
  set _ key value ordered := (SourceModel.enumAbs_bind ordered key value).symm
  elements _ _ := rfl

/-- Search and update refinement here use the independent structural proofs;
only the elements field needs the established agreement with enumeration. -/
theorem rawTree_model_structural (default : ν) :
    ModelLaws (rawTreeTable (κ := κ) default) rawTreeObservations default
      (OrderedBy Prod.fst) SourceModel.mapOfTree where
  empty_valid := trivial
  set_valid key value _ ordered := ordered_bind ordered key value
  empty := rfl
  bound _ key ordered := SourceModel.mapOfTree_bound ordered key
  get _ key ordered := SourceModel.mapOfTree_default ordered default key
  set _ key value ordered := (SourceModel.mapOfTree_bind ordered key value).symm
  elements _ ordered := (SourceModel.enumAbs_eq_mapOfTree ordered).symm

def treeTable (default : ν) : TotalTable.Ops κ ν (Tree κ ν) :=
  TotalTable.ofPartial (trees κ ν) default

def treeObservations : Observations κ ν (Tree κ ν) :=
  observationsOfPartial (trees κ ν) (fun t => entries t.1)

theorem tree_laws (default : ν) :
    SubsetLaws (treeTable (κ := κ) default) treeObservations default :=
  Laws.ofPartial (trees κ ν) decode (fun t => entries t.1) default (fun _ => True)
    trees_laws trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ _ found => mem_entries_of_lookup found)
    (fun key value t _ member =>
      (lookup_eq_some_iff_mem_entries t.2 key value).mpr member)

theorem tree_strong :
    StrongElements (treeObservations : Observations κ ν _) (fun _ => True) where
  absent_no_entry key t _ := rawTree_strong.absent_no_entry key t.1 t.2
  no_entry_absent key t := rawTree_strong.no_entry_absent key t.1
  keys_sorted t _ := rawTree_strong.keys_sorted t.1 t.2
  keys_nodup t _ := rawTree_strong.keys_nodup t.1 t.2

end LinearOrder
end Search.OrderedMap.EnumeratedTable
