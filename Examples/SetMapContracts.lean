import Applications.Collections.AList
import Applications.Collections.Set
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.List.AList
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Function.Basic

/-! Connected Set/Map clients, valid hidden-state realizations, and the actual
finite association-list adapter. Independent calculations and source/statement
assessment: `docs/research/fdsa-adt-refinement.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace SetMapContractExamples
open Collections
universe u v
variable {α : Type u} {β : Type v}

abbrev MapState (α : Type u) (β : Type v) := (α → Option β) × Nat

def pairedMapValid (m : MapState α β) : Prop := Even m.2

def pairedMapEmpty (α : Type u) (β : Type v) : MapState α β := (fun _ => none, 0)

def pairedMapUpdate [DecidableEq α] (a : α) (b : β) (m : MapState α β) :
    MapState α β := (Function.update m.1 a (some b), m.2 + 2)

def pairedMapDelete [DecidableEq α] (a : α) (m : MapState α β) : MapState α β :=
  (Function.update m.1 a none, m.2 + 2)

def pairedMapLookup (m : MapState α β) : α → Option β := m.1

theorem pairedMapEmpty_valid : pairedMapValid (pairedMapEmpty α β) :=
  ⟨0, rfl⟩

theorem pairedMapUpdate_valid [DecidableEq α] (a : α) (b : β) (m : MapState α β)
    (h : pairedMapValid m) : pairedMapValid (pairedMapUpdate a b m) :=
  h.add (show Even (2 : Nat) from ⟨1, rfl⟩)

theorem pairedMapDelete_valid [DecidableEq α] (a : α) (m : MapState α β)
    (h : pairedMapValid m) : pairedMapValid (pairedMapDelete a m) :=
  h.add (show Even (2 : Nat) from ⟨1, rfl⟩)

theorem pairedMap_odd_invalid (m : α → Option β) : ¬ pairedMapValid (m, 1) :=
  Nat.not_even_one

def mapModel (α : Type u) (β : Type v) [DecidableEq α] :
    Collections.Maps.Ops α β (α → Option β) where
  empty := fun _ => none
  update a b m := Function.update m a (some b)
  delete a m := Function.update m a none
  lookup := id

theorem mapModel_laws (α : Type u) (β : Type v) [DecidableEq α] :
    Collections.Maps.Laws (mapModel α β) (fun _ => True) where
  empty_lookup := rfl
  empty_valid := True.intro
  update_lookup a b m _ :=
    ⟨Function.update_self a (some b) m, fun _ hk => Function.update_of_ne hk (some b) m⟩
  update_valid _ _ _ _ := True.intro
  delete_lookup a m _ :=
    ⟨Function.update_self a none m, fun _ hk => Function.update_of_ne hk none m⟩
  delete_valid _ _ _ := True.intro

def pairedMap (α : Type u) (β : Type v) [DecidableEq α] :
    Collections.Maps.Ops α β (MapState α β) where
  empty := pairedMapEmpty α β
  update := pairedMapUpdate
  delete := pairedMapDelete
  lookup := pairedMapLookup

theorem pairedMap_laws (α : Type u) (β : Type v) [DecidableEq α] :
    Collections.Maps.Laws (pairedMap α β) pairedMapValid where
  empty_lookup := rfl
  empty_valid := pairedMapEmpty_valid
  update_lookup a b m _ :=
    ⟨Function.update_self a (some b) m.1,
      fun _ hk => Function.update_of_ne hk (some b) m.1⟩
  update_valid := pairedMapUpdate_valid
  delete_lookup a m _ :=
    ⟨Function.update_self a none m.1, fun _ hk => Function.update_of_ne hk none m.1⟩
  delete_valid := pairedMapDelete_valid

def setDecode (s : α → Bool) : Set α := {a | s a = true}

theorem setDecode_empty : setDecode (fun _ : α => false) = ∅ := by
  ext a
  simp [setDecode]

theorem setDecode_insert [DecidableEq α] (s : α → Bool) (a : α) :
    setDecode (Function.update s a true) = setDecode s ∪ {a} := by
  ext x
  by_cases h : x = a
  · subst x
    simp [setDecode]
  · change (Function.update s a true x = true) ↔ (s x = true ∨ x = a)
    rw [Function.update_of_ne h]
    simp [h]

theorem setDecode_delete [DecidableEq α] (s : α → Bool) (a : α) :
    setDecode (Function.update s a false) = setDecode s \ {a} := by
  ext x
  by_cases h : x = a
  · subst x
    simp [setDecode]
  · change (Function.update s a false x = true) ↔ (s x = true ∧ x ≠ a)
    rw [Function.update_of_ne h]
    simp [h]

abbrev SetState (α : Type u) := (α → Bool) × Nat

def pairedSetValid (s : SetState α) : Prop := Even s.2

def pairedSetDecode (s : SetState α) : Set α := setDecode s.1

def pairedSetEmpty (α : Type u) : SetState α := (fun _ => false, 0)

def pairedSetInsert [DecidableEq α] (a : α) (s : SetState α) : SetState α :=
  (Function.update s.1 a true, s.2 + 2)

def pairedSetDelete [DecidableEq α] (a : α) (s : SetState α) : SetState α :=
  (Function.update s.1 a false, s.2 + 2)

def pairedSetIsin (s : SetState α) (a : α) : Bool := s.1 a

theorem pairedSet_odd_invalid (s : α → Bool) : ¬ pairedSetValid (s, 1) :=
  Nat.not_even_one

def setModel (α : Type u) [DecidableEq α] : Sets.Ops α (α → Bool) where
  empty := fun _ => false
  insert a s := Function.update s a true
  delete a s := Function.update s a false
  isin s a := s a

theorem setModel_laws (α : Type u) [DecidableEq α] :
    Sets.Laws (setModel α) setDecode (fun _ => True) where
  empty_decode := setDecode_empty
  empty_valid := True.intro
  insert_decode a s _ := setDecode_insert s a
  insert_valid _ _ _ := True.intro
  delete_decode a s _ := setDecode_delete s a
  delete_valid _ _ _ := True.intro
  isin_iff _ _ _ := Iff.rfl

def pairedSet (α : Type u) [DecidableEq α] : Sets.Ops α (SetState α) where
  empty := pairedSetEmpty α
  insert := pairedSetInsert
  delete := pairedSetDelete
  isin := pairedSetIsin

theorem pairedSet_laws (α : Type u) [DecidableEq α] :
    Sets.Laws (pairedSet α) pairedSetDecode pairedSetValid where
  empty_decode := setDecode_empty
  empty_valid := ⟨0, rfl⟩
  insert_decode a s _ := setDecode_insert s.1 a
  insert_valid _ _ hs := hs.add (show Even (2 : Nat) from ⟨1, rfl⟩)
  delete_decode a s _ := setDecode_delete s.1 a
  delete_valid _ _ hs := hs.add (show Even (2 : Nat) from ⟨1, rfl⟩)
  isin_iff _ _ _ := Iff.rfl

/-- One generic client proof compares the paired state with the function model. -/
theorem pairedMap_client_model [DecidableEq α] (a : α) (x : β) (b : α) (y : β)
    (m : MapState α β) (hm : pairedMapValid m) :
    pairedMapLookup (Maps.client (pairedMap α β) a x b y m) =
      Maps.client (mapModel α β) a x b y m.1 :=
  (pairedMap_laws α β).client_observation_agrees (mapModel_laws α β)
    a x b y hm True.intro rfl

def mapFirst : MapState (Fin 2) Bool :=
  (pairedMap (Fin 2) Bool).update 0 false (pairedMap (Fin 2) Bool).empty

def mapSecond : MapState (Fin 2) Bool := (pairedMap (Fin 2) Bool).update 1 true mapFirst

def mapFinal : MapState (Fin 2) Bool :=
  Maps.client (pairedMap (Fin 2) Bool) 0 false 1 true (pairedMap (Fin 2) Bool).empty

theorem map_states_valid :
    pairedMapValid mapFirst ∧ pairedMapValid mapSecond ∧ pairedMapValid mapFinal :=
  (pairedMap_laws (Fin 2) Bool).client_intermediate_valid 0 false 1 true
    (pairedMap_laws (Fin 2) Bool).empty_valid

theorem map_first_queries :
    pairedMapLookup mapFirst 0 = some false ∧ pairedMapLookup mapFirst 1 = none := by
  have h := (pairedMap_laws (Fin 2) Bool).update_lookup 0 false
    (pairedMap (Fin 2) Bool).empty (pairedMap_laws (Fin 2) Bool).empty_valid
  exact ⟨h.1, h.2 1 (by decide)⟩

theorem map_second_queries :
    pairedMapLookup mapSecond 0 = some false ∧ pairedMapLookup mapSecond 1 = some true := by
  have h := (pairedMap_laws (Fin 2) Bool).update_lookup 1 true mapFirst map_states_valid.1
  exact ⟨(h.2 0 (by decide)).trans map_first_queries.1, h.1⟩

theorem map_final_queries :
    pairedMapLookup mapFinal 0 = none ∧ pairedMapLookup mapFinal 1 = some true :=
  ⟨(pairedMap_laws (Fin 2) Bool).client_lookup_deleted 0 false 1 true
      (pairedMap_laws (Fin 2) Bool).empty_valid,
    (pairedMap_laws (Fin 2) Bool).client_lookup_inserted 0 false 1 true
      (pairedMap_laws (Fin 2) Bool).empty_valid (by decide)⟩

theorem map_counters : mapFirst.2 = 2 ∧ mapSecond.2 = 4 ∧ mapFinal.2 = 6 :=
  ⟨rfl, rfl, rfl⟩

theorem map_model_agrees :
    pairedMapLookup mapFinal =
      Maps.client (mapModel (Fin 2) Bool) 0 false 1 true (mapModel (Fin 2) Bool).empty :=
  pairedMap_client_model 0 false 1 true _ (pairedMap_laws (Fin 2) Bool).empty_valid

theorem map_model_queries :
    Maps.client (mapModel (Fin 2) Bool) 0 false 1 true (mapModel (Fin 2) Bool).empty 0 = none ∧
      Maps.client (mapModel (Fin 2) Bool) 0 false 1 true
        (mapModel (Fin 2) Bool).empty 1 = some true :=
  ⟨(congrFun map_model_agrees 0).symm.trans map_final_queries.1,
    (congrFun map_model_agrees 1).symm.trans map_final_queries.2⟩

def mapSame : MapState (Fin 2) Bool :=
  Maps.client (pairedMap (Fin 2) Bool) 0 false 0 true (pairedMap (Fin 2) Bool).empty

theorem map_same_queries :
    pairedMapLookup mapSame 0 = none ∧ pairedMapLookup mapSame 1 = none :=
  ⟨(pairedMap_laws (Fin 2) Bool).client_lookup_same 0 false true
      (pairedMap_laws (Fin 2) Bool).empty_valid,
    (pairedMap_laws (Fin 2) Bool).client_lookup_untouched 0 false 0 true
      (pairedMap_laws (Fin 2) Bool).empty_valid 1 (by decide) (by decide)⟩

def mapAbsent : MapState (Fin 2) Bool := (pairedMap (Fin 2) Bool).delete 0 mapFinal

theorem map_absent_valid : pairedMapValid mapAbsent :=
  (pairedMap_laws (Fin 2) Bool).delete_valid 0 mapFinal map_states_valid.2.2

theorem map_absent_lookup : pairedMapLookup mapAbsent = pairedMapLookup mapFinal := by
  calc
    pairedMapLookup mapAbsent = Function.update (pairedMapLookup mapFinal) 0 none :=
      (pairedMap_laws (Fin 2) Bool).lookup_delete_eq 0 map_states_valid.2.2
    _ = pairedMapLookup mapFinal := by
      simpa only [map_final_queries.1] using
        Function.update_eq_self (0 : Fin 2) (pairedMapLookup mapFinal)

theorem map_absent_counter : mapAbsent.2 = 8 := rfl

theorem map_absent_changes_state : mapAbsent ≠ mapFinal := by
  intro h
  exact (by decide : (8 : Nat) ≠ 6) (congrArg Prod.snd h)

/-- Equal observations do not erase private state differences. -/
theorem map_hidden_states [DecidableEq α] (m : α → Option β)
    (a : α) (x : β) (b : α) (y : β) :
    (m, 0) ≠ (m, 2) ∧
      pairedMapLookup (Maps.client (pairedMap α β) a x b y (m, 0)) =
        pairedMapLookup (Maps.client (pairedMap α β) a x b y (m, 2)) := by
  refine ⟨?_, ?_⟩
  · intro h
    exact (by decide : (0 : Nat) ≠ 2) (congrArg Prod.snd h)
  · exact (pairedMap_laws α β).client_observation_agrees (pairedMap_laws α β)
      a x b y (show pairedMapValid (m, 0) from ⟨0, rfl⟩)
      (show pairedMapValid (m, 2) from ⟨1, rfl⟩) rfl

def alistFirst : AList (fun _ : Fin 2 => Bool) :=
  (Maps.alistOps (Fin 2) Bool).update 0 false (Maps.alistOps (Fin 2) Bool).empty

def alistSecond : AList (fun _ : Fin 2 => Bool) :=
  (Maps.alistOps (Fin 2) Bool).update 1 true alistFirst

def alistFinal : AList (fun _ : Fin 2 => Bool) :=
  Maps.client (Maps.alistOps (Fin 2) Bool) 0 false 1 true (Maps.alistOps (Fin 2) Bool).empty

/-- The middle entry order is [1,0], independent of the ordered-list algorithm. -/
theorem alist_entries :
    (Maps.alistOps (Fin 2) Bool).empty.entries = [] ∧
      alistFirst.entries = [⟨0, false⟩] ∧
      alistSecond.entries = [⟨1, true⟩, ⟨0, false⟩] ∧
      alistFinal.entries = [⟨1, true⟩] := ⟨rfl, rfl, rfl, rfl⟩

theorem alist_queries :
    (Maps.alistOps (Fin 2) Bool).lookup alistFinal 0 = none ∧
      (Maps.alistOps (Fin 2) Bool).lookup alistFinal 1 = some true :=
  ⟨(Maps.alist_laws (Fin 2) Bool).client_lookup_deleted 0 false 1 true True.intro,
    (Maps.alist_laws (Fin 2) Bool).client_lookup_inserted 0 false 1 true
      True.intro (by decide)⟩

theorem alist_paired_agree :
    (Maps.alistOps (Fin 2) Bool).lookup alistFinal = pairedMapLookup mapFinal :=
  (Maps.alist_laws (Fin 2) Bool).client_observation_agrees
    (pairedMap_laws (Fin 2) Bool) 0 false 1 true True.intro
    (pairedMap_laws (Fin 2) Bool).empty_valid rfl

def alistWithThird : AList (fun _ : Nat => Bool) := AList.singleton 2 true

def alistNatFirst : AList (fun _ : Nat => Bool) :=
  (Maps.alistOps Nat Bool).update 0 false alistWithThird

def alistNatSecond : AList (fun _ : Nat => Bool) :=
  (Maps.alistOps Nat Bool).update 1 true alistNatFirst

def alistNatFinal : AList (fun _ : Nat => Bool) :=
  Maps.client (Maps.alistOps Nat Bool) 0 false 1 true alistWithThird

theorem alist_nat_entries :
    alistWithThird.entries = [⟨2, true⟩] ∧
      alistNatFirst.entries = [⟨0, false⟩, ⟨2, true⟩] ∧
      alistNatSecond.entries = [⟨1, true⟩, ⟨0, false⟩, ⟨2, true⟩] ∧
      alistNatFinal.entries = [⟨1, true⟩, ⟨2, true⟩] := ⟨rfl, rfl, rfl, rfl⟩

/-- This key is untouched by all three mutations, unlike either Fin 2 key. -/
theorem alist_third_unchanged :
    (Maps.alistOps Nat Bool).lookup alistNatFirst 2 = some true ∧
      (Maps.alistOps Nat Bool).lookup alistNatSecond 2 = some true ∧
      (Maps.alistOps Nat Bool).lookup alistNatFinal 2 = some true := by
  have hfirst := (Maps.alist_laws Nat Bool).update_lookup 0 false alistWithThird True.intro
  have hsecond := (Maps.alist_laws Nat Bool).update_lookup 1 true alistNatFirst True.intro
  exact ⟨(hfirst.2 2 (by decide)).trans rfl,
    (hsecond.2 2 (by decide)).trans ((hfirst.2 2 (by decide)).trans rfl),
    ((Maps.alist_laws Nat Bool).client_lookup_untouched 0 false 1 true
      (m := alistWithThird) True.intro 2 (by decide) (by decide)).trans rfl⟩

theorem alist_nat_queries :
    (Maps.alistOps Nat Bool).lookup alistNatFinal 0 = none ∧
      (Maps.alistOps Nat Bool).lookup alistNatFinal 1 = some true ∧
      (Maps.alistOps Nat Bool).lookup alistNatFinal 2 = some true :=
  ⟨(Maps.alist_laws Nat Bool).client_lookup_deleted 0 false 1 true True.intro,
    (Maps.alist_laws Nat Bool).client_lookup_inserted 0 false 1 true True.intro (by decide),
    alist_third_unchanged.2.2⟩

/-- A finite actual key list cannot realize the map present at every Nat key. -/
theorem alist_lookup_not_surjective :
    ¬ Function.Surjective (Maps.alistOps Nat Bool).lookup := by
  intro h
  obtain ⟨s, hs⟩ := h (fun _ => some false)
  obtain ⟨k, hk⟩ := Finset.exists_notMem s.keys.toFinset
  have hnot : k ∉ s := by
    intro hmem
    exact hk (List.mem_toFinset.mpr (AList.mem_keys.mp hmem))
  have hn : AList.lookup k s = none := AList.lookup_eq_none.mpr hnot
  have hv : AList.lookup k s = some false := congrFun hs k
  have bad : (none : Option Bool) = some false := hn.symm.trans hv
  cases bad

theorem empty_key_lookup (m : Empty → Option β) : m = (fun _ => none) := by
  funext k
  exact Empty.elim k

theorem empty_value_lookup (m : α → Option Empty) (k : α) : m k = none := by
  cases m k with
  | none => rfl
  | some value => exact Empty.elim value

theorem empty_keys_initialized :
    pairedMapValid (pairedMapEmpty Empty β) ∧
      pairedMapLookup (pairedMapEmpty Empty β) = (fun _ => none) :=
  ⟨(pairedMap_laws Empty β).empty_valid, (pairedMap_laws Empty β).empty_lookup⟩

theorem empty_values_delete :
    pairedMapValid ((pairedMap (Fin 2) Empty).delete 0 (pairedMap (Fin 2) Empty).empty) ∧
      ((pairedMap (Fin 2) Empty).delete 0 (pairedMap (Fin 2) Empty).empty).2 = 2 ∧
      pairedMapLookup ((pairedMap (Fin 2) Empty).delete 0 (pairedMap (Fin 2) Empty).empty) =
        pairedMapLookup (pairedMap (Fin 2) Empty).empty := by
  refine ⟨(pairedMap_laws (Fin 2) Empty).delete_valid 0 _
    (pairedMap_laws (Fin 2) Empty).empty_valid, rfl, ?_⟩
  calc
    pairedMapLookup ((pairedMap (Fin 2) Empty).delete 0 (pairedMap (Fin 2) Empty).empty) =
        Function.update (pairedMapLookup (pairedMap (Fin 2) Empty).empty) 0 none :=
      (pairedMap_laws (Fin 2) Empty).lookup_delete_eq 0
        (pairedMap_laws (Fin 2) Empty).empty_valid
    _ = pairedMapLookup (pairedMap (Fin 2) Empty).empty :=
      Function.update_eq_self (0 : Fin 2) (fun _ => (none : Option Empty))

theorem no_empty_map_state : ¬ Nonempty (Maps.Ops α β Empty) := by
  rintro ⟨ops⟩
  exact Empty.elim ops.empty

theorem no_empty_set_state : ¬ Nonempty (Sets.Ops α Empty) := by
  rintro ⟨ops⟩
  exact Empty.elim ops.empty

def absentMap : Fin 2 → Option Bool := fun _ => none

def storedFalseMap : Fin 2 → Option Bool := Function.update absentMap 0 (some false)

theorem stored_false_is_present : storedFalseMap 0 ≠ absentMap 0 := by decide

theorem some_true_observation_forgets_false :
    {k | storedFalseMap k = some true} = {k | absentMap k = some true} := by
  ext k
  by_cases hk : k = 0
  · subst k
    simp [storedFalseMap, absentMap]
  · change (storedFalseMap k = some true) ↔ (absentMap k = some true)
    rw [storedFalseMap, Function.update_of_ne hk]

open SquareKit.ValidGraphs

/-- All three schemas retain the paired invariant and the explicit Bool reflection. -/
theorem pairedSet_schemas [DecidableEq α] (a : α) (s : SetState α)
    (hs : pairedSetValid s) :
    validGraph pairedSetValid pairedSetDecode (pairedSetInsert a s) (pairedSetDecode s ∪ {a}) ∧
      validGraph pairedSetValid pairedSetDecode (pairedSetDelete a s) (pairedSetDecode s \ {a}) ∧
      validGraph (fun _ : Bool => True) (fun b : Bool => b = true)
        (pairedSetIsin s a) (a ∈ pairedSetDecode s) :=
  ⟨(pairedSet_laws α).insert_preserves a ⟨hs, rfl⟩,
    (pairedSet_laws α).delete_preserves a ⟨hs, rfl⟩,
    (pairedSet_laws α).isin_preserves a ⟨hs, rfl⟩⟩

theorem pairedSet_initialized [DecidableEq α] :
    validGraph pairedSetValid pairedSetDecode (pairedSetEmpty α) ∅ :=
  (pairedSet_laws α).empty_related

theorem pairedSet_client_model [DecidableEq α] (a b : α) (s : SetState α)
    (hs : pairedSetValid s) (q : α) :
    pairedSetIsin (Sets.client (pairedSet α) a b s) q =
      (setModel α).isin (Sets.client (setModel α) a b s.1) q :=
  (pairedSet_laws α).client_isin_eq (setModel_laws α) a b s s.1 hs True.intro rfl q

def setFirst : SetState (Fin 2) := (pairedSet (Fin 2)).insert 0 (pairedSet (Fin 2)).empty

def setSecond : SetState (Fin 2) := (pairedSet (Fin 2)).insert 1 setFirst

def setFinal : SetState (Fin 2) :=
  Sets.client (pairedSet (Fin 2)) 0 1 (pairedSet (Fin 2)).empty

theorem set_states_valid :
    pairedSetValid setFirst ∧ pairedSetValid setSecond ∧ pairedSetValid setFinal := by
  have hf := (pairedSet_laws (Fin 2)).insert_valid 0 (pairedSet (Fin 2)).empty
    (pairedSet_laws (Fin 2)).empty_valid
  have hs := (pairedSet_laws (Fin 2)).insert_valid 1 setFirst hf
  exact ⟨hf, hs, (pairedSet_laws (Fin 2)).client_valid 0 1 (pairedSet (Fin 2)).empty
    (pairedSet_laws (Fin 2)).empty_valid⟩

theorem set_final_queries :
    pairedSetIsin setFinal 0 = false ∧ pairedSetIsin setFinal 1 = true :=
  ⟨(pairedSet_laws (Fin 2)).client_isin_first 0 1 (pairedSet (Fin 2)).empty
      (pairedSet_laws (Fin 2)).empty_valid,
    (pairedSet_laws (Fin 2)).client_isin_second 0 1 (pairedSet (Fin 2)).empty
      (pairedSet_laws (Fin 2)).empty_valid (by decide)⟩

theorem set_counters : setFirst.2 = 2 ∧ setSecond.2 = 4 ∧ setFinal.2 = 6 :=
  ⟨rfl, rfl, rfl⟩

theorem set_model_queries :
    (setModel (Fin 2)).isin
        (Sets.client (setModel (Fin 2)) 0 1 (setModel (Fin 2)).empty) 0 = false ∧
      (setModel (Fin 2)).isin
        (Sets.client (setModel (Fin 2)) 0 1 (setModel (Fin 2)).empty) 1 = true :=
  ⟨(pairedSet_client_model 0 1 (pairedSet (Fin 2)).empty
      (pairedSet_laws (Fin 2)).empty_valid 0).symm.trans set_final_queries.1,
    (pairedSet_client_model 0 1 (pairedSet (Fin 2)).empty
      (pairedSet_laws (Fin 2)).empty_valid 1).symm.trans set_final_queries.2⟩

theorem set_same_key :
    (pairedSet (Fin 2)).isin
      (Sets.client (pairedSet (Fin 2)) 0 0 (pairedSet (Fin 2)).empty) 0 = false :=
  (pairedSet_laws (Fin 2)).client_isin_same 0 (pairedSet (Fin 2)).empty
    (pairedSet_laws (Fin 2)).empty_valid

def setWithThird : SetState Nat := (Function.update (fun _ => false) 2 true, 0)

theorem set_third_unchanged :
    (pairedSet Nat).isin (Sets.client (pairedSet Nat) 0 1 setWithThird) 2 = true :=
  ((pairedSet_laws Nat).client_isin_other 0 1 setWithThird ⟨0, rfl⟩
    2 (by decide) (by decide)).trans rfl

def setAbsent : SetState (Fin 2) := (pairedSet (Fin 2)).delete 0 setFinal

theorem set_absent_valid : pairedSetValid setAbsent :=
  (pairedSet_laws (Fin 2)).delete_valid 0 setFinal set_states_valid.2.2

theorem set_absent_decode : pairedSetDecode setAbsent = pairedSetDecode setFinal := by
  have hn : (0 : Fin 2) ∉ pairedSetDecode setFinal := by
    intro hm
    have ht := ((pairedSet_laws (Fin 2)).isin_iff setFinal 0 set_states_valid.2.2).2 hm
    have bad : false = true := set_final_queries.1.symm.trans ht
    cases bad
  calc
    pairedSetDecode setAbsent = pairedSetDecode setFinal \ {0} :=
      (pairedSet_laws (Fin 2)).delete_decode 0 setFinal set_states_valid.2.2
    _ = pairedSetDecode setFinal := by
      ext k
      constructor
      · exact And.left
      · intro hk
        exact ⟨hk, fun hzero => hn ((Set.mem_singleton_iff.mp hzero) ▸ hk)⟩

theorem set_absent_changes_state : setAbsent.2 = 8 ∧ setAbsent ≠ setFinal := by
  refine ⟨rfl, ?_⟩
  intro h
  exact (by decide : (8 : Nat) ≠ 6) (congrArg Prod.snd h)

theorem set_hidden_states [DecidableEq α] (s : α → Bool) (a b q : α) :
    (s, 0) ≠ (s, 2) ∧
      (pairedSet α).isin (Sets.client (pairedSet α) a b (s, 0)) q =
        (pairedSet α).isin (Sets.client (pairedSet α) a b (s, 2)) q := by
  refine ⟨?_, ?_⟩
  · intro h
    exact (by decide : (0 : Nat) ≠ 2) (congrArg Prod.snd h)
  · exact (pairedSet_laws α).client_isin_eq (pairedSet_laws α)
      a b (s, 0) (s, 2) ⟨0, rfl⟩ ⟨1, rfl⟩ rfl q

theorem empty_key_set_decode (s : Empty → Bool) : setDecode s = ∅ := by
  ext k
  exact Empty.elim k

theorem empty_set_initialized :
    pairedSetValid (pairedSetEmpty Empty) ∧ pairedSetDecode (pairedSetEmpty Empty) = ∅ :=
  ⟨(pairedSet_laws Empty).empty_valid, (pairedSet_laws Empty).empty_decode⟩

end SetMapContractExamples
