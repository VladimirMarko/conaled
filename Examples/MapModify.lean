import Examples.SetMapContracts
import Applications.Collections.Modify

/-! Connected uses of both Map/modify translations. The history-sensitive
counterexample separates equal lookup observations from equality of returned
states. Source and statement assessment: `docs/research/fdsa-adt-refinement.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace MapModifyExamples
open SetMapContractExamples
open Collections

def sequenceStart : MapState (Fin 2) Bool :=
  (Function.update (fun _ => none) 1 (some true), 0)

theorem sequenceStart_valid : pairedMapValid sequenceStart := ⟨0, rfl⟩

theorem sequenceStart_lookup :
    pairedMapLookup sequenceStart 0 = none ∧ pairedMapLookup sequenceStart 1 = some true :=
  ⟨rfl, rfl⟩

def pairedModify : Maps.Modify.Ops (Fin 2) Bool (MapState (Fin 2) Bool) :=
  Maps.Modify.ofMap (pairedMap (Fin 2) Bool)

theorem pairedModify_laws : Maps.Modify.Laws pairedModify pairedMapValid :=
  Maps.Modify.ofMap_laws (pairedMap_laws (Fin 2) Bool)

def created : MapState (Fin 2) Bool :=
  pairedModify.modify 0 (fun _ => some false) sequenceStart

def kept : MapState (Fin 2) Bool := pairedModify.modify 0 id created

def overwritten : MapState (Fin 2) Bool := pairedModify.modify 0 (Option.map Bool.not) kept

def deleted : MapState (Fin 2) Bool := pairedModify.modify 0 (fun _ => none) overwritten

theorem created_valid : pairedMapValid created :=
  pairedModify_laws.modify_valid 0 (fun _ => some false) sequenceStart sequenceStart_valid

theorem kept_valid : pairedMapValid kept :=
  pairedModify_laws.modify_valid 0 id created created_valid

theorem overwritten_valid : pairedMapValid overwritten :=
  pairedModify_laws.modify_valid 0 (Option.map Bool.not) kept kept_valid

theorem deleted_valid : pairedMapValid deleted :=
  pairedModify_laws.modify_valid 0 (fun _ => none) overwritten overwritten_valid

/-- The first callback creates a binding from an absent observation. -/
theorem created_queries :
    pairedMapLookup created 0 = some false ∧ pairedMapLookup created 1 = some true := by
  have h := pairedModify_laws.modify_lookup 0 (fun _ => some false)
    sequenceStart sequenceStart_valid
  exact ⟨h.1, (h.2 1 (by decide)).trans sequenceStart_lookup.2⟩

theorem kept_queries :
    pairedMapLookup kept 0 = some false ∧ pairedMapLookup kept 1 = some true := by
  have h := pairedModify_laws.modify_lookup 0 id created created_valid
  exact ⟨h.1.trans created_queries.1, (h.2 1 (by decide)).trans created_queries.2⟩

theorem overwritten_queries :
    pairedMapLookup overwritten 0 = some true ∧ pairedMapLookup overwritten 1 = some true := by
  have h := pairedModify_laws.modify_lookup 0 (Option.map Bool.not) kept kept_valid
  exact ⟨h.1.trans (congrArg (Option.map Bool.not) kept_queries.1),
    (h.2 1 (by decide)).trans kept_queries.2⟩

theorem deleted_queries :
    pairedMapLookup deleted 0 = none ∧ pairedMapLookup deleted 1 = some true := by
  have h := pairedModify_laws.modify_lookup 0 (fun _ => none) overwritten overwritten_valid
  exact ⟨h.1, (h.2 1 (by decide)).trans overwritten_queries.2⟩

theorem sequence_counters :
    created.2 = 2 ∧ kept.2 = 4 ∧ overwritten.2 = 6 ∧ deleted.2 = 8 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem identity_keeps_observation : pairedMapLookup kept = pairedMapLookup created :=
  (pairedModify_laws.lookup_modify_eq 0 id created_valid).trans
    (Function.update_eq_self (0 : Fin 2) (pairedMapLookup created))

theorem identity_changes_paired_state : kept ≠ created := by
  intro h
  exact (by decide : (4 : Nat) ≠ 2) (congrArg Prod.snd h)

def oddStart : MapState (Fin 2) Bool := (sequenceStart.1, 1)

theorem oddStart_invalid : ¬ pairedMapValid oddStart := pairedMap_odd_invalid _

/-- This equality consumes the unconditional definitional round trip, without
applying a mutation law to the invalid counter-one state. -/
theorem raw_round_trip :
    (Maps.Modify.toMap (Maps.Modify.ofMap (pairedMap (Fin 2) Bool))).update
        0 false oddStart =
      (pairedMap (Fin 2) Bool).update 0 false oddStart := by
  rw [Maps.Modify.toMap_ofMap]

theorem raw_round_trip_counters :
    ((Maps.Modify.toMap (Maps.Modify.ofMap (pairedMap (Fin 2) Bool))).update
        0 false oddStart).2 = 3 ∧
      ((pairedMap (Fin 2) Bool).update 0 false oddStart).2 = 3 :=
  ⟨(congrArg Prod.snd raw_round_trip).trans rfl, rfl⟩

def alistModify : Maps.Modify.Ops (Fin 2) Bool (AList (fun _ : Fin 2 => Bool)) :=
  Maps.Modify.ofMap (Maps.alistOps (Fin 2) Bool)

theorem alistModify_laws : Maps.Modify.Laws alistModify (fun _ => True) :=
  Maps.Modify.ofMap_laws (Maps.alist_laws (Fin 2) Bool)

def alistModified : AList (fun _ : Fin 2 => Bool) :=
  alistModify.modify 0 (Option.map Bool.not) alistSecond

theorem alist_modified_queries :
    alistModify.lookup alistModified 0 = some true ∧
      alistModify.lookup alistModified 1 = some true := by
  have hfirst := (Maps.alist_laws (Fin 2) Bool).update_lookup 0 false
    (Maps.alistOps (Fin 2) Bool).empty True.intro
  have hsecond := (Maps.alist_laws (Fin 2) Bool).update_lookup 1 true alistFirst True.intro
  have hzero := (hsecond.2 0 (by decide)).trans hfirst.1
  have h := alistModify_laws.modify_lookup 0 (Option.map Bool.not) alistSecond True.intro
  exact ⟨h.1.trans (congrArg (Option.map Bool.not) hzero),
    (h.2 1 (by decide)).trans hsecond.1⟩

theorem alist_modified_entries : alistModified.entries = [⟨0, true⟩, ⟨1, true⟩] := rfl

/-- This metadata depends on the callback away from the current binding. -/
def counterDelta (f : Option Bool → Option Bool) : Nat :=
  if f none = none then 1 else 2

def historyModify (a : Fin 2) (f : Option Bool → Option Bool)
    (m : MapState (Fin 2) Bool) : MapState (Fin 2) Bool :=
  (Function.update m.1 a (f (m.1 a)), m.2 + counterDelta f)

def historyStart : MapState (Fin 2) Bool :=
  (Function.update (Function.update (fun _ => none) 0 (some false)) 1 (some true), 0)

theorem historyStart_lookup :
    pairedMapLookup historyStart 0 = some false ∧
      pairedMapLookup historyStart 1 = some true := ⟨rfl, rfl⟩

theorem history_identity_counter : (historyModify 0 id historyStart).2 = 1 := rfl

theorem history_constant_counter :
    (historyModify 0 (fun _ => some false) historyStart).2 = 2 := rfl

def historyOps : Maps.Modify.Ops (Fin 2) Bool (MapState (Fin 2) Bool) where
  empty := pairedMapEmpty (Fin 2) Bool
  modify := historyModify
  lookup := pairedMapLookup

/-- Validity is True here; the earlier even invariant would reject the odd increment. -/
theorem history_laws : Maps.Modify.Laws historyOps (fun _ => True) where
  empty_lookup := rfl
  empty_valid := True.intro
  modify_lookup a f m _ :=
    ⟨Function.update_self a (f (m.1 a)) m.1,
      fun _ hk => Function.update_of_ne hk (f (m.1 a)) m.1⟩
  modify_valid _ _ _ _ := True.intro

theorem history_map_laws : Maps.Laws (Maps.Modify.toMap historyOps) (fun _ => True) :=
  history_laws.toMap

def historyRebuilt : MapState (Fin 2) Bool :=
  (Maps.Modify.ofMap (Maps.Modify.toMap historyOps)).modify 0 id historyStart

/-- Equality is of complete lookup functions, supplied by the public round trip. -/
theorem history_round_trip_lookup :
    pairedMapLookup historyRebuilt = pairedMapLookup (historyModify 0 id historyStart) :=
  history_laws.roundTrip_lookup 0 id (m := historyStart) True.intro

theorem history_round_trip_valid :
    (fun _ : MapState (Fin 2) Bool => True) historyRebuilt ∧
      (fun _ : MapState (Fin 2) Bool => True) (historyModify 0 id historyStart) :=
  ⟨history_laws.roundTrip_valid 0 id (m := historyStart) True.intro,
    history_laws.modify_valid 0 id historyStart True.intro⟩

theorem history_original_lookup :
    pairedMapLookup (historyModify 0 id historyStart) = pairedMapLookup historyStart :=
  (history_laws.lookup_modify_eq 0 id (m := historyStart) True.intro).trans
    (Function.update_eq_self (0 : Fin 2) (pairedMapLookup historyStart))

theorem history_rebuilt_lookup : pairedMapLookup historyRebuilt = pairedMapLookup historyStart :=
  history_round_trip_lookup.trans history_original_lookup

theorem history_rebuilt_counter : historyRebuilt.2 = 2 := rfl

theorem history_round_trip_states_ne : historyRebuilt ≠ historyModify 0 id historyStart := by
  intro h
  exact (by decide : (2 : Nat) ≠ 1) (congrArg Prod.snd h)

end MapModifyExamples
