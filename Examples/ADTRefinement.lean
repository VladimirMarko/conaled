import SquareKit.ValidGraphs
import SquareKit.RelationComposition
import Examples.SetMapContracts
import Mathlib.Tactic

/-! Actual relational composition, explicit argument roles, and the boundaries
of invariant-conditioned Set/Map refinement. The independent calculations and
source correspondence are recorded in `docs/research/fdsa-adt-refinement.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace ADTRefinementExamples

open SquareKit.ValidGraphs

/-! The two Bool cases distinguish missing intermediate validity from missing
agreement of the actual intermediate operations. -/

def allBool : Relational.RelRep :=
  ⟨Bool, Bool, validGraph (fun _ => True) id⟩

def trueBool : Relational.RelRep :=
  ⟨Bool, Bool, validGraph (fun b => b = true) id⟩

def constantFirst : Relational.RelSquare allBool allBool where
  impl _ := true
  spec _ := true
  preserves _ := ⟨True.intro, rfl⟩

def constantSecond : Relational.RelSquare trueBool trueBool where
  impl _ := true
  spec := id
  preserves h := ⟨rfl, h.1.symm.trans h.2⟩

def constantComposite :=
  Relational.existentialSquare constantFirst constantSecond (fun _ => rfl)

theorem constant_composite_relation (b c : Bool) :
    Relational.compRel allBool.Rel trueBool.Rel b c ↔ b = true ∧ b = c := by
  simpa [allBool, trueBool] using
    (comp_iff (fun _ : Bool => True) id (fun b : Bool => b = true) id b c)

theorem constant_composite_legal :
    Relational.compRel allBool.Rel trueBool.Rel
      (constantComposite.impl true) (constantComposite.spec true) :=
  constantComposite.preserves
    ⟨true, ⟨True.intro, rfl⟩, ⟨rfl, rfl⟩⟩

theorem false_not_composite_related :
    ¬ Relational.compRel allBool.Rel trueBool.Rel false false := by
  intro h
  have bad : false = true := ((constant_composite_relation false false).mp h).1
  cases bad

/-- The actual composite is valid, but its equation cannot be extended to an
input lacking the intermediate predicate. Both middle arrows are constant true. -/
theorem middle_validity_needed :
    ¬ (∀ b : Bool, constantComposite.impl b = constantComposite.spec b) := by
  intro h
  have bad : true = false := h false
  cases bad

def negateSquare : Relational.RelSquare allBool allBool where
  impl := Bool.not
  spec := Bool.not
  preserves h := ⟨True.intro, congrArg Bool.not h.2⟩

def identitySquare : Relational.RelSquare allBool allBool :=
  Relational.identity allBool

theorem incompatible_middle :
    ¬ (∀ b : Bool, negateSquare.spec b = identitySquare.impl b) := by
  intro h
  have bad : true = false := h false
  cases bad

/-- Individually preserving squares cannot be pasted through different middle
operations, even when every state is valid and both decoders are identity. -/
theorem middle_agreement_needed :
    ¬ Relator.LiftFun (Relational.compRel allBool.Rel allBool.Rel)
      (Relational.compRel allBool.Rel allBool.Rel)
      negateSquare.impl identitySquare.spec := by
  intro h
  have input : Relational.compRel allBool.Rel allBool.Rel false false :=
    ⟨false, ⟨True.intro, rfl⟩, ⟨True.intro, rfl⟩⟩
  obtain ⟨middle, first, second⟩ := h input
  have bad : true = false := first.2.trans second.2
  cases bad

/-! Explicit products retain argument roles even when their Lean carriers are
identical. The valid-graph bridge supplies the unbundled preservation proof. -/

def ordinaryNat : Relational.RelRep := ⟨Nat, Nat, Eq⟩

def evenNat : Relational.RelRep :=
  ⟨Nat, Nat, validGraph Even (fun n => n / 2)⟩

def shiftImpl (p : Nat × Nat) : Nat := p.2 + 2 * p.1

def shiftSpec (p : Nat × Nat) : Nat := p.2 + p.1

theorem shift_preserves :
    Relator.LiftFun
      (validGraph (fun p : Nat × Nat => Even p.2)
        (fun p => (p.1, p.2 / 2)))
      (validGraph Even (fun n : Nat => n / 2)) shiftImpl shiftSpec := by
  apply (liftFun_iff (fun p : Nat × Nat => Even p.2)
    (fun p => (p.1, p.2 / 2)) Even (fun n : Nat => n / 2)
    shiftImpl shiftSpec).mpr
  intro p hp
  obtain ⟨k, hk⟩ := hp
  constructor
  · refine ⟨k + p.1, ?_⟩
    dsimp only [shiftImpl]
    omega
  · dsimp only [shiftImpl, shiftSpec]
    omega

def shiftSquare :
    Relational.RelSquare (Relational.product ordinaryNat evenNat) evenNat where
  impl := shiftImpl
  spec := shiftSpec
  preserves := by
    intro p q h
    exact shift_preserves ⟨h.2.1, Prod.ext h.1 h.2.2⟩

theorem ordinary_parameter_case :
    shiftSquare.impl (3, 4) = 10 ∧ shiftSquare.spec (3, 2) = 5 ∧
      evenNat.Rel (shiftSquare.impl (3, 4)) (shiftSquare.spec (3, 2)) ∧
      ¬ Even (3 : Nat) := by
  refine ⟨rfl, rfl, ?_, by decide⟩
  exact shiftSquare.preserves ⟨rfl, ⟨⟨2, rfl⟩, rfl⟩⟩

theorem decoding_ordinary_parameter_changes_result :
    shiftSpec (3 / 2, 4 / 2) = 3 ∧
      shiftSpec (3, 4 / 2) ≠ shiftSpec (3 / 2, 4 / 2) := by
  decide

def pairSum (p : Nat × Nat) : Nat := p.1 + p.2

theorem pairSum_preserves :
    Relator.LiftFun
      (validGraph (fun p : Nat × Nat => Even p.1 ∧ Even p.2)
        (fun p => (p.1 / 2, p.2 / 2)))
      (validGraph Even (fun n : Nat => n / 2)) pairSum pairSum := by
  apply (liftFun_iff (fun p : Nat × Nat => Even p.1 ∧ Even p.2)
    (fun p => (p.1 / 2, p.2 / 2)) Even (fun n : Nat => n / 2)
    pairSum pairSum).mpr
  intro p hp
  obtain ⟨k, hk⟩ := hp.1
  obtain ⟨l, hl⟩ := hp.2
  constructor
  · refine ⟨k + l, ?_⟩
    dsimp only [pairSum]
    omega
  · dsimp only [pairSum]
    omega

def pairSumSquare :
    Relational.RelSquare (Relational.product evenNat evenNat) evenNat where
  impl := pairSum
  spec := pairSum
  preserves := by
    intro p q h
    exact pairSum_preserves ⟨⟨h.1.1, h.2.1⟩, Prod.ext h.1.2 h.2.2⟩

theorem two_represented_inputs :
    pairSumSquare.impl (4, 6) = 10 ∧ pairSumSquare.spec (2, 3) = 5 ∧
      evenNat.Rel (pairSumSquare.impl (4, 6)) (pairSumSquare.spec (2, 3)) := by
  refine ⟨rfl, rfl, ?_⟩
  exact pairSumSquare.preserves
    ⟨⟨⟨2, rfl⟩, rfl⟩, ⟨⟨3, rfl⟩, rfl⟩⟩

theorem first_input_validity_insufficient :
    Even (4 : Nat) ∧ ¬ Even (1 : Nat) ∧
      ¬ Even (pairSumSquare.impl (4, 1)) := by
  decide

theorem second_input_validity_insufficient :
    ¬ Even (1 : Nat) ∧ Even (4 : Nat) ∧
      ¬ Even (pairSumSquare.impl (1, 4)) := by
  decide

/-! A tagged implementation refines the actual even-counter Map, which refines
ordinary partial functions. Every vertical pasting uses the same middle arrow. -/

open SetMapContractExamples

abbrev SmallMap := MapState (Fin 2) Bool
abbrev TaggedMap := SmallMap × Bool
abbrev MapModel := Fin 2 → Option Bool

def taggedIntrinsic (t : TaggedMap) : Prop := t.2 = true

def taggedValid (t : TaggedMap) : Prop :=
  taggedIntrinsic t ∧ pairedMapValid t.1

def taggedLookup (t : TaggedMap) : MapModel := pairedMapLookup t.1

def taggedEmpty : TaggedMap := (pairedMapEmpty (Fin 2) Bool, true)

def taggedUpdate (a : Fin 2) (x : Bool) (t : TaggedMap) : TaggedMap :=
  (pairedMapUpdate a x t.1, t.2)

def taggedDelete (a : Fin 2) (t : TaggedMap) : TaggedMap :=
  (pairedMapDelete a t.1, t.2)

def taggedOps : Collections.Maps.Ops (Fin 2) Bool TaggedMap where
  empty := taggedEmpty
  update := taggedUpdate
  delete := taggedDelete
  lookup := taggedLookup

def tagRepresentation : Relational.RelRep :=
  ⟨TaggedMap, SmallMap, validGraph taggedIntrinsic (fun t => t.1)⟩

def mapRepresentation : Relational.RelRep :=
  ⟨SmallMap, MapModel, validGraph pairedMapValid pairedMapLookup⟩

def taggedRepresentation : Relational.RelRep :=
  ⟨TaggedMap, MapModel, validGraph taggedValid taggedLookup⟩

/-- This exact relation transport retains both predicates. -/
theorem tagged_relation_iff (t : TaggedMap) (m : MapModel) :
    Relational.compRel tagRepresentation.Rel mapRepresentation.Rel t m ↔
      taggedRepresentation.Rel t m :=
  comp_iff taggedIntrinsic (fun t : TaggedMap => t.1)
    pairedMapValid pairedMapLookup t m

def tagUpdateSquare (a : Fin 2) (x : Bool) :
    Relational.RelSquare tagRepresentation tagRepresentation where
  impl := taggedUpdate a x
  spec := pairedMapUpdate a x
  preserves h := ⟨h.1, congrArg (pairedMapUpdate a x) h.2⟩

def mapUpdateSquare (a : Fin 2) (x : Bool) :
    Relational.RelSquare mapRepresentation mapRepresentation where
  impl := pairedMapUpdate a x
  spec f := Function.update f a (some x)
  preserves := (pairedMap_laws (Fin 2) Bool).update_preserves a x

def taggedUpdateSquare (a : Fin 2) (x : Bool) :
    Relational.RelSquare taggedRepresentation taggedRepresentation :=
  Relational.transportRelations
    (Relational.existentialSquare (tagUpdateSquare a x) (mapUpdateSquare a x)
      (fun _ => rfl))
    taggedRepresentation.Rel taggedRepresentation.Rel
    tagged_relation_iff tagged_relation_iff

def tagDeleteSquare (a : Fin 2) :
    Relational.RelSquare tagRepresentation tagRepresentation where
  impl := taggedDelete a
  spec := pairedMapDelete a
  preserves h := ⟨h.1, congrArg (pairedMapDelete a) h.2⟩

def mapDeleteSquare (a : Fin 2) :
    Relational.RelSquare mapRepresentation mapRepresentation where
  impl := pairedMapDelete a
  spec f := Function.update f a none
  preserves := (pairedMap_laws (Fin 2) Bool).delete_preserves a

def taggedDeleteSquare (a : Fin 2) :
    Relational.RelSquare taggedRepresentation taggedRepresentation :=
  Relational.transportRelations
    (Relational.existentialSquare (tagDeleteSquare a) (mapDeleteSquare a)
      (fun _ => rfl))
    taggedRepresentation.Rel taggedRepresentation.Rel
    tagged_relation_iff tagged_relation_iff

def tagEmptySquare : Relational.RelSquare Relational.terminal tagRepresentation where
  impl _ := taggedEmpty
  spec _ := pairedMapEmpty (Fin 2) Bool
  preserves _ := ⟨rfl, rfl⟩

def mapEmptySquare : Relational.RelSquare Relational.terminal mapRepresentation where
  impl _ := pairedMapEmpty (Fin 2) Bool
  spec _ := fun _ => none
  preserves _ := (pairedMap_laws (Fin 2) Bool).empty_related

/-- Nullary initialization has a true input condition at both stages. -/
def taggedEmptySquare :
    Relational.RelSquare Relational.terminal taggedRepresentation :=
  Relational.transportRelations
    (Relational.existentialSquare tagEmptySquare mapEmptySquare (fun _ => rfl))
    (fun _ _ => True) taggedRepresentation.Rel
    (fun _ _ => ⟨fun _ => True.intro,
      fun _ => ⟨PUnit.unit, True.intro, True.intro⟩⟩)
    tagged_relation_iff

theorem tagged_empty_related :
    taggedRepresentation.Rel taggedOps.empty (fun _ => none) :=
  taggedEmptySquare.preserves (r := PUnit.unit) (s := PUnit.unit) True.intro

/-- The ordinary tagged operations obtain all six laws from the actual
composed squares, including their output validity certificates. -/
theorem tagged_laws : Collections.Maps.Laws taggedOps taggedValid where
  empty_lookup := tagged_empty_related.2
  empty_valid := tagged_empty_related.1
  update_lookup a x t ht :=
    Function.eq_update_iff.mp ((taggedUpdateSquare a x).preserves ⟨ht, rfl⟩).2
  update_valid a x t ht := ((taggedUpdateSquare a x).preserves ⟨ht, rfl⟩).1
  delete_lookup a t ht :=
    Function.eq_update_iff.mp ((taggedDeleteSquare a).preserves ⟨ht, rfl⟩).2
  delete_valid a t ht := ((taggedDeleteSquare a).preserves ⟨ht, rfl⟩).1

def taggedClientSquare (a : Fin 2) (x : Bool) (b : Fin 2) (y : Bool) :
    Relational.RelSquare taggedRepresentation taggedRepresentation :=
  Relational.compose (taggedDeleteSquare a)
    (Relational.compose (taggedUpdateSquare b y) (taggedUpdateSquare a x))

theorem tagged_client_impl (a : Fin 2) (x : Bool) (b : Fin 2) (y : Bool)
    (t : TaggedMap) :
    (taggedClientSquare a x b y).impl t =
      Collections.Maps.client taggedOps a x b y t := rfl

theorem tagged_client_spec (a : Fin 2) (x : Bool) (b : Fin 2) (y : Bool)
    (m : MapModel) :
    (taggedClientSquare a x b y).spec m =
      Function.update (Function.update (Function.update m a (some x)) b (some y))
        a none := rfl

def optionRepresentation : Relational.RelRep :=
  ⟨Option Bool, Option Bool, validGraph (fun _ => True) id⟩

/-- The endpoint observation uses the law-free lookup schema. -/
def taggedLookupSquare (a : Fin 2) :
    Relational.RelSquare taggedRepresentation optionRepresentation where
  impl t := taggedOps.lookup t a
  spec f := f a
  preserves := Collections.Maps.lookup_preserves taggedOps taggedValid a

def taggedFirst : TaggedMap := taggedOps.update 0 false taggedOps.empty

def taggedSecond : TaggedMap := taggedOps.update 1 true taggedFirst

def taggedSample : TaggedMap :=
  Collections.Maps.client taggedOps 0 false 1 true taggedOps.empty

theorem tagged_intermediate_validity :
    taggedValid taggedFirst ∧ taggedValid taggedSecond ∧ taggedValid taggedSample :=
  tagged_laws.client_intermediate_valid 0 false 1 true tagged_laws.empty_valid

theorem tagged_history :
    [taggedOps.empty.1.2, taggedFirst.1.2, taggedSecond.1.2, taggedSample.1.2] =
      [0, 2, 4, 6] ∧
    [taggedOps.empty.2, taggedFirst.2, taggedSecond.2, taggedSample.2] =
      [true, true, true, true] := ⟨rfl, rfl⟩

theorem tagged_queries_from_laws :
    taggedOps.lookup taggedSample 0 = none ∧
      taggedOps.lookup taggedSample 1 = some true :=
  ⟨tagged_laws.client_lookup_deleted 0 false 1 true tagged_laws.empty_valid,
    tagged_laws.client_lookup_inserted 0 false 1 true tagged_laws.empty_valid
      (by decide)⟩

/-- Initialization, all three mutations, and the ordinary endpoint observation
are horizontally composed after the two implementation stages were pasted. -/
def sampleQuerySquare (a : Fin 2) :
    Relational.RelSquare Relational.terminal optionRepresentation :=
  Relational.compose (taggedLookupSquare a)
    (Relational.compose (taggedClientSquare 0 false 1 true) taggedEmptySquare)

theorem tagged_query_from_squares (a : Fin 2) :
    optionRepresentation.Rel (taggedOps.lookup taggedSample a)
      ((taggedClientSquare 0 false 1 true).spec (fun _ => none) a) :=
  (sampleQuerySquare a).preserves (r := PUnit.unit) (s := PUnit.unit) True.intro

theorem tagged_queries_from_composition :
    taggedOps.lookup taggedSample 0 = none ∧
      taggedOps.lookup taggedSample 1 = some true :=
  ⟨(tagged_query_from_squares 0).2.trans rfl,
    (tagged_query_from_squares 1).2.trans rfl⟩

def oddTagged : TaggedMap := ((fun _ => none, 1), true)

def falseTagged : TaggedMap := (pairedMapEmpty (Fin 2) Bool, false)

/-- Neither constituent predicate follows from the other. These witnesses
make no claim that the decoded operation fails on every invalid state. -/
theorem tagged_predicates_independent :
    taggedIntrinsic oddTagged ∧ ¬ pairedMapValid oddTagged.1 ∧
      ¬ taggedIntrinsic falseTagged ∧ pairedMapValid falseTagged.1 :=
  ⟨rfl, pairedMap_odd_invalid _, by decide, pairedMapEmpty_valid⟩

theorem malformed_tagged_states :
    ¬ taggedValid oddTagged ∧ ¬ taggedValid falseTagged :=
  ⟨fun h => tagged_predicates_independent.2.1 h.2,
    fun h => tagged_predicates_independent.2.2.1 h.1⟩

end ADTRefinementExamples
