import SquareKit.Internal.Cubical.NativeStructureRecovery
import SquareKit.Internal.Cubical.CartesianNativeStructureRecovery
import Examples.CompositionalStructureIdentity

/-! Native recovery retains state invariants and dependent comparable-pair
witnesses. Boolean complementation changes both the carrier values and the
lattice operation against which the dependent witness is checked. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.NativeStructureRecovery
open CategoryTheory SquareKit.StructureIdentity
open Examples.CompositionalStructureIdentity

def boolState : state.Model Bool :=
  ⟨(false, id, fun b => b = false), ⟨rfl, fun _ h => h⟩⟩

/-- A bounded dependent lattice client: the first component lies below the
second precisely when their meet is the first component. -/
def comparablePair : Formula rawLattice (.product .carrier .carrier) :=
  .equal (opExpr false (.first .var) (.second .var)) (.first .var)

namespace Presheaf
open SquareKit.Cubical.Presheaf StructureIdentity.Native
variable {Γ : Context.{1}}

def encodedData (D : Description) {X : Type} (s : D.Data X) :
    Term (family D (constantFamily Γ (ULift.{1} X))) :=
  Term.map (presentedIso D (Iso.refl _)).inv ⟨fun _ => ⟨s⟩, fun _ => rfl⟩

theorem encodedData_recovery (D : Description) {X : Type} (s : D.Data X) (x : Γ.Elements) :
    decode D (Iso.refl _) x ((encodedData D s).val x) = s :=
  decode_presentedIso_inv D (Iso.refl _) x s

def encodedModel (T : Specification) {X : Type} (s : T.Model X) :
    Term (modelsFamily T (constantFamily Γ (ULift.{1} X))) :=
  Term.map (presentedModelsIso T (Iso.refl _)).inv ⟨fun _ => ⟨s⟩, fun _ => rfl⟩

theorem encodedModel_recovery (T : Specification) {X : Type} (s : T.Model X) (x : Γ.Elements) :
    (presentedModelsEquiv T (Iso.refl _) x ((encodedModel T s).val x)).down = s :=
  congrArg ULift.down ((presentedModelsEquiv T (Iso.refl _) x).apply_symm_apply ⟨s⟩)

def statePackageEquiv {X : Type} (x : Γ.Elements) :
    (modelsFamily state (constantFamily Γ (ULift.{1} X))).obj x ≃
      ULift.{1} (Examples.CubicalStateTransport.StatePackage X) :=
  (presentedModelsEquiv state (Iso.refl _) x).trans
    (Equiv.ulift.trans ((stateModelEquiv X).trans Equiv.ulift.symm))

theorem state_transport {X Y : Type} (e : X ≃ Y) (x : Γ.Elements)
    (s : (modelsFamily state (constantFamily Γ (ULift.{1} X))).obj x) :
    (statePackageEquiv x ((presentedModelsTransport state (Iso.refl _) (Iso.refl _) e).hom.app x s)).down =
      (statePackageEquiv x s).down.conjugate e := by
  change stateModelEquiv Y
    (presentedModelsEquiv state (Iso.refl _) x
      ((presentedModelsTransport state (Iso.refl _) (Iso.refl _) e).hom.app x s)).down = _
  rw [presentedModelsTransport_recovery]
  exact Examples.CompositionalStructureIdentity.state_transport e _

example {X : Type} (x : Γ.Elements)
    (s : (modelsFamily state (constantFamily Γ (ULift.{1} X))).obj x) :
    (statePackageEquiv x).symm (statePackageEquiv x s) = s :=
  (statePackageEquiv x).symm_apply_apply s

def movedState : Term (modelsFamily state (constantFamily Γ (ULift.{1} Bool))) :=
  Term.map (presentedModelsTransport state (Iso.refl _) (Iso.refl _) complement).hom
    (encodedModel state boolState)

theorem movedState_recovery (x : Γ.Elements) :
    (statePackageEquiv x (movedState.val x)).down =
      (stateModelEquiv Bool boolState).conjugate complement := by
  rw [show movedState.val x =
    (presentedModelsTransport state (Iso.refl _) (Iso.refl _) complement).hom.app x
      ((encodedModel state boolState).val x) from rfl, state_transport]
  change (stateModelEquiv Bool
    (presentedModelsEquiv state (Iso.refl _) x ((encodedModel state boolState).val x)).down).conjugate complement = _
  rw [encodedModel_recovery]

example (x : Γ.Elements) : (statePackageEquiv x (movedState.val x)).down.initial = true := by
  rw [movedState_recovery]
  rfl

example (x : Γ.Elements) : (statePackageEquiv x (movedState.val x)).down.Invariant true := by
  rw [movedState_recovery]
  rfl

example (x : Γ.Elements) : ¬ (statePackageEquiv x (movedState.val x)).down.Invariant false := by
  rw [movedState_recovery]
  exact Bool.noConfusion

theorem unchanged_state_rejected (x : Γ.Elements) :
    movedState.val x ≠ (encodedModel state boolState).val x := by
  intro h
  have h' := congrArg (fun s => (statePackageEquiv x s).down.initial) h
  rw [movedState_recovery] at h'
  change true = (stateModelEquiv Bool
    (presentedModelsEquiv state (Iso.refl _) x ((encodedModel state boolState).val x)).down).initial at h'
  rw [encodedModel_recovery] at h'
  exact Bool.noConfusion h'

def movedStatePreservation (x : Γ.Elements) :
    (preserves state.description
      (presentedCarrierIso (Iso.refl _) (Iso.refl _) complement).hom
      (presentedCarrierIso (Iso.refl _) (Iso.refl _) complement).inv
      (sigmaFst (encodedModel state boolState)) (sigmaFst movedState)).obj x :=
  (presentedModelPreservationEquiv state (Iso.refl _) (Iso.refl _) complement
    (encodedModel state boolState) movedState x).symm ⟨⟨by
      apply (state.preserves_iff complement _ _).mpr
      exact (presentedModelsTransport_recovery state (Iso.refl _) (Iso.refl _) complement x
        ((encodedModel state boolState).val x)).symm⟩⟩

theorem unchanged_state_preservation_rejected (x : Γ.Elements) :
    ¬ Nonempty ((preserves state.description
      (presentedCarrierIso (Iso.refl _) (Iso.refl _) complement).hom
      (presentedCarrierIso (Iso.refl _) (Iso.refl _) complement).inv
      (sigmaFst (encodedModel state boolState)) (sigmaFst (encodedModel state boolState))).obj x) := by
  intro h
  have hp := (presented_model_preserves_iff state (Iso.refl _) (Iso.refl _) complement
    (encodedModel state boolState) (encodedModel state boolState) x).mp h
  rw [encodedModel_recovery] at hp
  exact Bool.noConfusion (congrArg (fun z => z.val.1) hp)

def latticeFields : Term (family rawLattice (constantFamily Γ (ULift.{1} Bool))) :=
  encodedData rawLattice boolLattice.val

def comparableFalseTrue (x : Γ.Elements) : (solutionsFamily comparablePair latticeFields).obj x :=
  (presentedSolutionsEquiv comparablePair (Iso.refl _) latticeFields x).symm ⟨⟨(false, true), by
    rw [show decode rawLattice (Iso.refl _) x (latticeFields.val x) = boolLattice.val from
      encodedData_recovery rawLattice boolLattice.val x]
    rfl⟩⟩

theorem comparableFalseTrue_data (x : Γ.Elements) :
    decode (.product .carrier .carrier) (Iso.refl _) x (comparableFalseTrue x).1 = (false, true) :=
  congrArg (fun z => z.down.val)
    ((presentedSolutionsEquiv comparablePair (Iso.refl _) latticeFields x).apply_symm_apply _)

def movedComparable (x : Γ.Elements) :=
  presentedSolutionsTransport comparablePair (Iso.refl _) (Iso.refl _) complement latticeFields x
    (comparableFalseTrue x)

theorem movedComparable_data (x : Γ.Elements) :
    decode (.product .carrier .carrier) (Iso.refl _) x (movedComparable x).1 = (true, false) := by
  unfold movedComparable
  rw [presentedSolutionsTransport_data,
    decode_action _ _ _ complement _ (decode_presentedCarrierIso _ _ complement), comparableFalseTrue_data]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem movedComparable_holds (x : Γ.Elements) :
    transportedLattice.val.1 true false = true := by
  have h := (presentedSolutionsEquiv comparablePair (Iso.refl _)
    (Term.map (actionIso rawLattice (presentedCarrierIso (Iso.refl _) (Iso.refl _) complement)).hom
      latticeFields) x (movedComparable x)).down.property
  change comparablePair.Eval
    (decode rawLattice (Iso.refl _) x
      ((actionIso rawLattice (presentedCarrierIso (Iso.refl _) (Iso.refl _) complement)).hom.app x
        (latticeFields.val x)))
    (decode (.product .carrier .carrier) (Iso.refl _) x (movedComparable x).1) at h
  rw [movedComparable_data, decode_action _ _ _ complement _
    (decode_presentedCarrierIso _ _ complement)] at h
  rw [show decode rawLattice (Iso.refl _) x (latticeFields.val x) = boolLattice.val from
    encodedData_recovery rawLattice boolLattice.val x] at h
  exact h

example (x : Γ.Elements) :
    (presentedSolutionsTransport comparablePair (Iso.refl _) (Iso.refl _) complement latticeFields x).symm
      (movedComparable x) = comparableFalseTrue x :=
  (presentedSolutionsTransport comparablePair (Iso.refl _) (Iso.refl _) complement latticeFields x).symm_apply_apply _

theorem unchanged_comparable_pair_rejected (x : Γ.Elements)
    (c : (solutionsFamily comparablePair latticeFields).obj x)
    (hc : decode (.product .carrier .carrier) (Iso.refl _) x c.1 = (true, false)) : False := by
  have h := (presentedSolutionsEquiv comparablePair (Iso.refl _) latticeFields x c).down.property
  change comparablePair.Eval (decode rawLattice (Iso.refl _) x (latticeFields.val x))
    (decode (.product .carrier .carrier) (Iso.refl _) x c.1) at h
  rw [hc, show decode rawLattice (Iso.refl _) x (latticeFields.val x) = boolLattice.val from
    encodedData_recovery rawLattice boolLattice.val x] at h
  exact Bool.noConfusion h

end Presheaf
namespace Cartesian
open SquareKit.Cubical.Cartesian StructureIdentity.Native
variable {Γ : Context.{1}}

def encodedData (D : Description) {X : Type} (s : D.Data X) :
    Term (family D (constantFamily Γ (ULift.{1} X))) :=
  Term.map (presentedIso D (Iso.refl _)).inv ⟨fun _ => ⟨s⟩, fun _ => rfl⟩

theorem encodedData_recovery (D : Description) {X : Type} (s : D.Data X) (x : Γ.Elements) :
    decode D (Iso.refl _) x ((encodedData D s).val x) = s :=
  decode_presentedIso_inv D (Iso.refl _) x s

def encodedModel (T : Specification) {X : Type} (s : T.Model X) :
    Term (modelsFamily T (constantFamily Γ (ULift.{1} X))) :=
  Term.map (presentedModelsIso T (Iso.refl _)).inv ⟨fun _ => ⟨s⟩, fun _ => rfl⟩

theorem encodedModel_recovery (T : Specification) {X : Type} (s : T.Model X) (x : Γ.Elements) :
    (presentedModelsEquiv T (Iso.refl _) x ((encodedModel T s).val x)).down = s :=
  congrArg ULift.down ((presentedModelsEquiv T (Iso.refl _) x).apply_symm_apply ⟨s⟩)

def statePackageEquiv {X : Type} (x : Γ.Elements) :
    (modelsFamily state (constantFamily Γ (ULift.{1} X))).obj x ≃
      ULift.{1} (Examples.CubicalStateTransport.StatePackage X) :=
  (presentedModelsEquiv state (Iso.refl _) x).trans
    (Equiv.ulift.trans ((stateModelEquiv X).trans Equiv.ulift.symm))

theorem state_transport {X Y : Type} (e : X ≃ Y) (x : Γ.Elements)
    (s : (modelsFamily state (constantFamily Γ (ULift.{1} X))).obj x) :
    (statePackageEquiv x ((presentedModelsTransport state (Iso.refl _) (Iso.refl _) e).hom.app x s)).down =
      (statePackageEquiv x s).down.conjugate e := by
  change stateModelEquiv Y
    (presentedModelsEquiv state (Iso.refl _) x
      ((presentedModelsTransport state (Iso.refl _) (Iso.refl _) e).hom.app x s)).down = _
  rw [presentedModelsTransport_recovery]
  exact Examples.CompositionalStructureIdentity.state_transport e _

example {X : Type} (x : Γ.Elements)
    (s : (modelsFamily state (constantFamily Γ (ULift.{1} X))).obj x) :
    (statePackageEquiv x).symm (statePackageEquiv x s) = s :=
  (statePackageEquiv x).symm_apply_apply s

def movedState : Term (modelsFamily state (constantFamily Γ (ULift.{1} Bool))) :=
  Term.map (presentedModelsTransport state (Iso.refl _) (Iso.refl _) complement).hom
    (encodedModel state boolState)

theorem movedState_recovery (x : Γ.Elements) :
    (statePackageEquiv x (movedState.val x)).down =
      (stateModelEquiv Bool boolState).conjugate complement := by
  rw [show movedState.val x =
    (presentedModelsTransport state (Iso.refl _) (Iso.refl _) complement).hom.app x
      ((encodedModel state boolState).val x) from rfl, state_transport]
  change (stateModelEquiv Bool
    (presentedModelsEquiv state (Iso.refl _) x ((encodedModel state boolState).val x)).down).conjugate complement = _
  rw [encodedModel_recovery]

example (x : Γ.Elements) : (statePackageEquiv x (movedState.val x)).down.initial = true := by
  rw [movedState_recovery]
  rfl

example (x : Γ.Elements) : (statePackageEquiv x (movedState.val x)).down.Invariant true := by
  rw [movedState_recovery]
  rfl

example (x : Γ.Elements) : ¬ (statePackageEquiv x (movedState.val x)).down.Invariant false := by
  rw [movedState_recovery]
  exact Bool.noConfusion

theorem unchanged_state_rejected (x : Γ.Elements) :
    movedState.val x ≠ (encodedModel state boolState).val x := by
  intro h
  have h' := congrArg (fun s => (statePackageEquiv x s).down.initial) h
  rw [movedState_recovery] at h'
  change true = (stateModelEquiv Bool
    (presentedModelsEquiv state (Iso.refl _) x ((encodedModel state boolState).val x)).down).initial at h'
  rw [encodedModel_recovery] at h'
  exact Bool.noConfusion h'

def movedStatePreservation (x : Γ.Elements) :
    (preserves state.description
      (presentedCarrierIso (Iso.refl _) (Iso.refl _) complement).hom
      (presentedCarrierIso (Iso.refl _) (Iso.refl _) complement).inv
      (sigmaFst (encodedModel state boolState)) (sigmaFst movedState)).obj x :=
  (presentedModelPreservationEquiv state (Iso.refl _) (Iso.refl _) complement
    (encodedModel state boolState) movedState x).symm ⟨⟨by
      apply (state.preserves_iff complement _ _).mpr
      exact (presentedModelsTransport_recovery state (Iso.refl _) (Iso.refl _) complement x
        ((encodedModel state boolState).val x)).symm⟩⟩

theorem unchanged_state_preservation_rejected (x : Γ.Elements) :
    ¬ Nonempty ((preserves state.description
      (presentedCarrierIso (Iso.refl _) (Iso.refl _) complement).hom
      (presentedCarrierIso (Iso.refl _) (Iso.refl _) complement).inv
      (sigmaFst (encodedModel state boolState)) (sigmaFst (encodedModel state boolState))).obj x) := by
  intro h
  have hp := (presented_model_preserves_iff state (Iso.refl _) (Iso.refl _) complement
    (encodedModel state boolState) (encodedModel state boolState) x).mp h
  rw [encodedModel_recovery] at hp
  exact Bool.noConfusion (congrArg (fun z => z.val.1) hp)

def latticeFields : Term (family rawLattice (constantFamily Γ (ULift.{1} Bool))) :=
  encodedData rawLattice boolLattice.val

def comparableFalseTrue (x : Γ.Elements) : (solutionsFamily comparablePair latticeFields).obj x :=
  (presentedSolutionsEquiv comparablePair (Iso.refl _) latticeFields x).symm ⟨⟨(false, true), by
    rw [show decode rawLattice (Iso.refl _) x (latticeFields.val x) = boolLattice.val from
      encodedData_recovery rawLattice boolLattice.val x]
    rfl⟩⟩

theorem comparableFalseTrue_data (x : Γ.Elements) :
    decode (.product .carrier .carrier) (Iso.refl _) x (comparableFalseTrue x).1 = (false, true) :=
  congrArg (fun z => z.down.val)
    ((presentedSolutionsEquiv comparablePair (Iso.refl _) latticeFields x).apply_symm_apply _)

def movedComparable (x : Γ.Elements) :=
  presentedSolutionsTransport comparablePair (Iso.refl _) (Iso.refl _) complement latticeFields x
    (comparableFalseTrue x)

theorem movedComparable_data (x : Γ.Elements) :
    decode (.product .carrier .carrier) (Iso.refl _) x (movedComparable x).1 = (true, false) := by
  unfold movedComparable
  rw [presentedSolutionsTransport_data,
    decode_action _ _ _ complement _ (decode_presentedCarrierIso _ _ complement), comparableFalseTrue_data]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem movedComparable_holds (x : Γ.Elements) :
    transportedLattice.val.1 true false = true := by
  have h := (presentedSolutionsEquiv comparablePair (Iso.refl _)
    (Term.map (actionIso rawLattice (presentedCarrierIso (Iso.refl _) (Iso.refl _) complement)).hom
      latticeFields) x (movedComparable x)).down.property
  change comparablePair.Eval
    (decode rawLattice (Iso.refl _) x
      ((actionIso rawLattice (presentedCarrierIso (Iso.refl _) (Iso.refl _) complement)).hom.app x
        (latticeFields.val x)))
    (decode (.product .carrier .carrier) (Iso.refl _) x (movedComparable x).1) at h
  rw [movedComparable_data, decode_action _ _ _ complement _
    (decode_presentedCarrierIso _ _ complement)] at h
  rw [show decode rawLattice (Iso.refl _) x (latticeFields.val x) = boolLattice.val from
    encodedData_recovery rawLattice boolLattice.val x] at h
  exact h

example (x : Γ.Elements) :
    (presentedSolutionsTransport comparablePair (Iso.refl _) (Iso.refl _) complement latticeFields x).symm
      (movedComparable x) = comparableFalseTrue x :=
  (presentedSolutionsTransport comparablePair (Iso.refl _) (Iso.refl _) complement latticeFields x).symm_apply_apply _

theorem unchanged_comparable_pair_rejected (x : Γ.Elements)
    (c : (solutionsFamily comparablePair latticeFields).obj x)
    (hc : decode (.product .carrier .carrier) (Iso.refl _) x c.1 = (true, false)) : False := by
  have h := (presentedSolutionsEquiv comparablePair (Iso.refl _) latticeFields x c).down.property
  change comparablePair.Eval (decode rawLattice (Iso.refl _) x (latticeFields.val x))
    (decode (.product .carrier .carrier) (Iso.refl _) x c.1) at h
  rw [hc, show decode rawLattice (Iso.refl _) x (latticeFields.val x) = boolLattice.val from
    encodedData_recovery rawLattice boolLattice.val x] at h
  exact Bool.noConfusion h

end Cartesian
/-- Cross-model comparison is proved through the common presented structure,
without equating either model's selected univalence path. -/
def modelComparison (T : Specification) {Γ : SquareKit.Cubical.Presheaf.Context.{1}} (X : Type) :
    SquareKit.Cubical.Cartesian.restrictFamily
      (SquareKit.Cubical.Presheaf.StructureIdentity.Native.modelsFamily T
        (SquareKit.Cubical.Presheaf.constantFamily Γ (ULift.{1} X))) ≅
    SquareKit.Cubical.Cartesian.StructureIdentity.Native.modelsFamily T
      (SquareKit.Cubical.Cartesian.constantFamily (SquareKit.Cubical.Cartesian.restrict Γ) (ULift.{1} X)) :=
  Functor.isoWhiskerLeft (SquareKit.Cubical.Cartesian.elements Γ)
    (SquareKit.Cubical.Presheaf.StructureIdentity.Native.presentedModelsIso T (Iso.refl _)) ≪≫
      (SquareKit.Cubical.Cartesian.StructureIdentity.Native.presentedModelsIso T (Iso.refl _)).symm

theorem modelComparison_recovery (T : Specification) {Γ : SquareKit.Cubical.Presheaf.Context.{1}}
    {X : Type} (x : (SquareKit.Cubical.Cartesian.restrict Γ).Elements)
    (s : (SquareKit.Cubical.Cartesian.restrictFamily
      (SquareKit.Cubical.Presheaf.StructureIdentity.Native.modelsFamily T
        (SquareKit.Cubical.Presheaf.constantFamily Γ (ULift.{1} X)))).obj x) :
    SquareKit.Cubical.Cartesian.StructureIdentity.Native.presentedModelsEquiv T (Iso.refl _) x
      ((modelComparison T X).hom.app x s) =
    SquareKit.Cubical.Presheaf.StructureIdentity.Native.presentedModelsEquiv T (Iso.refl _)
      ((SquareKit.Cubical.Cartesian.elements Γ).obj x) s :=
  (SquareKit.Cubical.Cartesian.StructureIdentity.Native.presentedModelsEquiv T (Iso.refl _) x).apply_symm_apply _

end Examples.NativeStructureRecovery
