import SquareKit.Internal.Cubical.NativeStructureLaws
import SquareKit.Internal.Cubical.CartesianNativeStructureLaws
import SquareKit.Internal.Cubical.NativeStructureUaComparison
import SquareKit.Internal.Cubical.CartesianNativeStructureUaComparison
import Examples.NativeStructureDescriptions

/-! Native law witnesses, fixed-point models, and complete path recovery in both models. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.NativeStructureLaws
open CategoryTheory SquareKit.StructureIdentity

def fixedPointLaw : Formula Examples.NativeStructureDescriptions.pointedUnary (.fixed Unit) :=
  .equal (.apply (.second .data) (.first .data)) (.first .data)

def identityLaw : Formula Examples.NativeStructureDescriptions.pointedUnary (.fixed Unit) :=
  .all .carrier (.equal (.apply (.second .data) (.second .var)) (.second .var))

def fixedPointSpecification : Specification :=
  ⟨Examples.NativeStructureDescriptions.pointedUnary, fixedPointLaw⟩

namespace Presheaf
open SquareKit.Cubical.Presheaf
universe u
variable {Γ : Context.{u}}

def emptyProposition : Term (HomotopyLevels.isProp (constantFamily Γ PEmpty.{u+1})) :=
  HomotopyLevels.ofSubsingleton _ (fun _ => (show Subsingleton PEmpty from inferInstance))

def unitProposition : Term (HomotopyLevels.isProp (constantFamily Γ PUnit.{u+1})) :=
  HomotopyLevels.ofSubsingleton _ (fun _ => (show Subsingleton PUnit from inferInstance))

def unitPoint : Term (constantFamily Γ PUnit.{u+1}) := ⟨fun _ => PUnit.unit, fun _ => rfl⟩

example : (HomotopyLevels.contractible unitProposition unitPoint).center =
    unitPoint (Γ := Γ) := rfl

theorem empty_has_no_point (x : Γ.Elements) :
    ¬ Nonempty (Term (constantFamily Γ PEmpty.{u+1})) := by
  rintro ⟨a⟩
  exact (a.val x).elim

/-- A native proposition witness cannot identify distinct constant observations. -/
theorem bool_not_proposition (x : Γ.Elements) :
    ¬ Nonempty (Term (HomotopyLevels.isProp (constantFamily Γ (ULift.{u} Bool)))) := by
  rintro ⟨p⟩
  let a : Term (constantFamily Γ (ULift.{u} Bool)) := ⟨fun _ => ⟨false⟩, fun _ => rfl⟩
  let b : Term (constantFamily Γ (ULift.{u} Bool)) := ⟨fun _ => ⟨true⟩, fun _ => rfl⟩
  have h := discretePath_endpoints (HomotopyLevels.path p a b)
  have := congrArg (fun z => (z.val x).down) h
  contradiction

end Presheaf

namespace Cartesian
open SquareKit.Cubical.Cartesian
universe u
variable {Γ : Context.{u}}

def emptyProposition : Term (HomotopyLevels.isProp (constantFamily Γ PEmpty.{u+1})) :=
  HomotopyLevels.ofSubsingleton _ (fun _ => (show Subsingleton PEmpty from inferInstance))

def unitProposition : Term (HomotopyLevels.isProp (constantFamily Γ PUnit.{u+1})) :=
  HomotopyLevels.ofSubsingleton _ (fun _ => (show Subsingleton PUnit from inferInstance))

def unitPoint : Term (constantFamily Γ PUnit.{u+1}) := ⟨fun _ => PUnit.unit, fun _ => rfl⟩

example : (HomotopyLevels.contractible unitProposition unitPoint).center =
    unitPoint (Γ := Γ) := rfl

theorem empty_has_no_point (x : Γ.Elements) :
    ¬ Nonempty (Term (constantFamily Γ PEmpty.{u+1})) := by
  rintro ⟨a⟩
  exact (a.val x).elim

end Cartesian

namespace Presheaf.LawCases
open SquareKit.Cubical.Presheaf StructureIdentity.Native
open Examples.NativeStructureDescriptions Examples.NativeStructureDescriptions.Presheaf
variable {Γ : Context.{1}}

def identitySelected : Term (family pointedUnary (boolCarrier (Γ := Γ))) :=
  Term.map pointedPresentation.inv ⟨fun _ => ⟨(false, id)⟩, fun _ => rfl⟩

def fixedPointWitness : Term (lawFamily fixedPointLaw (identitySelected (Γ := Γ)) unitContext) :=
  homogeneousRefl (sigmaFst identitySelected)

def identityWitness : Term (lawFamily identityLaw (identitySelected (Γ := Γ)) unitContext) :=
  lam (homogeneousRefl (generic (boolCarrier (Γ := Γ))))

def lawfulModel : Term (modelsFamily fixedPointSpecification (boolCarrier (Γ := Γ))) :=
  sigmaIntro identitySelected
    (Term.map (EquivalenceFamilies.homogeneousReindexIso _ _ _ _).inv fixedPointWitness)

theorem negation_rejects_fixed_point (x : Γ.Elements) :
    ¬ Nonempty (Term (lawFamily fixedPointLaw (selected (Γ := Γ)) unitContext)) := by
  rintro ⟨p⟩
  have h := discretePath_endpoints p
  have h' := congrArg (fun s => (s.val x).down) h
  contradiction

def trueWitness : Term (lawFamily (Formula.holds (.fixed True))
    (identitySelected (Γ := Γ)) (unitContext (A := boolCarrier))) :=
  ⟨fun _ => ⟨⟨True.intro⟩⟩, fun _ => rfl⟩

theorem false_has_no_witness (x : Γ.Elements) :
    ¬ Nonempty (Term (lawFamily (Formula.holds (.fixed False))
      (identitySelected (Γ := Γ)) (unitContext (A := boolCarrier)))) := by
  rintro ⟨p⟩
  exact (p.val x).down.down

variable {Δ : Context.{1}}

def identityAt (a : Γ ⟶ smallFamilyCodes.{0})
    (x : Term (SmallUniverse.liftedDecode a)) : Term (family pointedUnary (SmallUniverse.liftedDecode a)) :=
  sigmaIntro x (lam (generic (SmallUniverse.liftedDecode a)))

noncomputable def genericPointedModel (a : Γ ⟶ smallFamilyCodes.{0})
    (sA : Term (HomotopyLevels.isSet (SmallUniverse.liftedDecode a)))
    (x : Term (SmallUniverse.liftedDecode a)) : Term (modelObjects fixedPointSpecification Γ) :=
  modelObject fixedPointSpecification a (identityAt a x) sA (homogeneousRefl x)

noncomputable example (a : Γ ⟶ smallFamilyCodes.{0})
    (sA : Term (HomotopyLevels.isSet (SmallUniverse.liftedDecode a)))
    (x : Term (SmallUniverse.liftedDecode a)) :
    HomotopyEquivalence (HomotopyLevels.pathMap (PropositionExtension.first
      (objectConditions fixedPointSpecification Γ)) (genericPointedModel a sA x) (genericPointedModel a sA x)) :=
  modelPathProjectionEquivalence fixedPointSpecification _ _

private def pointObjectMap (a : Γ ⟶ smallFamilyCodes.{0}) :
    SmallUniverse.liftedDecode a ⟶ objects pointedUnary Γ :=
  let A := SmallUniverse.liftedDecode a
  let U := SmallUniverse.family Γ
  let C := SmallUniverse.liftedDecode (SmallUniverse.code (generic U))
  let σ := pair (A := U) (𝟙 Γ) (SmallUniverse.term a)
  let π := projection A
  let fields : Term (reindex (family pointedUnary A) π) :=
    sigmaIntro (B := reindex (reindex (pi A (reindex A (projection A))) π)
      (projection (reindex A π))) (generic A) (Term.reindex (lam (generic A)) π)
  IntervalTransport.mapOfSection
    (sigmaIntro (B := reindex (family pointedUnary C) (liftSub U π))
      (Term.reindex (SmallUniverse.term a) π)
      (Term.map (Functor.whiskerLeft π.mapElements (reindexIso pointedUnary C σ).inv) fields))

private theorem pointObjectMap_apply (a : Γ ⟶ smallFamilyCodes.{0})
    (x : Term (SmallUniverse.liftedDecode a)) :
    Term.map (pointObjectMap a) x = objectOf pointedUnary a (identityAt a x) := by
  apply Term.ext
  intro γ
  rfl

/-- Vary the chosen fixed point along its complete native path, keeping the operation identity. -/
def pointedRawPath (a : Γ ⟶ smallFamilyCodes.{0})
    (x y : Term (SmallUniverse.liftedDecode a))
    (p : Term (homogeneousPath (SmallUniverse.liftedDecode a) x y)) :
    Term (homogeneousPath (objects pointedUnary Γ)
      (objectOf pointedUnary a (identityAt a x))
      (objectOf pointedUnary a (identityAt a y))) := by
  rw [← pointObjectMap_apply a x, ← pointObjectMap_apply a y]
  exact Term.map (HomotopyLevels.pathMap (pointObjectMap a) x y) p

/-- The native proposition extension reconstructs the fixed-point law along this path. -/
noncomputable def pointedModelPath (a : Γ ⟶ smallFamilyCodes.{0})
    (sA : Term (HomotopyLevels.isSet (SmallUniverse.liftedDecode a)))
    (x y : Term (SmallUniverse.liftedDecode a))
    (p : Term (homogeneousPath (SmallUniverse.liftedDecode a) x y)) :
    Term (homogeneousPath (modelObjects fixedPointSpecification Γ)
      (genericPointedModel a sA x) (genericPointedModel a sA y)) :=
  Term.map (StructuredIdentity.UaComparison.modelPathInverse fixedPointSpecification _ _)
    (pointedRawPath a x y p)

/-- Forgetting the reconstructed law recovers the whole raw structure path. -/
noncomputable def pointedModelPath_projection (a : Γ ⟶ smallFamilyCodes.{0})
    (sA : Term (HomotopyLevels.isSet (SmallUniverse.liftedDecode a)))
    (x y : Term (SmallUniverse.liftedDecode a))
    (p : Term (homogeneousPath (SmallUniverse.liftedDecode a) x y)) :
    Term (homogeneousPath (homogeneousPath (objects pointedUnary Γ)
      (objectOf pointedUnary a (identityAt a x)) (objectOf pointedUnary a (identityAt a y)))
      (Term.map (HomotopyLevels.pathMap (PropositionExtension.first (objectConditions fixedPointSpecification Γ))
        (genericPointedModel a sA x) (genericPointedModel a sA y))
        (pointedModelPath a sA x y p))
      (pointedRawPath a x y p)) :=
  StructuredIdentity.UaComparison.modelPathInverse_projection fixedPointSpecification
    (genericPointedModel a sA x) (genericPointedModel a sA y) (pointedRawPath a x y p)

/-- The final model SIP recovers this law-bearing path through independent preservation. -/
noncomputable def pointedModelPath_roundtrip (a : Γ ⟶ smallFamilyCodes.{0})
    (sA : Term (HomotopyLevels.isSet (SmallUniverse.liftedDecode a)))
    (x y : Term (SmallUniverse.liftedDecode a))
    (p : Term (homogeneousPath (SmallUniverse.liftedDecode a) x y)) :
    Term (homogeneousPath
      (homogeneousPath (modelObjects fixedPointSpecification Γ)
        (genericPointedModel a sA x) (genericPointedModel a sA y))
      (Term.map (StructuredIdentity.UaComparison.modelMap fixedPointSpecification
        (genericPointedModel a sA x) (genericPointedModel a sA y))
        (Term.map (StructuredIdentity.UaComparison.modelInverse fixedPointSpecification
          (genericPointedModel a sA x) (genericPointedModel a sA y))
          (pointedModelPath a sA x y p)))
      (pointedModelPath a sA x y p)) :=
  StructuredIdentity.UaComparison.modelRightInverseAt fixedPointSpecification
    (genericPointedModel a sA x) (genericPointedModel a sA y) (pointedModelPath a sA x y p)


theorem quantified_reindex_roundtrip (σ : Δ ⟶ Γ) :
    let i := lawReindexIso identityLaw (identitySelected (Γ := Γ)) unitContext σ
    Term.map i.inv (Term.map i.hom (Term.reindex identityWitness σ)) = Term.reindex identityWitness σ := by
  apply Term.ext
  intro x
  exact (lawReindexIso identityLaw (identitySelected (Γ := Γ)) unitContext σ).hom_inv_id_app_apply x _

end Presheaf.LawCases

namespace Cartesian.LawCases
open SquareKit.Cubical.Cartesian StructureIdentity.Native
open Examples.NativeStructureDescriptions Examples.NativeStructureDescriptions.Cartesian
variable {Γ : Context.{1}}

def identitySelected : Term (family pointedUnary (boolCarrier (Γ := Γ))) :=
  Term.map pointedPresentation.inv ⟨fun _ => ⟨(false, id)⟩, fun _ => rfl⟩

def fixedPointWitness : Term (lawFamily fixedPointLaw (identitySelected (Γ := Γ)) unitContext) :=
  homogeneousRefl (sigmaFst identitySelected)

def identityWitness : Term (lawFamily identityLaw (identitySelected (Γ := Γ)) unitContext) :=
  lam (homogeneousRefl (generic (boolCarrier (Γ := Γ))))

def lawfulModel : Term (modelsFamily fixedPointSpecification (boolCarrier (Γ := Γ))) :=
  sigmaIntro identitySelected
    (Term.map (EquivalenceFamilies.homogeneousReindexIso _ _ _ _).inv fixedPointWitness)

theorem negation_rejects_fixed_point (x : Γ.Elements) :
    ¬ Nonempty (Term (lawFamily fixedPointLaw (selected (Γ := Γ)) unitContext)) := by
  rintro ⟨p⟩
  have h := (congrArg (fun t => t.val x) (pathApp_zero p)).symm.trans
    ((constant_section_interval (pathApp p) x ((endpoint Γ false).val x)
      ((endpoint Γ true).val x)).trans (congrArg (fun t => t.val x) (pathApp_one p)))
  have h' := congrArg ULift.down h
  contradiction

def trueWitness : Term (lawFamily (Formula.holds (.fixed True))
    (identitySelected (Γ := Γ)) (unitContext (A := boolCarrier))) :=
  ⟨fun _ => ⟨⟨True.intro⟩⟩, fun _ => rfl⟩

theorem false_has_no_witness (x : Γ.Elements) :
    ¬ Nonempty (Term (lawFamily (Formula.holds (.fixed False))
      (identitySelected (Γ := Γ)) (unitContext (A := boolCarrier)))) := by
  rintro ⟨p⟩
  exact (p.val x).down.down

variable {Δ : Context.{1}}

def identityAt (a : Γ ⟶ smallFamilyCodes.{0})
    (x : Term (SmallUniverse.liftedDecode a)) : Term (family pointedUnary (SmallUniverse.liftedDecode a)) :=
  sigmaIntro x (lam (generic (SmallUniverse.liftedDecode a)))

noncomputable def genericPointedModel (a : Γ ⟶ smallFamilyCodes.{0})
    (sA : Term (HomotopyLevels.isSet (SmallUniverse.liftedDecode a)))
    (x : Term (SmallUniverse.liftedDecode a)) : Term (modelObjects fixedPointSpecification Γ) :=
  modelObject fixedPointSpecification a (identityAt a x) sA (homogeneousRefl x)

noncomputable example (a : Γ ⟶ smallFamilyCodes.{0})
    (sA : Term (HomotopyLevels.isSet (SmallUniverse.liftedDecode a)))
    (x : Term (SmallUniverse.liftedDecode a)) :
    HomotopyEquivalence (HomotopyLevels.pathMap (PropositionExtension.first
      (objectConditions fixedPointSpecification Γ)) (genericPointedModel a sA x) (genericPointedModel a sA x)) :=
  modelPathProjectionEquivalence fixedPointSpecification _ _

private def pointObjectMap (a : Γ ⟶ smallFamilyCodes.{0}) :
    SmallUniverse.liftedDecode a ⟶ objects pointedUnary Γ :=
  let A := SmallUniverse.liftedDecode a
  let U := SmallUniverse.family Γ
  let C := SmallUniverse.liftedDecode (SmallUniverse.code (generic U))
  let σ := pair (A := U) (𝟙 Γ) (SmallUniverse.term a)
  let π := projection A
  let fields : Term (reindex (family pointedUnary A) π) :=
    sigmaIntro (B := reindex (reindex (pi A (reindex A (projection A))) π)
      (projection (reindex A π))) (generic A) (Term.reindex (lam (generic A)) π)
  IntervalTransport.mapOfSection
    (sigmaIntro (B := reindex (family pointedUnary C) (liftSub U π))
      (Term.reindex (SmallUniverse.term a) π)
      (Term.map (Functor.whiskerLeft π.mapElements (reindexIso pointedUnary C σ).inv) fields))

private theorem pointObjectMap_apply (a : Γ ⟶ smallFamilyCodes.{0})
    (x : Term (SmallUniverse.liftedDecode a)) :
    Term.map (pointObjectMap a) x = objectOf pointedUnary a (identityAt a x) := by
  apply Term.ext
  intro γ
  rfl

/-- Vary the chosen fixed point along its complete native path, keeping the operation identity. -/
def pointedRawPath (a : Γ ⟶ smallFamilyCodes.{0})
    (x y : Term (SmallUniverse.liftedDecode a))
    (p : Term (homogeneousPath (SmallUniverse.liftedDecode a) x y)) :
    Term (homogeneousPath (objects pointedUnary Γ)
      (objectOf pointedUnary a (identityAt a x))
      (objectOf pointedUnary a (identityAt a y))) := by
  rw [← pointObjectMap_apply a x, ← pointObjectMap_apply a y]
  exact Term.map (HomotopyLevels.pathMap (pointObjectMap a) x y) p

/-- The native proposition extension reconstructs the fixed-point law along this path. -/
noncomputable def pointedModelPath (a : Γ ⟶ smallFamilyCodes.{0})
    (sA : Term (HomotopyLevels.isSet (SmallUniverse.liftedDecode a)))
    (x y : Term (SmallUniverse.liftedDecode a))
    (p : Term (homogeneousPath (SmallUniverse.liftedDecode a) x y)) :
    Term (homogeneousPath (modelObjects fixedPointSpecification Γ)
      (genericPointedModel a sA x) (genericPointedModel a sA y)) :=
  Term.map (StructuredIdentity.UaComparison.modelPathInverse fixedPointSpecification _ _)
    (pointedRawPath a x y p)

/-- Forgetting the reconstructed law recovers the whole raw structure path. -/
noncomputable def pointedModelPath_projection (a : Γ ⟶ smallFamilyCodes.{0})
    (sA : Term (HomotopyLevels.isSet (SmallUniverse.liftedDecode a)))
    (x y : Term (SmallUniverse.liftedDecode a))
    (p : Term (homogeneousPath (SmallUniverse.liftedDecode a) x y)) :
    Term (homogeneousPath (homogeneousPath (objects pointedUnary Γ)
      (objectOf pointedUnary a (identityAt a x)) (objectOf pointedUnary a (identityAt a y)))
      (Term.map (HomotopyLevels.pathMap (PropositionExtension.first (objectConditions fixedPointSpecification Γ))
        (genericPointedModel a sA x) (genericPointedModel a sA y))
        (pointedModelPath a sA x y p))
      (pointedRawPath a x y p)) :=
  StructuredIdentity.UaComparison.modelPathInverse_projection fixedPointSpecification
    (genericPointedModel a sA x) (genericPointedModel a sA y) (pointedRawPath a x y p)

/-- The final model SIP recovers this law-bearing path through independent preservation. -/
noncomputable def pointedModelPath_roundtrip (a : Γ ⟶ smallFamilyCodes.{0})
    (sA : Term (HomotopyLevels.isSet (SmallUniverse.liftedDecode a)))
    (x y : Term (SmallUniverse.liftedDecode a))
    (p : Term (homogeneousPath (SmallUniverse.liftedDecode a) x y)) :
    Term (homogeneousPath
      (homogeneousPath (modelObjects fixedPointSpecification Γ)
        (genericPointedModel a sA x) (genericPointedModel a sA y))
      (Term.map (StructuredIdentity.UaComparison.modelMap fixedPointSpecification
        (genericPointedModel a sA x) (genericPointedModel a sA y))
        (Term.map (StructuredIdentity.UaComparison.modelInverse fixedPointSpecification
          (genericPointedModel a sA x) (genericPointedModel a sA y))
          (pointedModelPath a sA x y p)))
      (pointedModelPath a sA x y p)) :=
  StructuredIdentity.UaComparison.modelRightInverseAt fixedPointSpecification
    (genericPointedModel a sA x) (genericPointedModel a sA y) (pointedModelPath a sA x y p)


theorem quantified_reindex_roundtrip (σ : Δ ⟶ Γ) :
    let i := lawReindexIso identityLaw (identitySelected (Γ := Γ)) unitContext σ
    Term.map i.inv (Term.map i.hom (Term.reindex identityWitness σ)) = Term.reindex identityWitness σ := by
  apply Term.ext
  intro x
  exact (lawReindexIso identityLaw (identitySelected (Γ := Γ)) unitContext σ).hom_inv_id_app_apply x _

end Cartesian.LawCases
end Examples.NativeStructureLaws
