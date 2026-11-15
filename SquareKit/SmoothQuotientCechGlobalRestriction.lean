import SquareKit.SmoothQuotientCechGlobalEquivalence
import SquareKit.SmoothQuotientCechGeneratedLocal
import SquareKit.Internal.PathTransport.AlignedSignatureComparisonLaws

/-! Selected recovery for global restriction of generated Čech interpretations. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechGlobal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

def restrictedSignature := alignedUniverseSignature
  ((baseEquivalence a A).functor ⋙ restriction (SplitSheaf.p A))
  (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
  (family a (SplitSheaf.Ext A)) (restrictedFiber a A)

theorem context_restriction (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    (contextEquivalence a A hΓ).functor ⋙
      SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.p A) =
        generatedContextMap (restrictedSignature a A) hΓ :=
  Context.relabel_composition
    (GeneratedComposition.generatedCtx (signature a A)
      (SmoothQuotientComparison.signature (a := a) (SplitSheaf.p A)) rfl HEq.rfl hΓ)
    _ _ _ _ _ _

def restrictionComparison (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    (contextEquivalence a A hΓ).functor ⋙
      SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.p A) ≅
        SmoothQuotientCechLocal.localMap a A hΓ :=
  eqToIso (context_restriction a A hΓ) ≪≫ contextLocalComparison a A hΓ

theorem primitiveRestrictionOverlap_eq :
    ((baseEquivalence a A).functor ⋙ restriction (SplitSheaf.p A)) ⋙
      restriction (SplitSheaf.Cech.first A) =
    ((baseEquivalence a A).functor ⋙ restriction (SplitSheaf.p A)) ⋙
      restriction (SplitSheaf.Cech.second A) := rfl

/-- The selected local recovery respects the original supplied overlap arrow. -/
theorem localComparison_overlap :
    isoWhiskerRight (localComparison a A) (restriction (SplitSheaf.Cech.first A)) ≪≫
      SmoothQuotientCechLocal.overlap a A =
    eqToIso (primitiveRestrictionOverlap_eq a A) ≪≫
      isoWhiskerRight (localComparison a A) (restriction (SplitSheaf.Cech.second A)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext d
  apply SheafActionQuotient.Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x p
  exact SheafTorsor.Descent.evaluation_transport d.toDescent.torsorDatum
    (X.obj.elementsMk x.obj x.val.1.1) x.val.1.2 x.val.2 p

def parameterRestrictedFiber {Y : Sheaf topology Type} (f : Y ⟶ SplitSheaf.Ext A) :=
  restrictedFiber a A ≫ whiskerLeft
    ((baseEquivalence a A).functor ⋙ restriction (SplitSheaf.p A)) (restrictionFamily f)

theorem localComparison_restrict_square {Y : Sheaf topology Type} (f : Y ⟶ SplitSheaf.Ext A) :
    parameterRestrictedFiber a A f ≫
      whiskerRight (isoWhiskerRight (localComparison a A) (restriction f)).hom (family a Y) =
        SmoothQuotientCechLocal.parameterFiber a A f := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  change transport ((localComparison a A).hom.app d |>.reindex f)
    (restrict f ((restrictedFiber a A).app d x)) = restrict f x.val
  rw [← transport_restrict]
  exact congrArg (restrict f)
    (CocycleDatum.ofFiber d.toDescent (SmoothQuotientDeformations.Cech.fiberEquiv d x)).recover


def parameterRecovery (hΓ : Typed.CtxDeriv.{2} Γ γ)
    {Y : Sheaf topology Type} (f : Y ⟶ SplitSheaf.Ext A) :=
  alignedContextComparison (isoWhiskerRight (localComparison a A) (restriction f))
    (SmoothQuotientDeformations.Cech.family (a := a) (A := A)) (family a Y)
    (parameterRestrictedFiber a A f) (SmoothQuotientCechLocal.parameterFiber a A f)
    (localComparison_restrict_square a A f) hΓ

theorem primitiveRecovery_cocycle :
    isoWhiskerRight (localComparison a A) (restriction (SplitSheaf.Cech.first A)) ≪≫
      SmoothQuotientCechLocal.overlap a A =
    isoWhiskerRight (localComparison a A) (restriction (SplitSheaf.Cech.second A)) := by
  simpa only [eqToIso_refl, Iso.refl_trans] using localComparison_overlap a A

/-- The primitive recovery triangle records every endpoint identification before
lifting, keeping concrete generated interpretation normalization outside the proof. -/
def recoveryTriangle : AlignedTriangle
    (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
    (family a (SplitSheaf.Cech.double A)) where
  F₁ := ((baseEquivalence a A).functor ⋙ restriction (SplitSheaf.p A)) ⋙
    restriction (SplitSheaf.Cech.first A)
  F₂ := SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.first A)
  G₁ := SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.first A)
  G₂ := SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.second A)
  H₁ := ((baseEquivalence a A).functor ⋙ restriction (SplitSheaf.p A)) ⋙
    restriction (SplitSheaf.Cech.second A)
  H₂ := SheafActionQuotient.Cech.localFunctor ⋙ restriction (SplitSheaf.Cech.second A)
  η := isoWhiskerRight (localComparison a A) (restriction (SplitSheaf.Cech.first A))
  θ := SmoothQuotientCechLocal.overlap a A
  ζ := isoWhiskerRight (localComparison a A) (restriction (SplitSheaf.Cech.second A))
  α := parameterRestrictedFiber a A (SplitSheaf.Cech.first A)
  β := SmoothQuotientCechLocal.firstFiber a A
  β' := SmoothQuotientCechLocal.firstFiber a A
  δ := SmoothQuotientCechLocal.secondFiber a A
  α' := parameterRestrictedFiber a A (SplitSheaf.Cech.second A)
  δ' := SmoothQuotientCechLocal.secondFiber a A
  hm := rfl
  hf := primitiveRestrictionOverlap_eq a A
  hl := rfl
  ha := HEq.rfl
  hb := HEq.rfl
  hd := HEq.rfl
  cocycle := by
    simpa only [eqToIso_refl, Iso.trans_refl, Iso.refl_symm, Iso.refl_trans] using
      primitiveRecovery_cocycle a A
  squareη := localComparison_restrict_square a A (SplitSheaf.Cech.first A)
  squareθ := SmoothQuotientCechLocal.overlap_square a A
  squareζ := localComparison_restrict_square a A (SplitSheaf.Cech.second A)



end SquareKit.SmoothQuotientCechGlobal
