import SquareKit.SmoothQuotientCechGlobalRestriction
import SquareKit.Internal.PathTransport.AlignedRecoverySquare

/-! Coherence of selected global recovery with generated overlap restriction. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechGlobal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

theorem parameterRecovery_postcompose (hΓ : Typed.CtxDeriv.{2} Γ γ)
    {Y : Sheaf topology Type} (f : Y ⟶ SplitSheaf.Ext A) :
    parameterRecovery a A hΓ f =
      (eqToIso (alignedGenerated_comp
        (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
        (family a (SplitSheaf.Ext A)) (restriction f) (family a Y)
        (restrictedFiber a A) (restrictionFamily f) hΓ)).symm ≪≫
      isoWhiskerRight (contextLocalComparison a A hΓ)
        (SmoothQuotientGeneratedMatching.restriction a hΓ f) ≪≫
      eqToIso (SmoothQuotientCechLocal.localMap_restriction a A hΓ f) :=
  alignedContextComparison_postcompose
    (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
    (family a (SplitSheaf.Ext A)) (restriction f) (family a Y)
    (localComparison a A) (restrictedFiber a A)
    (SmoothQuotientCechLocal.localFiber a A) (restrictionFamily f)
    (localComparison_square a A) (localComparison_restrict_square a A f) hΓ

theorem globalRestrictionOverlap_eq (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    ((contextEquivalence a A hΓ).functor ⋙
      SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.p A)) ⋙
        SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.first A) =
    ((contextEquivalence a A hΓ).functor ⋙
      SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.p A)) ⋙
        SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.second A) := by
  rw [Functor.assoc, Functor.assoc, SmoothQuotientGeneratedMatching.restrictionOverlap_eq]

theorem restrictedOverlap_eq (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    generatedContextMap (restrictedSignature a A) hΓ ⋙
        SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.first A) =
    generatedContextMap (restrictedSignature a A) hΓ ⋙
        SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.second A) := by
  rw [← context_restriction a A hΓ]
  exact globalRestrictionOverlap_eq a A hΓ

theorem contextLocalComparison_overlap (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    isoWhiskerRight (contextLocalComparison a A hΓ)
      (SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.first A)) ≪≫
        SmoothQuotientCechLocal.generatedOverlap a A hΓ =
    eqToIso (restrictedOverlap_eq a A hΓ) ≪≫
      isoWhiskerRight (contextLocalComparison a A hΓ)
        (SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.second A)) := by
  have h := alignedRecovery_square
    (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
    (family a (SplitSheaf.Ext A)) (family a (SplitSheaf.Cech.double A))
    (localComparison a A) (restriction (SplitSheaf.Cech.first A))
    (restriction (SplitSheaf.Cech.second A)) (SmoothQuotientCechLocal.overlap a A)
    (restrictedFiber a A) (SmoothQuotientCechLocal.localFiber a A)
    (restrictionFamily (SplitSheaf.Cech.first A)) (restrictionFamily (SplitSheaf.Cech.second A))
    (localComparison_square a A)
    (localComparison_restrict_square a A (SplitSheaf.Cech.first A))
    (localComparison_restrict_square a A (SplitSheaf.Cech.second A))
    (SmoothQuotientCechLocal.overlap_square a A)
    (primitiveRestrictionOverlap_eq a A) HEq.rfl (localComparison_overlap a A) hΓ
  apply Iso.ext
  simpa only [contextLocalComparison, SmoothQuotientCechLocal.generatedOverlap,
    Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    Category.assoc, eqToHom_trans, SmoothQuotientGeneratedMatching.restriction,
    SmoothQuotientComparison.signature, SmoothQuotientCechLocal.localMap,
    SmoothQuotientCechLocal.signature, SmoothQuotientCechLocal.firstFiber,
    SmoothQuotientCechLocal.secondFiber, SmoothQuotientCechLocal.parameterSignature,
    SmoothQuotientCechLocal.parameterFiber] using congrArg Iso.hom h

end SquareKit.SmoothQuotientCechGlobal
