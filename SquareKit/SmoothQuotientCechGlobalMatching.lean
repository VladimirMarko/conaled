import SquareKit.SmoothQuotientCechGlobalCoherence
import SquareKit.SmoothQuotientCechGeneratedCone
import SquareKit.Internal.PathTransport.CechMatchingConeComparison

/-! The actual canonical restriction functor agrees with independent matching evaluation. -/
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

theorem restrictionComparison_overlap (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    isoWhiskerRight (restrictionComparison a A hΓ)
      (SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.first A)) ≪≫
        SmoothQuotientCechLocal.generatedOverlap a A hΓ =
    eqToIso (globalRestrictionOverlap_eq a A hΓ) ≪≫
      isoWhiskerRight (restrictionComparison a A hΓ)
        (SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.second A)) :=
  CechMatching.canonicalSquare_relabel
    (D := SmoothQuotientGeneratedMatching.diagram a hΓ A)
    (context_restriction a A hΓ) (contextLocalComparison a A hΓ)
    (SmoothQuotientCechLocal.generatedOverlap a A hΓ)
    (globalRestrictionOverlap_eq a A hΓ) (restrictedOverlap_eq a A hΓ)
    (contextLocalComparison_overlap a A hΓ)

/-- The component retains the selected local descent recovery arrow. -/
def matchingComparison (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    (contextEquivalence a A hΓ).functor ⋙
      SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ A ≅
        SmoothQuotientCechLocal.matchingEvaluation a A hΓ :=
  CechMatching.precomposedCanonicalComparison
    (D := SmoothQuotientGeneratedMatching.strictDiagram a hΓ A)
    (contextEquivalence a A hΓ).functor
    (SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.p A))
    (SmoothQuotientGeneratedMatching.restrictionOverlap_eq a hΓ A)
    (SmoothQuotientCechLocal.localMap a A hΓ) (SmoothQuotientCechLocal.generatedOverlap a A hΓ)
    (SmoothQuotientCechLocal.generatedConeLaws a A hΓ) (restrictionComparison a A hΓ)
    (by
      rw [leftEq (contextEquivalence a A hΓ).functor
        (SmoothQuotientGeneratedMatching.restrictionOverlap_eq a hΓ A)
        (globalRestrictionOverlap_eq a A hΓ)]
      exact restrictionComparison_overlap a A hΓ)

theorem restrictionFunctor_isEquivalence (hΓ : Typed.CtxDeriv.{2} Γ γ)
    [(SmoothQuotientCechLocal.matchingEvaluation a A hΓ).IsEquivalence] :
    (SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ A).IsEquivalence := by
  have : ((contextEquivalence a A hΓ).functor ⋙
      SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ A).IsEquivalence :=
    Functor.isEquivalence_of_iso (matchingComparison a A hΓ).symm
  exact Functor.isEquivalence_of_comp_left (contextEquivalence a A hΓ).functor
    (SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ A)

end SquareKit.SmoothQuotientCechGlobal
