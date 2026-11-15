import SquareKit.SmoothQuotientCechGeneratedFamilyEvaluation
import SquareKit.Internal.PathTransport.CechMatchingComprehensionEffectivity

/-! The context-extension induction step for the actual evaluation functor. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)

/-- Equivalence on the evaluated context and its actual extracted fibers suffices. -/
theorem totalMatchingEvaluation_isEquivalence
    [(matchingEvaluation a A hΓ).IsEquivalence]
    (families : ∀ c, (familyEvaluation a A hΓ hB c).IsEquivalence) :
    (totalMatchingEvaluation a A hΓ hB).IsEquivalence :=
  CechMatching.Comprehension.Effectivity.isEquivalence
    (SmoothQuotientGeneratedMatching.relativeFamilyData a hΓ hB A)
    (SmoothQuotientGeneratedMatching.relativeFamilyCoherence a hΓ hB A)
    (b (model a A)) (totalMatchingEvaluation a A hΓ hB) (matchingEvaluation a A hΓ)
    (totalMatchingEvaluation_projection a A hΓ hB) families

/-- The induction conclusion concerns the original generated matching evaluation. -/
theorem matchingEvaluation_ext_isEquivalence
    [(matchingEvaluation a A hΓ).IsEquivalence]
    (families : ∀ c, (familyEvaluation a A hΓ hB c).IsEquivalence) :
    (matchingEvaluation a A (.ext hΓ hB)).IsEquivalence := by
  haveI : (matchingEvaluation a A (.ext hΓ hB) ⋙
      (SmoothQuotientGeneratedMatching.generatedToRelative a hΓ hB A).functor).IsEquivalence :=
    totalMatchingEvaluation_isEquivalence a A hΓ hB families
  haveI : (SmoothQuotientGeneratedMatching.generatedToRelative a hΓ hB A).functor.IsEquivalence :=
    (SmoothQuotientGeneratedMatching.relativeMatchingEquivalence a hΓ hB A).symm.isEquivalence_functor
  exact Functor.isEquivalence_of_comp_right (matchingEvaluation a A (.ext hΓ hB))
    (SmoothQuotientGeneratedMatching.generatedToRelative a hΓ hB A).functor

end SquareKit.SmoothQuotientCechLocal
