import SquareKit.SmoothQuotientCechGeneratedEffectivity
import SquareKit.Internal.PathTransport.SectionDescentResult
import SquareKit.Internal.PathTransport.CechMatchingComprehensionInverseProjection

/-! Section descent through the actual matching evaluation. The context and
fiber equivalence inputs are the remaining generated-effectivity obligations. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)

variable [(matchingEvaluation a A hΓ).IsEquivalence]
variable (families : ∀ c, (familyEvaluation a A hΓ hB c).IsEquivalence)

/-- The actual evaluated extension, expressed in the independent matching family. -/
def sectionTotalEquivalence :
    Extend (b (model a A)) ≌
      Extend (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ hB A) := by
  let : (totalMatchingEvaluation a A hΓ hB).IsEquivalence :=
    totalMatchingEvaluation_isEquivalence a A hΓ hB families
  exact (totalMatchingEvaluation a A hΓ hB).asEquivalence.trans
    (CechMatching.Comprehension.equivalence
      (SmoothQuotientGeneratedMatching.relativeFamilyData a hΓ hB A)
      (SmoothQuotientGeneratedMatching.relativeFamilyCoherence a hΓ hB A)).symm

def sectionTotalProjection :
    (sectionTotalEquivalence a A hΓ hB families).functor ⋙
        weaken (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ hB A) ≅
      weaken (b (model a A)) ⋙ matchingEvaluation a A hΓ :=
  isoWhiskerLeft (totalMatchingEvaluation a A hΓ hB)
    (CechMatching.Comprehension.inverseProjectionComparison
      (SmoothQuotientGeneratedMatching.relativeFamilyData a hΓ hB A)
      (SmoothQuotientGeneratedMatching.relativeFamilyCoherence a hΓ hB A)) ≪≫
      eqToIso (totalMatchingEvaluation_projection a A hΓ hB)

/-- The selected reconstruction, recovery and uniqueness laws are retained together. -/
def matchingSectionResult :
    SectionDescent.Result (matchingEvaluation a A hΓ).asEquivalence
      (sectionTotalEquivalence a A hΓ hB families)
      (sectionTotalProjection a A hΓ hB families) :=
  SectionDescent.result _ _ _


end SquareKit.SmoothQuotientCechLocal
