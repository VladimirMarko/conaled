import SquareKit.SmoothQuotientCechGeneratedSubstitution
import SquareKit.SmoothQuotientGeneratedRelativeMatching
import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberFunctor

/-! Evaluation into independently defined dependent matching fibers. -/
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

/-- Evaluation on the extended context, expressed in the relative total diagram. -/
def totalMatchingEvaluation :=
  matchingEvaluation a A (.ext hΓ hB) ⋙
    (SmoothQuotientGeneratedMatching.generatedToRelative a hΓ hB A).functor

theorem totalMatchingEvaluation_projection :
    totalMatchingEvaluation a A hΓ hB ⋙
      ((SmoothQuotientGeneratedMatching.relativeFamilyData a hΓ hB A).projection
        (SmoothQuotientGeneratedMatching.relativeFamilyCoherence a hΓ hB A)).functor =
    Grothendieck.forget (b (model a A) ⋙ Grpd.forgetToCat) ⋙ matchingEvaluation a A hΓ := by
  have hp : (SmoothQuotientGeneratedMatching.generatedToRelative a hΓ hB A).functor ⋙
      ((SmoothQuotientGeneratedMatching.relativeFamilyData a hΓ hB A).projection
        (SmoothQuotientGeneratedMatching.relativeFamilyCoherence a hΓ hB A)).functor =
      SmoothQuotientGeneratedMatching.projection a hΓ hB A := by
    rw [← CechMatching.StrictMap.functor_comp]
    congr 1
  dsimp only [totalMatchingEvaluation]
  rw [Functor.assoc, hp]
  exact matchingEvaluation_substitution a A hΓ (.ext hΓ hB) (.weaken hΓ hB)

def fiberTotalEvaluation (c : (show Grpd.{1,1} from γ (model a A))) :=
  Grothendieck.ι (b (model a A) ⋙ Grpd.forgetToCat) c ⋙
    totalMatchingEvaluation a A hΓ hB

theorem fiberTotalEvaluation_projection (c : (show Grpd.{1,1} from γ (model a A))) :
    fiberTotalEvaluation a A hΓ hB c ⋙
      ((SmoothQuotientGeneratedMatching.relativeFamilyData a hΓ hB A).projection
        (SmoothQuotientGeneratedMatching.relativeFamilyCoherence a hΓ hB A)).functor =
    (Functor.const ((b (model a A)).obj c)).obj ((matchingEvaluation a A hΓ).obj c) := by
  dsimp only [fiberTotalEvaluation]
  rw [Functor.assoc, totalMatchingEvaluation_projection]
  exact CechMatching.Comprehension.inclusion_forget_comp
    (b (model a A)) (matchingEvaluation a A hΓ) c

/-- A source fiber evaluates to local fiber data with the prescribed base overlap. -/
def familyEvaluation (c : (show Grpd.{1,1} from γ (model a A))) :
    (b (model a A)).obj c ⥤
      (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ hB A).obj
        ((matchingEvaluation a A hΓ).obj c) :=
  CechMatching.Comprehension.fixedBaseFunctor _ _
    (fiberTotalEvaluation a A hΓ hB c) _ (fiberTotalEvaluation_projection a A hΓ hB c)

/-- Forgetting the dependent matching fiber recovers its complete total evaluation. -/
def familyEvaluation_total (c : (show Grpd.{1,1} from γ (model a A))) :
    familyEvaluation a A hΓ hB c ⋙ CechMatching.Comprehension.Fiber.forget ≅
      fiberTotalEvaluation a A hΓ hB c :=
  CechMatching.Comprehension.fixedBaseComparison _ _ _ _ _

end SquareKit.SmoothQuotientCechLocal
