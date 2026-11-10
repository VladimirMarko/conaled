import SquareKit.SmoothQuotientCechGeneratedFamilyEvaluation
import SquareKit.SmoothQuotientGeneratedBaseMatching
import SquareKit.Internal.PathTransport.CechMatchingConstantEvaluation

/-! The actual base-fiber evaluation recovers its independent coefficient datum. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ} (hΓ : Typed.CtxDeriv.{2} Γ γ)

def baseCoefficientProjection :=
  CechMatching.Comprehension.Constant.projectionOfEq
    (SmoothQuotientGeneratedMatching.relativeFamilyData_base a hΓ A)
    (SmoothQuotientGeneratedMatching.relativeFamilyCoherence a hΓ (.base hΓ) A)
    (SmoothQuotientGeneratedMatching.baseCoherence a hΓ A)

def baseEvaluationComparison (c : (show Grpd.{1,1} from γ (model a A))) :
    familyEvaluation a A hΓ (.base hΓ) c ⋙
        ((SmoothQuotientGeneratedMatching.baseFamilyIso a hΓ A).hom.app
          ((matchingEvaluation a A hΓ).obj c)) ≅
      fiberTotalEvaluation a A hΓ (.base hΓ) c ⋙
        (baseCoefficientProjection a A hΓ).functor :=
  CechMatching.Comprehension.Constant.fixedBaseCoefficientComparison _ _ _ _ _ _

end SquareKit.SmoothQuotientCechLocal
