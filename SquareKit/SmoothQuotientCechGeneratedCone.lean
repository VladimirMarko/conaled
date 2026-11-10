import SquareKit.SmoothQuotientCechGeneratedMatching
import SquareKit.SmoothQuotientCechGeneratedCocycle
import SquareKit.Internal.PathTransport.CechMatchingCone

/-! A selected matching cone for every generated context. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

theorem generatedOverlap_cocycle (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    isoWhiskerRight (generatedOverlap a A hΓ)
        (SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.firstSecond A)) ≪≫
      isoWhiskerLeft (localMap a A hΓ)
        (eqToIso (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).tripleMiddle) ≪≫
      isoWhiskerRight (generatedOverlap a A hΓ)
        (SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.secondThird A)) =
    isoWhiskerLeft (localMap a A hΓ)
        (eqToIso (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).tripleFirst) ≪≫
      isoWhiskerRight (generatedOverlap a A hΓ)
        (SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.firstThird A)) ≪≫
      isoWhiskerLeft (localMap a A hΓ)
        (eqToIso (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).tripleLast) := by
  rw [generatedOverlap_restrict, generatedOverlap_restrict, generatedOverlap_restrict]
  rw [leftEq (localMap a A hΓ)
    (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).tripleMiddle
    (congrArg (fun F => localMap a A hΓ ⋙ F)
      (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).tripleMiddle)]
  rw [leftEq (localMap a A hΓ)
    (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).tripleFirst
    (congrArg (fun F => localMap a A hΓ ⋙ F)
      (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).tripleFirst)]
  rw [leftEq (localMap a A hΓ)
    (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).tripleLast
    (congrArg (fun F => localMap a A hΓ ⋙ F)
      (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).tripleLast)]
  exact tripleRelabelForward
    (restrictedComparison a A hΓ (SplitSheaf.Cech.firstSecond A))
    (restrictedComparison a A hΓ (SplitSheaf.Cech.secondThird A))
    (restrictedComparison a A hΓ (SplitSheaf.Cech.firstThird A))
    (localMap_twice a A hΓ (SplitSheaf.Cech.first A) (SplitSheaf.Cech.firstSecond A))
    (localMap_twice a A hΓ (SplitSheaf.Cech.second A) (SplitSheaf.Cech.firstSecond A))
    (localMap_twice a A hΓ (SplitSheaf.Cech.first A) (SplitSheaf.Cech.secondThird A))
    (localMap_twice a A hΓ (SplitSheaf.Cech.second A) (SplitSheaf.Cech.secondThird A))
    (localMap_twice a A hΓ (SplitSheaf.Cech.first A) (SplitSheaf.Cech.firstThird A))
    (localMap_twice a A hΓ (SplitSheaf.Cech.second A) (SplitSheaf.Cech.firstThird A))
    (tripleMiddleMap a A hΓ) (tripleFirstMap a A hΓ) (tripleLastMap a A hΓ)
    _ _ _ (restrictedComparison_cocycle a A hΓ)

theorem generatedConeLaws (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    CechMatching.ConeLaws (D := SmoothQuotientGeneratedMatching.diagram a hΓ A)
      (localMap a A hΓ) (generatedOverlap a A hΓ) where
  diagonal := generatedOverlap_diagonal a A hΓ
  cocycle := generatedOverlap_cocycle a A hΓ

def matchingEvaluation (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    (show Grpd.{1,1} from γ (model a A)) ⥤ SmoothQuotientGeneratedMatching.Datum a hΓ A :=
  CechMatching.coneFunctor (localMap a A hΓ) (generatedOverlap a A hΓ)
    (generatedConeLaws a A hΓ)

@[simp] theorem matchingEvaluation_local (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    matchingEvaluation a A hΓ ⋙ CechMatching.Datum.localFunctor = localMap a A hΓ := rfl

@[simp] theorem matchingEvaluation_overlap (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (c : (show Grpd.{1,1} from γ (model a A))) :
    ((matchingEvaluation a A hΓ).obj c).overlap = (generatedOverlap a A hΓ).app c := rfl

end SquareKit.SmoothQuotientCechLocal
