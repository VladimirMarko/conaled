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
        (eqToIso (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).triple_middle) ≪≫
      isoWhiskerRight (generatedOverlap a A hΓ)
        (SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.secondThird A)) =
    isoWhiskerLeft (localMap a A hΓ)
        (eqToIso (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).triple_first) ≪≫
      isoWhiskerRight (generatedOverlap a A hΓ)
        (SmoothQuotientGeneratedMatching.restriction a hΓ (SplitSheaf.Cech.firstThird A)) ≪≫
      isoWhiskerLeft (localMap a A hΓ)
        (eqToIso (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).triple_last) := by
  rw [generatedOverlap_restrict, generatedOverlap_restrict, generatedOverlap_restrict]
  rw [isoWhiskerLeft_eqToIso (localMap a A hΓ)
    (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).triple_middle
    (congrArg (fun F => localMap a A hΓ ⋙ F)
      (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).triple_middle)]
  rw [isoWhiskerLeft_eqToIso (localMap a A hΓ)
    (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).triple_first
    (congrArg (fun F => localMap a A hΓ ⋙ F)
      (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).triple_first)]
  rw [isoWhiskerLeft_eqToIso (localMap a A hΓ)
    (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).triple_last
    (congrArg (fun F => localMap a A hΓ ⋙ F)
      (SmoothQuotientGeneratedMatching.strictDiagram a hΓ A).triple_last)]
  exact triple_relabel_forward
    (restrictedComparison a A hΓ (SplitSheaf.Cech.firstSecond A))
    (restrictedComparison a A hΓ (SplitSheaf.Cech.secondThird A))
    (restrictedComparison a A hΓ (SplitSheaf.Cech.firstThird A))
    (localMap_twice a A hΓ (SplitSheaf.Cech.first A) (SplitSheaf.Cech.firstSecond A))
    (localMap_twice a A hΓ (SplitSheaf.Cech.second A) (SplitSheaf.Cech.firstSecond A))
    (localMap_twice a A hΓ (SplitSheaf.Cech.first A) (SplitSheaf.Cech.secondThird A))
    (localMap_twice a A hΓ (SplitSheaf.Cech.second A) (SplitSheaf.Cech.secondThird A))
    (localMap_twice a A hΓ (SplitSheaf.Cech.first A) (SplitSheaf.Cech.firstThird A))
    (localMap_twice a A hΓ (SplitSheaf.Cech.second A) (SplitSheaf.Cech.firstThird A))
    (triple_middle_map a A hΓ) (triple_first_map a A hΓ) (triple_last_map a A hΓ)
    _ _ _ (restrictedComparison_cocycle a A hΓ)

theorem generated_coneLaws (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    CechMatching.ConeLaws (D := SmoothQuotientGeneratedMatching.diagram a hΓ A)
      (localMap a A hΓ) (generatedOverlap a A hΓ) where
  diagonal := generatedOverlap_diagonal a A hΓ
  cocycle := generatedOverlap_cocycle a A hΓ

def matchingEvaluation (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    (show Grpd.{1,1} from γ (model a A)) ⥤ SmoothQuotientGeneratedMatching.Datum a hΓ A :=
  CechMatching.coneFunctor (localMap a A hΓ) (generatedOverlap a A hΓ)
    (generated_coneLaws a A hΓ)

@[simp] theorem matchingEvaluation_local (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    matchingEvaluation a A hΓ ⋙ CechMatching.Datum.localFunctor = localMap a A hΓ := rfl

@[simp] theorem matchingEvaluation_overlap (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (c : (show Grpd.{1,1} from γ (model a A))) :
    ((matchingEvaluation a A hΓ).obj c).overlap = (generatedOverlap a A hΓ).app c := rfl

end SquareKit.SmoothQuotientCechLocal
