import SquareKit.Internal.PathTransport.CechMatchingComprehensionTermEvaluation
import SquareKit.SmoothQuotientGeneratedTermMatching
import SquareKit.SmoothQuotientCechGeneratedFamilyEvaluation
import SquareKit.Internal.PathTransport.GeneratedSectionSubstitution

/-! Actual evaluation commutes with independently descended term sections. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ B b x ξ} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hB : Typed.TyDeriv.{2} Γ γ B b) (hx : Typed.TmDeriv.{2} Γ γ B b x ξ)

theorem termDiagram_comp_relativeToGenerated :
    (termDiagram a hΓ hB hx A).comp (relativeToGenerated a hΓ hB A) =
      substitutionDiagram a (.ext hΓ hB) hΓ (Typed.SubDeriv.section hΓ hB hx) A := by
  apply CechMatching.StrictMap.ext
  · exact (Typed.sectionCode_universeLift (Object a (SplitSheaf.extension A))
      (SmoothQuotientDeformations.family a (SplitSheaf.extension A)) b ξ).symm
  · exact (Typed.sectionCode_universeLift (Object a (SplitSheaf.Cech.double A))
      (SmoothQuotientDeformations.family a (SplitSheaf.Cech.double A)) b ξ).symm
  · exact (Typed.sectionCode_universeLift (Object a (SplitSheaf.Cech.triple A))
      (SmoothQuotientDeformations.family a (SplitSheaf.Cech.triple A)) b ξ).symm

theorem section_matchingEvaluation :
    (ξ (model a A)).down.lift ⋙ matchingEvaluation a A (.ext hΓ hB) =
      matchingEvaluation a A hΓ ⋙ (termDiagram a hΓ hB hx A).functor ⋙
        (relativeToGenerated a hΓ hB A).functor := by
  have hh := matchingEvaluation_substitution a A (.ext hΓ hB) hΓ
    (Typed.SubDeriv.section hΓ hB hx)
  change matchingEvaluation a A hΓ ⋙
    (substitutionDiagram a (.ext hΓ hB) hΓ (Typed.SubDeriv.section hΓ hB hx) A).functor = _ at hh
  rw [← termDiagram_comp_relativeToGenerated a A hΓ hB hx, CechMatching.StrictMap.functor_comp] at hh
  have hs : ((Typed.sectionCode b ξ) (model a A)).down = (ξ (model a A)).down.lift :=
    Typed.sectionCode_universeLift (SheafActionQuotient.Cech.Datum (a := a) A)
      (SmoothQuotientDeformations.Cech.family (a := a) (A := A)) b ξ
  rw [hs] at hh
  exact hh.symm

theorem section_totalMatchingEvaluation :
    (ξ (model a A)).down.lift ⋙ totalMatchingEvaluation a A hΓ hB =
      matchingEvaluation a A hΓ ⋙ (termDiagram a hΓ hB hx A).functor := by
  have hh := congrArg (fun F => F ⋙ (generatedToRelative a hΓ hB A).functor)
    (section_matchingEvaluation a A hΓ hB hx)
  have hi : (relativeToGenerated a hΓ hB A).functor ⋙
      (generatedToRelative a hΓ hB A).functor = 𝟭 _ := by
    rw [← CechMatching.StrictMap.functor_comp]
    have he : (relativeToGenerated a hΓ hB A).comp (generatedToRelative a hΓ hB A) =
        CechMatching.StrictMap.id _ := CechMatching.StrictMap.ext _ _ rfl rfl rfl
    rw [he, CechMatching.StrictMap.functor_id]
  simpa only [totalMatchingEvaluation, Functor.assoc, hi, Functor.comp_id] using hh

/-- Whole term comparison and exact endpoint recovery, packaged before
specializing the dependent equality to concrete model expressions. -/
def familyEvaluationTermComparison :=
  CechMatching.Comprehension.termEvaluationComparison
    (relativeFamilyData a hΓ hB A) (relativeFamilyData_coherence a hΓ hB A)
    (b (model a A)) (totalMatchingEvaluation a A hΓ hB) (matchingEvaluation a A hΓ)
    (totalMatchingEvaluation_projection a A hΓ hB) (ξ (model a A)).down
    (termDiagram a hΓ hB hx A).functor (termDiagram_functor_projection a hΓ hB hx A)
    (section_totalMatchingEvaluation a A hΓ hB hx)

/-- The section endpoint expressed in the actual fixed-base total functor. -/
theorem section_fiber_endpoint (c : (show Grpd.{1,1} from γ (model a A))) :
    (fiberTotalEvaluation a A hΓ hB c).obj ((ξ (model a A)).down.obj c) =
      (termDiagram a hΓ hB hx A).functor.obj ((matchingEvaluation a A hΓ).obj c) :=
  CechMatching.Comprehension.section_fiber_endpoint
    (relativeFamilyData a hΓ hB A) (relativeFamilyData_coherence a hΓ hB A)
    (b (model a A)) (totalMatchingEvaluation a A hΓ hB) (matchingEvaluation a A hΓ)
    (ξ (model a A)).down (termDiagram a hΓ hB hx A).functor
    (section_totalMatchingEvaluation a A hΓ hB hx) c

end SquareKit.SmoothQuotientCechLocal
