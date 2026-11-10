import SquareKit.SmoothQuotientGeneratedRelativeSubstitution
import SquareKit.SmoothQuotientCechGeneratedFamilyEvaluation
import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberComposition

/-! The actual evaluation of a substituted family retains lifted substitution. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ Δ δ B b σ s} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hΔ : Typed.CtxDeriv.{2} Δ δ)
variable (hB : Typed.TyDeriv.{2} Γ γ B b) (hs : Typed.SubDeriv.{2} Δ δ Γ γ σ s)

theorem totalMatchingEvaluation_substitution :
    totalMatchingEvaluation a A hΔ (.sub hB hs) ⋙
      (relativeSubstitution a hΓ hΔ hB hs A).functor =
    Grothendieck.pre (b (model a A) ⋙ Grpd.forgetToCat) (s (model a A)).down ⋙
      totalMatchingEvaluation a A hΓ hB := by
  have hi : (generatedToRelative a hΔ (.sub hB hs) A).functor ⋙
      (relativeToGenerated a hΔ (.sub hB hs) A).functor = 𝟭 _ := by
    rw [← CechMatching.StrictMap.functor_comp]
    have he : (generatedToRelative a hΔ (.sub hB hs) A).comp
        (relativeToGenerated a hΔ (.sub hB hs) A) = CechMatching.StrictMap.id _ :=
      CechMatching.StrictMap.ext _ _ rfl rfl rfl
    rw [he, CechMatching.StrictMap.functor_id]
  have hh := matchingEvaluation_substitution a A (.ext hΓ hB) (.ext hΔ (.sub hB hs))
    (Typed.Authoring.liftSubstitution hΔ hB hs)
  change matchingEvaluation a A (.ext hΔ (.sub hB hs)) ⋙
    (substitutionDiagram a (.ext hΓ hB) (.ext hΔ (.sub hB hs))
      (Typed.Authoring.liftSubstitution hΔ hB hs) A).functor =
    Grothendieck.pre (b (model a A) ⋙ Grpd.forgetToCat) (s (model a A)).down ⋙
      matchingEvaluation a A (.ext hΓ hB) at hh
  dsimp only [relativeSubstitution, totalMatchingEvaluation]
  rw [CechMatching.StrictMap.functor_comp, CechMatching.StrictMap.functor_comp]
  simp only [Functor.assoc, ← Functor.assoc (generatedToRelative a hΔ (.sub hB hs) A).functor,
    hi, Functor.id_comp]
  rw [← Functor.assoc]
  exact congrArg (fun G => G ⋙ (generatedToRelative a hΓ hB A).functor) hh

theorem fiberTotalEvaluation_substitution (c : (show Grpd.{1,1} from δ (model a A))) :
    fiberTotalEvaluation a A hΔ (.sub hB hs) c ⋙
      (relativeSubstitution a hΓ hΔ hB hs A).functor =
    fiberTotalEvaluation a A hΓ hB ((s (model a A)).down.obj c) := by
  dsimp only [fiberTotalEvaluation]
  rw [Functor.assoc, totalMatchingEvaluation_substitution, ← Functor.assoc]
  exact congrArg (fun G => G ⋙ totalMatchingEvaluation a A hΓ hB)
    (inclusion_pre (b (model a A) ⋙ Grpd.forgetToCat) (s (model a A)).down c)

/-- Substitution preserves effectiveness of the actual evaluation at the selected base object. -/
theorem substitutionEvaluation_isEquivalence
    (c : (show Grpd.{1,1} from δ (model a A)))
    [(familyEvaluation a A hΓ hB ((s (model a A)).down.obj c)).IsEquivalence] :
    (familyEvaluation a A hΔ (.sub hB hs) c).IsEquivalence := by
  let S := substitutionDiagram a hΓ hΔ hs A
  let F := relativeSubstitution a hΓ hΔ hB hs A
  let sq := relativeSubstitution_projection a hΓ hΔ hB hs A
  have hf := relativeSubstitution_fiber_full a hΓ hΔ hB hs A
    ((matchingEvaluation a A hΔ).obj c)
  have : (CechMatching.Comprehension.fiberMap S F sq
      ((matchingEvaluation a A hΔ).obj c)).Full := hf.1
  have : (CechMatching.Comprehension.fiberMap S F sq
      ((matchingEvaluation a A hΔ).obj c)).Faithful := hf.2
  have : (CechMatching.Comprehension.fixedBaseFunctor
      (relativeFamilyData a hΓ hB A) (relativeFamilyCoherence a hΓ hB A)
      (fiberTotalEvaluation a A hΓ hB ((s (model a A)).down.obj c))
      ((matchingEvaluation a A hΓ).obj ((s (model a A)).down.obj c))
      (fiberTotalEvaluation_projection a A hΓ hB ((s (model a A)).down.obj c))).IsEquivalence :=
    inferInstanceAs (familyEvaluation a A hΓ hB ((s (model a A)).down.obj c)).IsEquivalence
  exact CechMatching.Comprehension.fixedBaseFunctor_isEquivalence_of_comp S F sq
    (fiberTotalEvaluation a A hΔ (.sub hB hs) c) _
    (fiberTotalEvaluation_projection a A hΔ (.sub hB hs) c)
    (fiberTotalEvaluation a A hΓ hB ((s (model a A)).down.obj c)) _
    (fiberTotalEvaluation_projection a A hΓ hB ((s (model a A)).down.obj c))
    (Functor.congr_obj (matchingEvaluation_substitution a A hΓ hΔ hs) c)
    (fiberTotalEvaluation_substitution a A hΓ hΔ hB hs c)

end SquareKit.SmoothQuotientCechLocal
