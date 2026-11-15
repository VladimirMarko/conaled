import SquareKit.SmoothQuotientCechGeneratedFamilyEvaluation
import SquareKit.Internal.PathTransport.CechMatchingPresentation
import SquareKit.Internal.PathTransport.GeneratedDerivationInvariance

/-! Derivation presentation does not alter generated matching data. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hB kB : Typed.TyDeriv.{2} Γ γ B b)

theorem strictDiagram_derivation (hΓ kΓ : Typed.CtxDeriv.{2} Γ γ) :
    strictDiagram a hΓ A = strictDiagram a kΓ A := by
  dsimp only [strictDiagram, restriction]
  congr 1

theorem relativeFamilyData_derivation :
    relativeFamilyData a hΓ hB A = relativeFamilyData a hΓ kB A := by
  dsimp only [relativeFamilyData, familyRestriction]
  congr 1

theorem generatedToRelative_derivation :
    HEq (generatedToRelative a hΓ hB A) (generatedToRelative a hΓ kB A) := by
  unfold generatedToRelative
  rfl

end SquareKit.SmoothQuotientGeneratedMatching

namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hB kB : Typed.TyDeriv.{2} Γ γ B b)

theorem generatedOverlap_derivation (hΓ kΓ : Typed.CtxDeriv.{2} Γ γ) :
    generatedOverlap a A hΓ = generatedOverlap a A kΓ := by
  dsimp only [generatedOverlap]
  rw [Comparison.alignedContextComparison_derivation (hΓ := hΓ) (kΓ := kΓ)]

theorem matchingEvaluation_derivation (hΓ kΓ : Typed.CtxDeriv.{2} Γ γ) :
    HEq (matchingEvaluation a A hΓ) (matchingEvaluation a A kΓ) := by
  exact CechMatching.coneFunctor_heq
    (congrArg CechMatching.StrictDiagram.toDiagram
      (SmoothQuotientGeneratedMatching.strictDiagram_derivation a A hΓ kΓ))
    (heq_of_eq (Comparison.generatedContextMap_derivation (signature a A) hΓ kΓ))
    (heq_of_eq (generatedOverlap_derivation a A hΓ kΓ)) _ _

theorem totalMatchingEvaluation_derivation :
    HEq (totalMatchingEvaluation a A hΓ hB) (totalMatchingEvaluation a A hΓ kB) := by
  exact CechMatching.mappedFunctor_heq
    (SmoothQuotientGeneratedMatching.strictDiagram_derivation a A (.ext hΓ hB) (.ext hΓ kB))
    (CechMatching.Comprehension.total_eq
      (SmoothQuotientGeneratedMatching.relativeFamilyData_derivation a A hΓ hB kB) _ _)
    (matchingEvaluation_derivation a A (.ext hΓ hB) (.ext hΓ kB))
    (SmoothQuotientGeneratedMatching.generatedToRelative_derivation a A hΓ hB kB)

theorem familyEvaluation_derivation_iff (c : (show Grpd.{1,1} from γ (model a A))) :
    (familyEvaluation a A hΓ hB c).IsEquivalence ↔
      (familyEvaluation a A hΓ kB c).IsEquivalence := by
  exact CechMatching.Comprehension.fixedBase_precomp_equivalence_iff
    (SmoothQuotientGeneratedMatching.relativeFamilyData_derivation a A hΓ hB kB) _ _
    (totalMatchingEvaluation_derivation a A hΓ hB kB) _ _ _ _

end SquareKit.SmoothQuotientCechLocal
