import SquareKit.SmoothQuotientCechFamilyEffectivity
import SquareKit.SmoothQuotientCechGeneratedEffectivity
import SquareKit.SmoothQuotientCechGeneratedEmpty
import SquareKit.SmoothQuotientCechGlobalMatching
import SquareKit.Internal.PathTransport.TypedContextNormalization

/-! Effective matching and actual restriction for every generated context. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

theorem matchingEvaluation_derivation_iff (hΓ kΓ : Typed.CtxDeriv.{2} Γ γ) :
    (matchingEvaluation a A hΓ).IsEquivalence ↔ (matchingEvaluation a A kΓ).IsEquivalence :=
  CechMatching.functor_equivalence_iff
    (congrArg CechMatching.StrictDiagram.toDiagram
      (SmoothQuotientGeneratedMatching.strictDiagram_derivation a A hΓ kΓ))
    (matchingEvaluation_derivation a A hΓ kΓ)

theorem plainContextEvaluation_isEquivalence (hΓ : Typed.PlainCtxDeriv.{2} Γ γ) :
    (matchingEvaluation a A hΓ.derivation).IsEquivalence := by
  induction hΓ with
  | empty => exact matchingEvaluation_empty_equivalence a A
  | ext hΓ hB ih =>
      let := ih
      exact matchingEvaluation_ext_isEquivalence a A hΓ.derivation hB
        (familyEvaluation_isEquivalence a A hB hΓ.derivation)

theorem matchingEvaluation_isEquivalence (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    (matchingEvaluation a A hΓ).IsEquivalence :=
  (matchingEvaluation_derivation_iff a A hΓ hΓ.normalize.derivation).mpr
    (plainContextEvaluation_isEquivalence a A hΓ.normalize)

def evaluationEquivalence (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    (show Grpd.{1,1} from γ (model a A)) ≌ SmoothQuotientGeneratedMatching.Datum a hΓ A := by
  let := matchingEvaluation_isEquivalence a A hΓ
  exact (matchingEvaluation a A hΓ).asEquivalence

end SquareKit.SmoothQuotientCechLocal

namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

theorem restriction_isEquivalence (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    (restrictionFunctor a hΓ A).IsEquivalence := by
  let := SmoothQuotientCechLocal.matchingEvaluation_isEquivalence a A hΓ
  exact SmoothQuotientCechGlobal.restrictionFunctor_isEquivalence a A hΓ

def descentEquivalence (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    context a hΓ X ≌ Datum a hΓ A := by
  let := restriction_isEquivalence a A hΓ
  exact (restrictionFunctor a hΓ A).asEquivalence

end SquareKit.SmoothQuotientGeneratedMatching
