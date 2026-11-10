import SquareKit.SmoothQuotientCechPrimitiveEvaluation
import SquareKit.SmoothQuotientCechBaseTermEvaluation

/-! Primitive effectivity from the selected generated base-term comparison. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ t ξ} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hx : Typed.TmDeriv.{2} Γ γ .base (Typed.baseCode γ) t ξ)
variable (c : (show Grpd.{1,1} from γ (model a A)))
variable (q : (evaluatedBaseTerm a A hΓ hx).obj c = (sourceBaseTerm a A hx).obj c)

def primitiveRecoveryEquivalence :
    (relativeMatchingFamily a hΓ (.fiber hx) A).obj ((matchingEvaluation a A hΓ).obj c) ≌
      ((Typed.fiberCode ξ) (model a A)).obj c :=
  (primitiveCechMatchingEquivalence a A hΓ hx _).trans
    (Discrete.equivalence (Equiv.cast
      (congrArg (fun d => ULift.{1} (SmoothQuotientDeformations.Cech.Fiber d)) q)))

def primitiveEvaluationRecovery :
    familyEvaluation a A hΓ (.fiber hx) c ⋙ (primitiveRecoveryEquivalence a A hΓ hx c q).functor ≅
      𝟭 (((Typed.fiberCode ξ) (model a A)).obj c) :=
  NatIso.ofComponents (fun x => eqToIso (Discrete.ext
    (primitiveValue_cast_eq a A q _ x.as (primitiveEvaluation_matching_value a A hΓ hx c x))))
    (by
      intro x y f
      change @Eq (Discrete.mk _ ⟶ Discrete.mk _) _ _
      apply Subsingleton.elim)

include q in
theorem primitiveEvaluation_isEquivalence_of_baseTerm :
    (familyEvaluation a A hΓ (.fiber hx) c).IsEquivalence := by
  haveI : (familyEvaluation a A hΓ (.fiber hx) c ⋙
      (primitiveRecoveryEquivalence a A hΓ hx c q).functor).IsEquivalence :=
    Functor.isEquivalence_of_iso (primitiveEvaluationRecovery a A hΓ hx c q).symm
  exact Functor.isEquivalence_of_comp_right (familyEvaluation a A hΓ (.fiber hx) c)
    (primitiveRecoveryEquivalence a A hΓ hx c q).functor

end SquareKit.SmoothQuotientCechLocal
