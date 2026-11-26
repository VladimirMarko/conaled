import SquareKit.SmoothQuotientCechPrimitiveEvaluation
import SquareKit.SmoothQuotientCechBaseTermSquare

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
    (fiber_cast_eq_of_val_heq a A q _ x.as (familyEvaluation_fiber_matching_value a A hΓ hx c x))))
    (by
      intro x y f
      change @Eq (Discrete.mk _ ⟶ Discrete.mk _) _ _
      apply Subsingleton.elim)

include q in
theorem familyEvaluation_fiber_isEquivalence_of_base_term_eq :
    (familyEvaluation a A hΓ (.fiber hx) c).IsEquivalence := by
  have : (familyEvaluation a A hΓ (.fiber hx) c ⋙
      (primitiveRecoveryEquivalence a A hΓ hx c q).functor).IsEquivalence :=
    Functor.isEquivalence_of_iso (primitiveEvaluationRecovery a A hΓ hx c q).symm
  exact Functor.isEquivalence_of_comp_right (familyEvaluation a A hΓ (.fiber hx) c)
    (primitiveRecoveryEquivalence a A hΓ hx c q).functor

/-- Primitive matching is effective for every generated base term. -/
theorem familyEvaluation_fiber_isEquivalence :
    (familyEvaluation a A hΓ (.fiber hx) c).IsEquivalence :=
  familyEvaluation_fiber_isEquivalence_of_base_term_eq a A hΓ hx c
    (Functor.congr_obj (evaluatedBaseTerm_eq_source a A hΓ hx) c)

end SquareKit.SmoothQuotientCechLocal
