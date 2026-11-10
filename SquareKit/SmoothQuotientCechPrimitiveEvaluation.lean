import SquareKit.SmoothQuotientCechFamilyEvaluationRecovery
import SquareKit.SmoothQuotientPrimitiveCoefficientValues

/-! Selected local-value recovery for actual primitive matching evaluation. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ t ξ} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hx : Typed.TmDeriv.{2} Γ γ .base (Typed.baseCode γ) t ξ)

theorem primitiveEvaluation_local
    (c : (show Grpd.{1,1} from γ (model a A)))
    (x : ((Typed.fiberCode ξ) (model a A)).obj c) :
    ((familyEvaluation a A hΓ (.fiber hx) c).obj x).localFiber =
      (((localFamilyMap a A hΓ (.fiber hx)).app c).obj x) :=
  eq_of_heq (familyEvaluation_localComponent a A hΓ (.fiber hx) c x)

theorem primitiveEvaluation_value
    (c : (show Grpd.{1,1} from γ (model a A)))
    (x : ((Typed.fiberCode ξ) (model a A)).obj c) :
    ((familyEvaluation a A hΓ (.fiber hx) c).obj x).localFiber.as =
      (generatedFiberSetMap (signature a A) hΓ hx).app c x.as := by
  rw [primitiveEvaluation_local]
  change (((generatedFamilyMap (signature a A) hΓ (.fiber hx)).app c).obj x).as = _
  rw [generatedFamilyMap_fiber_set]
  rfl

theorem primitiveEvaluation_value_heq
    (c : (show Grpd.{1,1} from γ (model a A)))
    (x : ((Typed.fiberCode ξ) (model a A)).obj c) :
    HEq ((familyEvaluation a A hΓ (.fiber hx) c).obj x).localFiber.as
      (ULift.up.{1} x.as.down.val) := by
  rw [primitiveEvaluation_value]
  exact type_comp_eqToHom_apply_heq
    (whiskerLeft (baseFunctor (ξ (model a A)).down) (signature a A).fiberMap)
    (congrArg (· ⋙ (signature a A).rightFiber)
      (generatedBaseTerm_commutes (signature a A) hΓ hx)) c x.as

theorem primitiveEvaluation_coefficient_value
    (c : (show Grpd.{1,1} from γ (model a A)))
    (x : ((Typed.fiberCode ξ) (model a A)).obj c) :
    HEq (((primitiveCoefficientMatchingEquivalence a hΓ hx A
      ((matchingEvaluation a A hΓ).obj c)).functor.obj
        ((familyEvaluation a A hΓ (.fiber hx) c).obj x)).as.val)
      (ULift.up.{1} x.as.down.val) :=
  (primitiveCoefficientMatchingEquivalence_value a hΓ hx A _ _).trans
    (primitiveEvaluation_value_heq a A hΓ hx c x)

theorem primitiveEvaluation_matching_value
    (c : (show Grpd.{1,1} from γ (model a A)))
    (x : ((Typed.fiberCode ξ) (model a A)).obj c) :
    HEq (ULift.up.{1} (((primitiveCechMatchingEquivalence a A hΓ hx
      ((matchingEvaluation a A hΓ).obj c)).functor.obj
        ((familyEvaluation a A hΓ (.fiber hx) c).obj x)).as.down.val))
      (ULift.up.{1} x.as.down.val) :=
  primitiveEvaluation_coefficient_value a A hΓ hx c x

theorem primitiveValue_cast_eq
    {d e : SheafActionQuotient.Cech.Datum (a := a) A} (q : d = e)
    (x : ULift.{1} (SmoothQuotientDeformations.Cech.Fiber d))
    (y : ULift.{1} (SmoothQuotientDeformations.Cech.Fiber e))
    (hv : HEq (ULift.up.{1} x.down.val) (ULift.up.{1} y.down.val)) :
    cast (congrArg (fun d => ULift.{1} (SmoothQuotientDeformations.Cech.Fiber d)) q) x = y := by
  subst e
  apply ULift.ext
  apply Subtype.ext
  exact congrArg ULift.down (eq_of_heq hv)

end SquareKit.SmoothQuotientCechLocal
