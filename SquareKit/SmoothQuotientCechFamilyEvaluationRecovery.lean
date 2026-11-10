import SquareKit.SmoothQuotientCechGeneratedFamilyEvaluation
import SquareKit.Internal.PathTransport.GeneratedComparisonLaws

/-! Local recovery formulas for actual generated dependent matching evaluation. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)

theorem localMap_extend :
    localMap a A (.ext hΓ hB) = totalMap (localMap a A hΓ)
      (generatedFamilyMap (signature a A) hΓ hB) :=
  generatedContextMap_extend (signature a A) hΓ hB

/-- The extracted local fiber is precisely the one in total local evaluation. -/
theorem familyEvaluation_localFiber
    (c : (show Grpd.{1,1} from γ (model a A))) (x : (b (model a A)).obj c) :
    HEq ((familyEvaluation a A hΓ hB c).obj x).localFiber
      ((fiberTotalEvaluation a A hΓ hB c).obj x).localObject.fiber :=
  CechMatching.Comprehension.fixedBaseObject_localFiber _ _
    (fiberTotalEvaluation a A hΓ hB c) _
    (fiberTotalEvaluation_projection a A hΓ hB c) x

theorem totalMatchingEvaluation_local
    (z : Extend (b (model a A))) :
    ((totalMatchingEvaluation a A hΓ hB).obj z).localObject =
      (localMap a A (.ext hΓ hB)).obj z := rfl

end SquareKit.SmoothQuotientCechLocal
