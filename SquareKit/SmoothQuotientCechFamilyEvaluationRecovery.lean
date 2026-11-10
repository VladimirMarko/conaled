import SquareKit.Internal.PathTransport.ComparisonLocalRecovery
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

def localFamilyMap :
    (show (show Grpd.{1,1} from γ (model a A)) ⥤ Grpd.{1,1} from b (model a A)) ⟶
      localMap a A hΓ ⋙ (show (show Grpd.{1,1} from γ
        (SmoothQuotientSource.model a (SplitSheaf.Ext A))) ⥤ Grpd.{1,1} from
          b (SmoothQuotientSource.model a (SplitSheaf.Ext A))) :=
  generatedFamilyMap (signature a A) hΓ hB

theorem localMap_extend :
    localMap a A (.ext hΓ hB) = totalMap (localMap a A hΓ)
      (localFamilyMap a A hΓ hB) :=
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

theorem localMap_extend_fiber
    (c : (show Grpd.{1,1} from γ (model a A))) (x : (b (model a A)).obj c) :
    HEq (((localMap a A (.ext hΓ hB)).obj ⟨c,x⟩).fiber)
      (((localFamilyMap a A hΓ hB).app c).obj x) :=
  totalMap_obj_fiber_heq (localMap a A hΓ) (localFamilyMap a A hΓ hB)
    (localMap a A (.ext hΓ hB)) (localMap_extend a A hΓ hB) ⟨c,x⟩

theorem localMatching_fiber
    (c : (show Grpd.{1,1} from γ (model a A))) (x : (b (model a A)).obj c) :
    HEq (((fiberTotalEvaluation a A hΓ hB c).obj x).localObject.fiber)
      (((localMap a A (.ext hΓ hB)).obj ⟨c,x⟩).fiber) :=
  HEq.rfl

theorem familyEvaluation_localComponent
    (c : (show Grpd.{1,1} from γ (model a A))) (x : (b (model a A)).obj c) :
    HEq ((familyEvaluation a A hΓ hB c).obj x).localFiber
      (((localFamilyMap a A hΓ hB).app c).obj x) :=
  (familyEvaluation_localFiber a A hΓ hB c x).trans
    ((localMatching_fiber a A hΓ hB c x).trans (localMap_extend_fiber a A hΓ hB c x))

end SquareKit.SmoothQuotientCechLocal
