import SquareKit.Internal.PathTransport.ComparisonComposition

/-! Local fiber recovery through a presented comprehension comparison. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Grpd.{u,u}} {A : C ⥤ Grpd.{u,u}} {B : D ⥤ Grpd.{u,u}}

theorem totalMap_obj_fiber_heq (R : C ⥤ D) (α : A ⟶ R ⋙ B)
    (E : Extend A ⥤ Extend B) (hE : E = totalMap R α) (z : Extend A) :
    HEq (E.obj z).fiber ((α.app z.base).obj z.fiber) := by
  cases hE
  rfl

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
