import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupRight
import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupData
import SquareKit.Internal.PathTransport.TwoFunctorInverseData
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ uB vB wB
variable {Γ : Type uΓ} [ib : Bicategory.{wΓ,vΓ} Γ] [isb : Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward false in
set_option maxHeartbeats 200000 in
/-- Flatten nested dependent pairs, preserving both levels of genuine cells. -/
def sigmaRegroup : StrictPseudofunctor (Total (sigmaFamily F B)) (Total B) :=
  StrictPseudofunctor.mk'' (by
    refine { obj := sigmaRegroupObj F B
             map := fun {x y} p => sigmaRegroupMap F B p
             map₂ := fun {x y p q} α => sigmaRegroupCell F B α
             map_id := sigmaRegroupMap_id F B
             map_comp := sigmaRegroupMap_comp F B
             map₂_id := sigmaRegroupCell_id F B
             map₂_comp := sigmaRegroupCell_comp F B
             map₂_whisker_left := ?_
             map₂_whisker_right := ?_ }
    · intro x y z p q r α
      with_reducible exact @sigmaRegroupCell_whiskerLeft.{u,v,w,uΓ,vΓ,wΓ,uB,vB,wB} Γ ib isb F B x y z p q r α
    · intro x y z p q α r
      with_reducible exact @sigmaRegroupCell_whiskerRight.{u,v,w,uΓ,vΓ,wΓ,uB,vB,wB} Γ ib isb F B x y z p q α r)
/-- Restore the nested grouping using its actual inverse data. -/
def sigmaUngroup : StrictPseudofunctor (Total B) (Total (sigmaFamily F B)) :=
  strictFunctorOfInverseData (sigmaRegroup F B) (sigmaUngroupData F B)
    (sigmaRegroupData_ungroup F B) (sigmaUngroupData_regroup F B)

theorem sigmaRegroup_ungroup : (sigmaRegroup F B).comp (sigmaUngroup F B) =
    StrictPseudofunctor.id (Total (sigmaFamily F B)) :=
  strictFunctorData_ext (sigmaRegroupData_ungroup F B)

theorem sigmaUngroup_regroup : (sigmaUngroup F B).comp (sigmaRegroup F B) =
    StrictPseudofunctor.id (Total B) :=
  strictFunctorData_ext (sigmaUngroupData_regroup F B)

theorem sigmaRegroup_projection : (sigmaRegroup F B).comp (projectionHigher B) =
    sigmaFirst F B := strictFunctorData_ext rfl

theorem sigmaUngroup_first : (sigmaUngroup F B).comp (sigmaFirst F B) =
    projectionHigher B := strictFunctorData_ext rfl

theorem sigmaUngroup_projection :
    (sigmaUngroup F B).comp (projectionHigher (sigmaFamily F B)) =
      (projectionHigher B).comp (projectionHigher F) := strictFunctorData_ext rfl
end SquareKit.Internal.PathTransport.TwoFamily
