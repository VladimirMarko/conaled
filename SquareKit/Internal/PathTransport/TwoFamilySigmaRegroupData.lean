import SquareKit.Internal.PathTransport.TwoFamilySigmaUngroupCells
import SquareKit.Internal.PathTransport.TwoFamilySigmaRegroupFaithful
import SquareKit.Internal.PathTransport.TwoFunctorDataCancellation
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))
def sigmaRegroupData : PrelaxFunctorStruct (Total (sigmaFamily F B)) (Total B) where
  obj := sigmaRegroupObj F B
  map := sigmaRegroupMap F B
  map₂ := sigmaRegroupCell F B

def sigmaUngroupData : PrelaxFunctorStruct (Total B) (Total (sigmaFamily F B)) where
  obj := sigmaUngroupObj F B
  map := sigmaUngroupMap F B
  map₂ := sigmaUngroupCell F B

theorem sigmaUngroupData_regroup : (sigmaUngroupData F B).comp (sigmaRegroupData F B) =
    PrelaxFunctorStruct.id (Total B) := by
  apply prelaxData_ext
  · intro x; exact sigmaRegroupObj_ungroup F B x
  · intro x y p; exact heq_of_eq (sigmaRegroupMap_ungroup F B p)
  · intro x y p q α; exact sigmaRegroupCell_ungroup_heq F B α

theorem sigmaRegroupData_ungroup : (sigmaRegroupData F B).comp (sigmaUngroupData F B) =
    PrelaxFunctorStruct.id (Total (sigmaFamily F B)) := by
  refine raw_left_inverse_of_right (sigmaRegroupData F B) (sigmaUngroupData F B) ?_ ?_ ?_
    (sigmaUngroupData_regroup F B)
  · exact (sigmaRegroupObjectEquiv F B).injective
  · intro x y; exact (sigmaRegroupArrowEquiv F B x y).injective
  · intro x y p q; exact sigmaRegroupCell_injective F B

theorem sigmaUngroupCell_regroup_heq {x y : Total (sigmaFamily F B)}
    {p q : x ⟶ y} (α : p ⟶ q) :
    HEq (sigmaUngroupCell F B (sigmaRegroupCell F B α)) α :=
  congr_arg_heq (fun D => D.map₂ α) (sigmaRegroupData_ungroup F B)
end SquareKit.Internal.PathTransport.TwoFamily
