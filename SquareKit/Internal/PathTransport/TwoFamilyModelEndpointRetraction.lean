import SquareKit.Internal.PathTransport.TwoFamilyModelEndpointObjects
import SquareKit.Internal.PathTransport.TwoFamilyModelRootComponent
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ)
variable (x y : ULift.{u+1} (TwoFamily.Section A.data))
variable (p : ULift.{u+1} (TwoFamily.Section (TwoFamily.closedId A.data x.down y.down)))
local notation "M" => structuralModel C D
set_option maxHeartbeats 1000000 in
theorem endpointSub_retraction :
 ((M).endpointSub A x y p).down.comp (rootContraction C D A x).val.retraction = StrictPseudofunctor.id Γ := by
 have h := congrArg (fun f => f.comp (TwoFamily.projectionHigher A.data)) (endpointSub_projection C D A x y p)
 have k := h.trans y.down.over
 have e := rootContraction_retraction C D A x
 rw [e]
 exact (strictFunctor_comp_assoc _ _ _).symm.trans k
end SquareKit.Internal.PathTransport.HigherInterpretation
