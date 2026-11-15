import SquareKit.Internal.PathTransport.TwoFamilyModelRootComponent
import SquareKit.Internal.PathTransport.TwoFamilyRootedComponentFormula
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ)
 (x : ULift.{u+1} (TwoFamily.Section A.data))
theorem rootContraction_component :
 RootedComponentFormula A.data x.down (rootContraction C D A x).val.homotopy := by
 have hH := congrArg₂ StrictPseudofunctor.comp (rootContraction_retraction C D A x) (rootSub_down_eq C D A x)
 have h := RootedComponentFormula.congr A.data x.down hH rfl
  (rootContraction C D A x).val.homotopy (rootedContraction A.data x.down)
  (rootContraction_homotopy C D A x) (rootedContraction_component A.data x.down)
 exact h
theorem rootContraction_base :
 RootedBaseFormula A.data x.down (rootContraction C D A x).val.homotopy := by
 have hH := congrArg₂ StrictPseudofunctor.comp (rootContraction_retraction C D A x) (rootSub_down_eq C D A x)
 have h := RootedBaseFormula.congr A.data x.down hH rfl
  (rootContraction C D A x).val.homotopy (rootedContraction A.data x.down)
  (rootContraction_homotopy C D A x) (rootedContraction_base A.data x.down)
 exact h
end SquareKit.Internal.PathTransport.HigherInterpretation
