import SquareKit.Internal.PathTransport.TwoFamilyModelRootSub
import Examples.TwoFamilyStructuralModel
namespace Examples.TwoFamilyModelRooted
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport HigherInterpretation
open Examples.TwoFamilyModelData Examples.TwoFamilyStructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
example : HEq (model.rootSub display chosen).down
    (TwoFamily.rootedReflexivity display.data chosen.down) :=
  heq_of_eq (rootSub_down_eq integerContext integerContext display chosen)
end Examples.TwoFamilyModelRooted
