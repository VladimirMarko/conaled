import SquareKit.Internal.PathTransport.TwoFamilyModelSquareLift
import Examples.TwoFamilyStructuralModel
namespace Examples.TwoFamilyModelComparisons
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport HigherInterpretation
open Examples.TwoFamilyModelData Examples.TwoFamilyStructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
example (σ : StrictPseudofunctor integerContext integerContext) :
    (model.lift integers ⟨σ⟩).down = TwoFamily.reindexHigher integers.data σ :=
  lift_eq_reindexHigher integerContext integerContext integers σ
example (F F' K L : model.Substitution integerContext integerContext)
    (h : model.compSub K F' = model.compSub F L) :
    (model.squareLift F F' K L h integers).down =
      TwoFamily.contractionBranchSubstitution F.down F'.down K.down L.down
        (congrArg ULift.down h) integers.data :=
  squareLift_down_eq integerContext integerContext F F' K L h integers
end Examples.TwoFamilyModelComparisons
