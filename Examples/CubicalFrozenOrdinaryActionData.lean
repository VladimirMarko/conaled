import Examples.CubicalFrozenActionTransport
import Examples.CubicalFrozenActionHomotopy
import SquareKit.Internal.Cubical.CocycleOrdinaryAction
import SquareKit.Internal.Cubical.CocycleActionBridgeValues

/-! The interpreted ordinary J-action on the retained frozen h has the required beta coherence. -/
noncomputable section
namespace Examples.CubicalFrozenOrdinaryAction
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf SquareKit.Cubical.Contextual
open SquareKit.Cubical.CategoryCocycles
open Examples.CubicalCocycleAssignment Examples.CubicalFrozenActionInputs

def sourceHigherAction := cocycleOrdinaryAction cocycleBase cocycleRootedFamily
  assignedType.filling assignedType.lawful assignedTransport selectedNormalizedHomotopy

def selectedActionBridge := cocycleOrdinaryBridge cocycleBase cocycleRootedFamily
  assignedType.filling assignedType.lawful assignedTransport selectedNormalizedHomotopy

end Examples.CubicalFrozenOrdinaryAction
