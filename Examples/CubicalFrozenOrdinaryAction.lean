import Examples.CubicalFrozenActionSource
import Examples.FrozenOrdinaryActionSubstitution
import SquareKit.Internal.Cubical.OrdinaryActionBridge
import SquareKit.Internal.Cubical.CocycleOrdinaryConjugation

/-! The interpreted ordinary J-action on the retained frozen h has the required beta coherence. -/
noncomputable section
namespace Examples.CubicalFrozenOrdinaryAction
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf SquareKit.Cubical.Contextual
open SquareKit.Cubical.CategoryCocycles
open Examples.CubicalCocycleAssignment Examples.CubicalFrozenActionInputs

def conjugationCube := ordinaryConjugationCube cocycleBase cocycleRootedFamily assignedType.filling assignedType.lawful assignedTransport assignedBeta selectedNormalizedHomotopy

theorem source_transport_face : conjugationCube.pullback (Over.map (face3 1 false)) =
    sourceActionSquare (t := assignedTransport) sourceHigherAction :=
  ordinaryConjugation_start cocycleBase cocycleRootedFamily assignedType.filling assignedType.lawful assignedTransport assignedBeta selectedNormalizedHomotopy

theorem witness_face : conjugationCube.pullback (Over.map (face3 1 true)) =
    secondSquare selectedNormalizedHomotopy :=
  ordinaryConjugation_finish cocycleBase cocycleRootedFamily assignedType.filling assignedType.lawful assignedTransport assignedBeta selectedNormalizedHomotopy

theorem endpoint_faces (e : Bool) : conjugationCube.pullback (Over.map (face3 0 e)) =
    comparisonRootSquare assignedBeta :=
  ordinaryConjugation_root cocycleBase cocycleRootedFamily assignedType.filling assignedType.lawful assignedTransport assignedBeta selectedNormalizedHomotopy e

theorem remaining_faces (e : Bool) : conjugationCube.pullback (Over.map (face3 2 e)) =
    zeroCocycle (Over (⟨2⟩ : Cube)) :=
  ordinaryConjugation_side cocycleBase cocycleRootedFamily assignedType.filling assignedType.lawful assignedTransport assignedBeta selectedNormalizedHomotopy e

theorem sourceHigherObservation : observeSquare (sourceActionSquare (t := assignedTransport) sourceHigherAction) = 1 :=
  (ordinaryConjugation_observation cocycleBase cocycleRootedFamily assignedType.filling assignedType.lawful assignedTransport assignedBeta selectedNormalizedHomotopy).trans
    frozenHigherObservation

theorem sourceHigher_no_erasure : sourceActionSquare (t := assignedTransport) sourceHigherAction ≠ zeroCocycle (Over (⟨2⟩ : Cube)) := by
  intro h
  exact Int.one_ne_zero (sourceHigherObservation.symm.trans ((congrArg observeSquare h).trans observeSquare_zero))

end Examples.CubicalFrozenOrdinaryAction
