import Examples.CubicalFrozenConjugation
import Examples.CubicalFrozenPairOutputs

/-! Selected memo outputs and both original frozen substitutions in the same higher model. -/
noncomputable section
namespace Examples.CubicalFrozenOutputs
open SquareKit.Cubical.Presheaf SquareKit.Cubical.Contextual
open SquareKit.Cubical.CategoryCocycles
open Examples.CubicalCocycleAssignment Examples.FrozenMemoRealization
open Examples.GuardedGroupoidMemo

/-- This package retains the exact selected certificate and apd equations under both source maps. -/
def retainedOutputs := frozenClient

set_option linter.defProp false in
def selectedPair_twice := Examples.CubicalFrozenMemo.pair_twice cocycleBase cocycleRootedFamily

end Examples.CubicalFrozenOutputs
