import Examples.FrozenMemoClient
import SquareKit.Internal.Cubical.ContextualSums
import Examples.FrozenMemoPair

/-! The unchanged frozen signature and both source substitutions in the
constructed cubical model. Its selected certificates use cubical finite-tail J.
Concrete higher assignments and their observer are separate obligations. -/
noncomputable section
namespace Examples.CubicalFrozenMemo
open SquareKit.Cubical.Presheaf SquareKit.Cubical.Contextual
open SquareKit.Internal.DependentJudgments
open Examples.GuardedGroupoidMemo
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "CM" => model Base Fiber

def environment := FrozenMemoSignature.environment CM Base Fiber

def client : FrozenMemoRealization.Client CM (environment Base Fiber) signature :=
  FrozenMemoRealization.Client.ofTyping CM (environment Base Fiber)
    (FrozenMemoSignature.inputs CM Base Fiber) signature

noncomputable def selectedPair :=
  (client Base Fiber).input.selectedPair (sumCapability Base Fiber)

end Examples.CubicalFrozenMemo
