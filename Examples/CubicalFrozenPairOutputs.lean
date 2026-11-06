import Examples.CubicalFrozenMemo
import Examples.FrozenMemoPairReindex

/-! The selected pair's original source substitutions, for arbitrary cubical primitive families. -/
noncomputable section
namespace Examples.CubicalFrozenMemo
open SquareKit.Cubical.Presheaf SquareKit.Cubical.Contextual
open Examples.FrozenMemoRealization Examples.GuardedGroupoidMemo
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))

set_option linter.defProp false in
def pair_twice := FrozenSignature.pair_twice (model Base Fiber)
  (sumCapability Base Fiber) (environment Base Fiber)
  (Examples.FrozenMemoSignature.inputs (model Base Fiber) Base Fiber)
  signature (client Base Fiber).input

set_option linter.defProp false in
def pair_reindex {Δ : (model Base Fiber).Context}
    (σ : (model Base Fiber).Substitution Δ (client Base Fiber).input.context) :=
  (client Base Fiber).input.selectedPair_reindex (stableSums Base Fiber) σ

end Examples.CubicalFrozenMemo
