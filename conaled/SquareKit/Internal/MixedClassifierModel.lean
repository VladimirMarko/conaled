import SquareKit.Internal.GeometricMixedChange
import SquareKit.Internal.PartitionTransform
import SquareKit.SliceExtensive

/-! Context substitution and ambient inverse image compare on the actual
predicate models, using the geometric mixed square's carrier maps. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasPullbacks F] [HasPullbacks B] [FinitaryExtensive F] [FinitaryExtensive B]
variable (h : GeometricMorphism F B) {X Y : B} (σ : X ⟶ Y)
local instance mixedModelBaseCartesian : CartesianMonoidalCategory (Over Y) := Over.cartesianMonoidalCategory Y
local instance mixedModelSourceCartesian : CartesianMonoidalCategory (Over (h.inverseImage.obj Y)) :=
  Over.cartesianMonoidalCategory _
variable [Closed (Over.mk σ)] [Closed (Over.mk (h.inverseImage.map σ))]
variable {U : Over Y} (u : U ⟶ ⊤_ (Over Y)) [Mono u]

/-- The mixed context/base square compares model functors, with the actual pullback comparison at each carrier. -/
def mixedClassifierModelIso :
    pullModelFunctor ((h.onSlices X).comp (along σ)) ⋙
      PartitionSection.changeParameter
        (parameterPullback ((h.onSlices X).comp (along σ)) u)
        (parameterPullback ((along (h.inverseImage.map σ)).comp (h.onSlices Y)) u)
        ((pullbackPost h σ).app U) ≅
      pullModelFunctor ((along (h.inverseImage.map σ)).comp (h.onSlices Y)) :=
  pullModelNatIso (f := (h.onSlices X).comp (along σ))
    (g := (along (h.inverseImage.map σ)).comp (h.onSlices Y)) u (pullbackPost h σ)
end SquareKit.Internal.GeometricMorphism
