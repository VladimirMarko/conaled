import SquareKit.Internal.PartitionCoherence

/-! Identity and vertical-composition diagrams for source transformations.
All displayed arrows use actual components on the two predicate carriers. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open SquareKit.Internal.PartitionSection
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [HasBinaryProducts F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable {f g h : GeometricMorphism F B} {U : B} (u : U ⟶ ⊤_ B) [Mono u]

/-- Identity source transformation agrees with the identity parameter comparison. -/
theorem pullModelTransformation_identity :
    pullModelTransformation u (𝟙 f) =
      (isoWhiskerLeft (pullModelFunctor f) (parameterIdentityIso (parameterPullback f u))).hom ≫
        (Functor.rightUnitor (pullModelFunctor f)).hom := by
  apply NatTrans.ext
  funext M
  apply Subsingleton.elim

/-- Vertical composition agrees with parameter composition and the two actual carrier transformations. -/
theorem pullModelTransformation_composition (α : f ⟶ g) (β : g ⟶ h) :
    pullModelTransformation u (α ≫ β) =
      (isoWhiskerLeft (pullModelFunctor f)
        (parameterCompIso (parameterPullback f u) (parameterPullback g u) (parameterPullback h u)
          (α.app U) (β.app U))).inv ≫
        (Functor.associator (pullModelFunctor f)
          (mapParameter (parameterPullback f u) (parameterPullback g u) (α.app U))
          (mapParameter (parameterPullback g u) (parameterPullback h u) (β.app U))).inv ≫
          whiskerRight (pullModelTransformation u α)
            (mapParameter (parameterPullback g u) (parameterPullback h u) (β.app U)) ≫
              pullModelTransformation u β := by
  apply NatTrans.ext
  funext M
  apply Subsingleton.elim
end SquareKit.Internal.GeometricMorphism
