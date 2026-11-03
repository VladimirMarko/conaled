import SquareKit.Internal.PartitionMixedChange

/-! Coherence diagrams for the mixed parameter and inverse-image comparisons.
Thinness is proved from complementary predicates before it is used here. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits
open SquareKit.Internal.PartitionSection
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [HasBinaryProducts F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable (f : GeometricMorphism F B) {U V W : B}
variable (u : U ⟶ ⊤_ B) (v : V ⟶ ⊤_ B) (w : W ⟶ ⊤_ B)
variable [Mono u] [Mono v] [Mono w]

/-- The mixed square for an identity parameter map agrees with the identity comparisons. -/
theorem parameterPullback_identity (M : Model u) :
    (parameterPullbackIso f u u (𝟙 U)).hom.app M =
      (pullModelFunctor f).map ((parameterIdentityIso u).hom.app M) ≫
        (parameterIdentityIso (parameterPullback f u)).inv.app (pullModel f M) ≫
          eqToHom (congrArg (fun t => (mapParameter (parameterPullback f u) (parameterPullback f u) t).obj
            (pullModel f M)) (f.inverseImage.map_id U).symm) :=
  Subsingleton.elim _ _

/-- The mixed square for a composite parameter map is the pasted pair of mixed squares. -/
theorem parameterPullback_composition (s : U ⟶ V) (t : V ⟶ W) (M : Model u) :
    (parameterPullbackIso f u w (s ≫ t)).hom.app M =
      (pullModelFunctor f).map ((parameterCompIso u v w s t).inv.app M) ≫
        (parameterPullbackIso f v w t).hom.app ((mapParameter u v s).obj M) ≫
          (mapParameter (parameterPullback f v) (parameterPullback f w) (f.inverseImage.map t)).map
            ((parameterPullbackIso f u v s).hom.app M) ≫
              (parameterCompIso (parameterPullback f u) (parameterPullback f v) (parameterPullback f w)
                (f.inverseImage.map s) (f.inverseImage.map t)).hom.app (pullModel f M) ≫
                  eqToHom (congrArg (fun r => (mapParameter (parameterPullback f u) (parameterPullback f w) r).obj
                    (pullModel f M)) (f.inverseImage.map_comp s t).symm) :=
  Subsingleton.elim _ _
end SquareKit.Internal.GeometricMorphism
