import SquareKit.Internal.PartitionTransform

/-! The mixed parameter/inverse-image square and its transformation compatibility. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [HasBinaryProducts F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable (f : GeometricMorphism F B) {U V : B}
variable (u : U ⟶ ⊤_ B) (v : V ⟶ ⊤_ B) [Mono u] [Mono v] (t : U ⟶ V)

/-- Parameter substitution and geometric inverse image commute on both predicate carriers. -/
def parameterPullbackIso : PartitionSection.mapParameter u v t ⋙ pullModelFunctor f ≅
    pullModelFunctor f ⋙ PartitionSection.mapParameter
      (parameterPullback f u) (parameterPullback f v) (f.inverseImage.map t) :=
  NatIso.ofComponents (fun M => {
    hom := ⟨𝟙 _, 𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    inv := ⟨𝟙 _, 𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)

/-- The mixed comparison preserves the specific left predicate element, via identity on its carrier. -/
theorem parameterPullbackIso_left (M : PartitionSection.Model u) :
    ((parameterPullbackIso f u v t).hom.app M).left = 𝟙 (f.inverseImage.obj M.P) := rfl

/-- The right predicate is preserved independently, not identified with the left predicate. -/
theorem parameterPullbackIso_right (M : PartitionSection.Model u) :
    ((parameterPullbackIso f u v t).hom.app M).right = 𝟙 (f.inverseImage.obj M.Q) := rfl
end SquareKit.Internal.GeometricMorphism
