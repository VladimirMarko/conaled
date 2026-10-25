import SquareKit.Internal.PartitionPullback
import SquareKit.Internal.PartitionParameter

/-! Noninvertible inverse-image transformations act on the actual predicate
carriers. Identity and composition comparisons retain those carriers. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [HasBinaryProducts F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable {f g : GeometricMorphism F B} {U : B} (u : U ⟶ ⊤_ B) [Mono u]

/-- Each transformation acts at both predicate carriers, in the inverse-image direction. -/
def pullModelTransformation (α : f ⟶ g) :
    pullModelFunctor f ⋙ PartitionSection.mapParameter (parameterPullback f u)
      (parameterPullback g u) (α.app U) ⟶ pullModelFunctor g where
  app M := {
    left := α.app M.P
    right := α.app M.Q
    left_over := terminal.hom_ext _ _
    right_over := terminal.hom_ext _ _ }
  naturality _ _ _ := Subsingleton.elim _ _

/-- An isomorphism of inverse images compares actual model pullback with the same parameter isomorphism. -/
def pullModelNatIso (e : f.inverseImage ≅ g.inverseImage) :
    pullModelFunctor f ⋙ PartitionSection.changeParameter (parameterPullback f u)
      (parameterPullback g u) (e.app U) ≅ pullModelFunctor g :=
  NatIso.ofComponents (fun M => {
    hom := ⟨e.hom.app M.P, e.hom.app M.Q, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    inv := ⟨e.inv.app M.P, e.inv.app M.Q, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)

/-- Identity substitution retains each carrier and its maps. -/
def pullModelIdentityIso :
    pullModelFunctor (identity B) ⋙ PartitionSection.changeParameter
      (parameterPullback (identity B) u) u (Iso.refl _) ≅ 𝟭 (PartitionSection.Model u) :=
  NatIso.ofComponents (fun M => {
    hom := ⟨𝟙 M.P, 𝟙 M.Q, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    inv := ⟨𝟙 M.P, 𝟙 M.Q, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {F : Type u₁} {B : Type u₂} {G : Type u₃}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} G]
variable [CartesianMonoidalCategory F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable [HasTerminal G] [HasBinaryProducts G] [HasPullbacks G] [FinitaryExtensive G]
variable (f : GeometricMorphism G F) (g : GeometricMorphism F B)
variable {U : B} (u : U ⟶ ⊤_ B) [Mono u]

/-- Composite inverse image agrees with successive inverse images on actual predicate carriers. -/
def pullModelCompIso :
    pullModelFunctor g ⋙ pullModelFunctor f ⋙ PartitionSection.changeParameter
      (parameterPullback f (parameterPullback g u)) (parameterPullback (f.comp g) u) (Iso.refl _) ≅
        pullModelFunctor (f.comp g) :=
  NatIso.ofComponents (fun M => {
    hom := ⟨𝟙 _, 𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    inv := ⟨𝟙 _, 𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)
end SquareKit.Internal.GeometricMorphism
