import SquareKit.Internal.GenericModelPullback
import SquareKit.Internal.SliceRebase

/-! The classifier respects the specified comparison when the base inverse
image is replaced by an isomorphic one. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [HasBinaryProducts F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable {h h' : GeometricMorphism F B} {U : B} (u : U ⟶ ⊤_ B) [Mono u]
variable [Closed (U ⨿ ⊤_ B)] (e : h.inverseImage ≅ h'.inverseImage)

/-- Rebase normalization commutes with the actual classifier section. -/
theorem classifierRebase_section (k : Lift h (slice (U ⨿ ⊤_ B))) :
    ((PartitionSection.changeParameter (parameterPullback h u) (parameterPullback h' u) (e.app U)).obj
      (k.model u)).toSection = ((k.rebase e).model u).toSection := by
  rw [PartitionSection.changeParameter_section, Lift.model_section, Lift.model_section, Lift.rebase_section]
  simp only [Category.assoc]
  exact congrArg (fun t => k.section ≫ t)
    (classifierObjectComparison_natural (h := h) (k := h') e.hom U).symm

/-- The comparison acts on model morphisms as well as objects. -/
def classifierRebaseIso :
    modelFunctor (h := h) u ⋙ PartitionSection.changeParameter (parameterPullback h u)
      (parameterPullback h' u) (e.app U) ≅ Lift.rebaseFunctor e ⋙ modelFunctor (h := h') u :=
  NatIso.ofComponents (fun k => {
    hom := PartitionSection.Model.homOfSection (classifierRebase_section u e k)
    inv := PartitionSection.Model.homOfSection (classifierRebase_section u e k).symm
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)
end SquareKit.Internal.GeometricMorphism
