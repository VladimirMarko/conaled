import SquareKit.Internal.GenericModelPullback
import SquareKit.Internal.SliceSourceChange

/-! Source substitution compares the classifier with actual inverse image of
both predicates. Parameter normalization is explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {F : Type u₁} {B : Type u₂} {G : Type u₃}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} G]
variable [CartesianMonoidalCategory F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable [HasTerminal G] [HasBinaryProducts G] [HasPullbacks G] [FinitaryExtensive G]
variable (f : GeometricMorphism G F) (h : GeometricMorphism F B)
variable {U : B} (u : U ⟶ ⊤_ B) [Mono u]

/-- Pull back actual predicates and normalize the parameter to the composite geometric morphism. -/
def sourceModelFunctor : PartitionSection.Model (parameterPullback h u) ⥤
    PartitionSection.Model (parameterPullback (f.comp h) u) :=
  pullModelFunctor f ⋙ PartitionSection.changeParameter
    (parameterPullback f (parameterPullback h u)) (parameterPullback (f.comp h) u) (Iso.refl _)

/-- The source substitution functor retains inverse image of the actual section. -/
theorem sourceModelFunctor_section (M : PartitionSection.Model (parameterPullback h u)) :
    ((sourceModelFunctor f h u).obj M).toSection = f.pullSection M.toSection ≫
      (classifierObjectComparison f (U := h.inverseImage.obj U)).hom := by
  change ((PartitionSection.changeParameter _ _ (Iso.refl _)).obj (pullModel f M)).toSection = _
  rw [PartitionSection.changeParameter_section, pullModel_section]
  simp

variable [Closed (U ⨿ ⊤_ B)]

/-- Classification commutes with source substitution on the interpreted sections. -/
theorem sourceModel_classifier_section (k : Lift h (slice (U ⨿ ⊤_ B))) :
    ((sourceModelFunctor f h u).obj (k.model u)).toSection = ((k.precomp f).model u).toSection := by
  rw [sourceModelFunctor_section, Lift.model_section, Lift.model_section, Lift.precomp_section]
  dsimp only [pullSection]
  rw [f.inverseImage.map_comp]
  simp only [Category.assoc]
  rw [← classifierObjectComparison_comp]

/-- The source comparison is an isomorphism of model functors, including predicate maps. -/
def classifierSourceIso : modelFunctor (h := h) u ⋙ sourceModelFunctor f h u ≅
    Lift.precompFunctor f ⋙ modelFunctor (h := f.comp h) u :=
  NatIso.ofComponents (fun k => {
    hom := PartitionSection.Model.homOfSection (sourceModel_classifier_section f h u k)
    inv := PartitionSection.Model.homOfSection (sourceModel_classifier_section f h u k).symm
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)
end SquareKit.Internal.GeometricMorphism
