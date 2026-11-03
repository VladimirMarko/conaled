import SquareKit.Internal.PartitionPullback

/-! Coherence of the actual coproduct and terminal comparison maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [HasBinaryProducts F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable {h k : GeometricMorphism F B} (α : h ⟶ k) (U : B)

/-- The comparison is natural even for noninvertible inverse-image transformations. -/
theorem classifierObjectComparison_natural :
    α.app (U ⨿ ⊤_ B) ≫ (classifierObjectComparison k (U := U)).hom =
      (classifierObjectComparison h (U := U)).hom ≫ coprod.map (α.app U) (𝟙 (⊤_ F)) := by
  apply (cancel_epi (PreservesColimitPair.iso h.inverseImage U (⊤_ B)).hom).1
  apply coprod.hom_ext
  · simp only [← Category.assoc, PreservesColimitPair.iso_hom, inl_coprodComparison]
    rw [α.naturality, classifierObjectComparison_inl]
    simp only [Category.assoc, classifierObjectComparison_inl, coprod.inl_map]
  · simp only [← Category.assoc, PreservesColimitPair.iso_hom, inr_coprodComparison]
    rw [α.naturality, classifierObjectComparison_inr]
    simp only [Category.assoc, classifierObjectComparison_inr, coprod.inr_map, Category.id_comp]
    rw [← Category.assoc]
    congr 1
    exact terminal.hom_ext _ _
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {F : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} C]
variable [HasTerminal F] [HasBinaryProducts F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable [CartesianMonoidalCategory C] [HasPullbacks C] [FinitaryExtensive C]

/-- Composition preserves the specified coproduct and terminal comparisons. -/
theorem classifierObjectComparison_comp (f : GeometricMorphism F B) (g : GeometricMorphism B C)
    (U : C) :
    (classifierObjectComparison (f.comp g) (U := U)).hom =
      f.inverseImage.map (classifierObjectComparison g (U := U)).hom ≫
        (classifierObjectComparison f (U := g.inverseImage.obj U)).hom := by
  apply (cancel_epi (PreservesColimitPair.iso (f.comp g).inverseImage U (⊤_ C)).hom).1
  apply coprod.hom_ext
  · simp only [← Category.assoc, PreservesColimitPair.iso_hom, inl_coprodComparison]
    rw [classifierObjectComparison_inl]
    change _ = (f.inverseImage.map (g.inverseImage.map coprod.inl) ≫
      f.inverseImage.map (classifierObjectComparison g).hom) ≫ _
    rw [← f.inverseImage.map_comp, classifierObjectComparison_inl, classifierObjectComparison_inl]
    rfl
  · simp only [← Category.assoc, PreservesColimitPair.iso_hom, inr_coprodComparison]
    rw [classifierObjectComparison_inr]
    change _ = (f.inverseImage.map (g.inverseImage.map coprod.inr) ≫
      f.inverseImage.map (classifierObjectComparison g).hom) ≫ _
    rw [← f.inverseImage.map_comp, classifierObjectComparison_inr, f.inverseImage.map_comp,
      Category.assoc, classifierObjectComparison_inr, ← Category.assoc]
    congr 1
    exact terminal.hom_ext _ _
end SquareKit.Internal.GeometricMorphism
