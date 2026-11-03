import SquareKit.Internal.SheafSliceUniversal
import SquareKit.Internal.PartitionSequents
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! Classification of the finite complementary-predicate theory by the slice
at `u ⨿ 1`. The categorical model category retains chosen subterminal carriers
and their predicate-preserving morphisms. PartitionSequents proves that its
partition data express precisely coverage, exclusion and the parameter bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [HasBinaryProducts F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [HasBinaryCoproducts B]
variable (h : GeometricMorphism F B) {U : B} (u : U ⟶ ⊤_ B) [Mono u]

/-- Inverse image of the parameter, including the canonical terminal comparison. -/
def parameterPullback : h.inverseImage.obj U ⟶ ⊤_ F :=
  h.inverseImage.map u ≫ (PreservesTerminal.iso h.inverseImage).hom

instance : Mono (parameterPullback h u) := by
  dsimp [parameterPullback]
  infer_instance

/-- The canonical coproduct and terminal comparisons, with their directions fixed. -/
def classifierObjectComparison :
    h.inverseImage.obj (U ⨿ ⊤_ B) ≅ h.inverseImage.obj U ⨿ ⊤_ F :=
  (PreservesColimitPair.iso h.inverseImage U (⊤_ B)).symm ≪≫
    coprod.mapIso (Iso.refl _) (PreservesTerminal.iso h.inverseImage)

/-- Normalization of sections preserves the actual summand comparison maps. -/
def classifierSectionEquiv :
    (⊤_ F ⟶ h.inverseImage.obj (U ⨿ ⊤_ B)) ≃ (⊤_ F ⟶ h.inverseImage.obj U ⨿ ⊤_ F) where
  toFun s := s ≫ (classifierObjectComparison h (U := U)).hom
  invFun s := s ≫ (classifierObjectComparison h (U := U)).inv
  left_inv s := by simp
  right_inv s := by simp

local instance finiteClassifierLocal1 : CartesianMonoidalCategory (Over (h.inverseImage.obj (U ⨿ ⊤_ B))) :=
  Over.cartesianMonoidalCategory _
variable [Closed (U ⨿ ⊤_ B)] [MonoidalClosed (Over (h.inverseImage.obj (U ⨿ ⊤_ B)))]

/-- Full arbitrary-source classification under the stated categorical structure.
Sheaf sources discharge the source-slice closure hypothesis in the specialization below. -/
def finiteClassifier : Lift h (slice (U ⨿ ⊤_ B)) ≌
    PartitionSection.Model (parameterPullback h u) :=
  (sectionEquivalence h (U ⨿ ⊤_ B)).trans
    ((Discrete.equivalence (classifierSectionEquiv h (U := U))).trans
      (PartitionSection.sectionEquivalence (parameterPullback h u)).symm)
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [HasBinaryProducts F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [HasBinaryCoproducts B]
variable (h : GeometricMorphism F B) (U : B)

@[reassoc (attr := simp)] theorem classifierObjectComparison_inl :
    h.inverseImage.map (coprod.inl : U ⟶ U ⨿ ⊤_ B) ≫
      (classifierObjectComparison h (U := U)).hom = coprod.inl := by
  have hi : coprod.inl ≫ (PreservesColimitPair.iso h.inverseImage U (⊤_ B)).hom =
      h.inverseImage.map coprod.inl := by simp
  change h.inverseImage.map coprod.inl ≫
    (PreservesColimitPair.iso h.inverseImage U (⊤_ B)).inv ≫
      coprod.map (𝟙 _) (PreservesTerminal.iso h.inverseImage).hom = _
  rw [← hi, Category.assoc, Iso.hom_inv_id_assoc, coprod.inl_map, Category.id_comp]

@[reassoc (attr := simp)] theorem classifierObjectComparison_inr :
    h.inverseImage.map (coprod.inr : ⊤_ B ⟶ U ⨿ ⊤_ B) ≫
      (classifierObjectComparison h (U := U)).hom =
        (PreservesTerminal.iso h.inverseImage).hom ≫ coprod.inr := by
  have hi : coprod.inr ≫ (PreservesColimitPair.iso h.inverseImage U (⊤_ B)).hom =
      h.inverseImage.map coprod.inr := by simp
  change h.inverseImage.map coprod.inr ≫
    (PreservesColimitPair.iso h.inverseImage U (⊤_ B)).inv ≫
      coprod.map (𝟙 _) (PreservesTerminal.iso h.inverseImage).hom = _
  rw [← hi, Category.assoc, Iso.hom_inv_id_assoc, coprod.inr_map]
end SquareKit.Internal.GeometricMorphism
