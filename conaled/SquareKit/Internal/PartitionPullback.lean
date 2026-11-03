import SquareKit.Internal.FiniteClassifier
import SquareKit.Internal.GeometricSections

/-! Pullback of the actual two predicates along a geometric inverse image.
Colimit preservation and the terminal comparison transport the model laws. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [HasBinaryProducts F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable (h : GeometricMorphism F B) {U : B} {u : U ⟶ ⊤_ B} [Mono u]

/-- Inverse image of both predicate carriers and their bound; no reclassification is used. -/
def pullModel (M : PartitionSection.Model u) : PartitionSection.Model (parameterPullback h u) where
  P := h.inverseImage.obj M.P
  Q := h.inverseImage.obj M.Q
  p := h.inverseImage.map M.p ≫ (PreservesTerminal.iso h.inverseImage).hom
  q := h.inverseImage.map M.q ≫ (PreservesTerminal.iso h.inverseImage).hom
  bound := h.inverseImage.map M.bound
  bound_over := terminal.hom_ext _ _
  partition := IsColimit.ofIsoColimit
    (mapIsColimitOfPreservesOfIsColimit h.inverseImage _ _ M.partition)
    (BinaryCofan.ext (PreservesTerminal.iso h.inverseImage) ((terminalIsTerminal.isTerminalObj h.inverseImage).hom_ext _ _)
      ((terminalIsTerminal.isTerminalObj h.inverseImage).hom_ext _ _))

/-- Predicate-preserving maps are transported by the same inverse image. -/
def pullModelFunctor : PartitionSection.Model u ⥤ PartitionSection.Model (parameterPullback h u) where
  obj := pullModel h
  map f := {
    left := h.inverseImage.map f.left
    right := h.inverseImage.map f.right
    left_over := terminal.hom_ext _ _
    right_over := terminal.hom_ext _ _ }
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _
/-- Actual inverse image of predicates agrees with inverse image of their assembled section. -/
theorem pullModel_section (M : PartitionSection.Model u) :
    (pullModel h M).toSection = h.pullSection M.toSection ≫
      (classifierObjectComparison h (U := U)).hom := by
  apply (pullModel h M).partition.hom_ext
  rintro ⟨j⟩
  cases j
  · change (pullModel h M).p ≫ _ = _
    rw [PartitionSection.Model.p_section]
    change h.inverseImage.map M.bound ≫ coprod.inl =
      (h.inverseImage.map M.p ≫ (PreservesTerminal.iso h.inverseImage).hom) ≫
        ((PreservesTerminal.iso h.inverseImage).inv ≫ h.inverseImage.map M.toSection) ≫ _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← h.inverseImage.map_comp_assoc, PartitionSection.Model.p_section,
      h.inverseImage.map_comp, Category.assoc, classifierObjectComparison_inl]
  · change (pullModel h M).q ≫ _ = _
    rw [PartitionSection.Model.q_section]
    change (h.inverseImage.map M.q ≫ (PreservesTerminal.iso h.inverseImage).hom) ≫ coprod.inr =
      (h.inverseImage.map M.q ≫ (PreservesTerminal.iso h.inverseImage).hom) ≫
        ((PreservesTerminal.iso h.inverseImage).inv ≫ h.inverseImage.map M.toSection) ≫ _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← h.inverseImage.map_comp_assoc, PartitionSection.Model.q_section,
      h.inverseImage.map_comp, Category.assoc, classifierObjectComparison_inr]
end SquareKit.Internal.GeometricMorphism
