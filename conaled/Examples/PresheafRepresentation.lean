import Examples.PresheafSetting
import SquareKit.Internal.PresheafRepresentation

/-! Checked universal lifts and classification on the walking arrow.
The noninjective labelled substitution retains both coarse summands. -/
namespace Examples.PresheafSetting
open CategoryTheory SquareKit.Internal SquareKit.Internal.PresheafSetting
set_option backward.isDefEq.respectTransparency false

/-- Lift the formed object by its two existing structure maps. -/
def labelledLift : total (subst parameter forget) ⟶ pullback parameter forget :=
  pullbackLift parameter forget (totalMap parameter forget)
    (projection (subst parameter forget)) (totalMap_projection _ _)

/-- Uniqueness identifies the lift with the existing comparison, including its base. -/
theorem labelledLift_comparison : labelledLift = (comparison parameter forget).inv := by
  apply pullback_hom_ext parameter forget
  · rw [labelledLift, pullbackLift_original]
    simp [pullbackOriginal]
  · rw [labelledLift, pullbackLift_projection]
    simp [pullbackProjection]

/-- The coarse left point survives the universal lift. -/
theorem labelledLift_left : (labelledLift.app coarse labelledLeft).base = false ∧
    (labelledLift.app coarse labelledLeft).original = coarseLeft := by
  rw [labelledLift_comparison]
  constructor <;> rfl

/-- The fine right point retains its other label and restricts to coarse right. -/
theorem labelledLift_right : (labelledLift.app fine labelledRight).base = true ∧
    (pullback parameter forget).map step (labelledLift.app fine labelledRight) =
      labelledLift.app coarse ⟨true, .inr ()⟩ := by
  constructor
  · rfl
  · exact (NatTrans.naturality_apply labelledLift step labelledRight).symm

noncomputable def labelledClass : ClassifyingMap parameter forget :=
  modelOverEquiv parameter forget (valid.toModel.subst forget)

/-- Classifying the inhabited right model gives its expected natural map. -/
theorem labelledClass_right : labelledClass.left = forget ≫ valid.graph := by
  change (classify parameter forget (valid.toModel.subst forget)).left = _
  have h := classify_subst parameter (𝟙 terminal) forget valid.toModel
  rw [Category.comp_id] at h
  rw [h]
  congr 1
  change valid.toModel.toSection.graph ≫ totalMap parameter (𝟙 terminal) = _
  change (modelSectionEquiv parameter valid.toModel).graph ≫ totalMap parameter (𝟙 terminal) = _
  rw [valid_correspondence, totalMap_id, Category.comp_id]

/-- Pullback of both generic predicates recovers the chosen model. -/
theorem labelledClass_model : representedModel parameter forget labelledClass =
    valid.toModel.subst forget := represented_classify _ _ _

theorem labelledClass_unique (f : ClassifyingMap parameter forget)
    (h : representedModel parameter forget f = valid.toModel.subst forget) :
    f = labelledClass := represented_injective _ _ (h.trans labelledClass_model.symm)

/-- The generic model also tests a left point, absent from the constant right model. -/
theorem genericClass_left :
    (classify parameter (projection parameter) (genericModel parameter)).left.app
      coarse coarseLeft = coarseLeft := by rw [classify_generic]; rfl

/-- Precomposition by label flip is model substitution in the slice. -/
theorem labelledClass_flip :
    (classify parameter (flip ≫ forget) ((valid.toModel.subst forget).subst flip)).left =
      flip ≫ labelledClass.left := classify_subst _ _ _ _

/-- The interpreted graph of classification returns false for the right model. -/
theorem labelledClass_graph (j : Baseᵒᵖ) (b : Bool) :
    ∃ a : (total parameter).obj j,
      a = labelledClass.left.app j b ∧ false = (tag parameter).app j a := by
  apply (Presheaf.graph_evaluation labelledClass.left (tag parameter) j b false).mpr
  rw [labelledClass_right]
  rfl

/-- The existing graph comparison agrees with the universal lift on a left point. -/
theorem labelledLift_graph :
    (∃ p : (pullback parameter forget).obj coarse,
      p = labelledLift.app coarse labelledLeft ∧ true = p.original.2.isLeft) ↔
    (∃ c : (total (subst parameter forget)).obj coarse,
      c = labelledLeft ∧ true = c.2.isLeft) := by
  rw [labelledLift_comparison]
  exact graph_comparison parameter forget coarse labelledLeft true

/-- Source graph soundness over the generic represented model observes its left predicate. -/
theorem genericClass_graph :
    (∃ a : (total parameter).obj coarse,
      a = (classify parameter (projection parameter) (genericModel parameter)).left.app
        coarse coarseLeft ∧ true = (tag parameter).app coarse a) :=
  (represented_graph_P parameter (projection parameter) (genericModel parameter)
    coarse coarseLeft).mpr rfl

end Examples.PresheafSetting
