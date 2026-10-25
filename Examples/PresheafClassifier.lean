import Examples.PresheafRepresentation
import SquareKit.Internal.PresheafClassifierComparison

/-! The walking-arrow example passes through the categorical classifier
comparison without losing the two labels or the two summands. -/
noncomputable section
set_option autoImplicit false
namespace Examples.PresheafSetting
open CategoryTheory CategoryTheory.Limits SquareKit.Internal SquareKit.Internal.PresheafSetting
set_option backward.isDefEq.respectTransparency false

/-- The labelled substitution still classifies the old actual model after the new comparison. -/
theorem labelledClassifier_section :
    ((modelPartitionEquivalence (subst parameter forget)).functor.obj
      (valid.toModel.subst forget)).toSection =
      modelClassifierSectionEquiv (subst parameter forget) (valid.toModel.subst forget) :=
  PartitionSection.ofSection_section _ _

/-- The coproduct comparison sends the independently constructed left point to the left injection. -/
theorem classifier_left_injection :
    formedLeft parameter ≫ (formedClassifierIso parameter).hom = coprod.inl :=
  formedLeft_classifier parameter

/-- The right point uses the other summand with its terminal comparison. -/
theorem classifier_right_injection :
    formedRight parameter ≫ (formedClassifierIso parameter).hom =
      (Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal).hom ≫ coprod.inr :=
  formedRight_classifier parameter

/-- Returning through the classifier isomorphism recovers the coarse left witness exactly. -/
theorem classifier_coarse_left :
    (formedClassifierIso parameter).inv.left.app coarse
      ((formedClassifierIso parameter).hom.left.app coarse coarseLeft) = coarseLeft := by
  exact congrArg (fun t => t.left.app coarse coarseLeft) (formedClassifierIso parameter).hom_inv_id

/-- The fine right witness and its restriction remain distinct from the coarse left witness. -/
theorem classifier_fine_right :
    (total parameter).map step
      ((formedClassifierIso parameter).inv.left.app fine
        ((formedClassifierIso parameter).hom.left.app fine finePoint)) = coarseRight := by
  have he := congrArg (fun t => t.left.app fine finePoint) (formedClassifierIso parameter).hom_inv_id
  change (formedClassifierIso parameter).inv.left.app fine
    ((formedClassifierIso parameter).hom.left.app fine finePoint) = finePoint at he
  rw [he]
  rfl
end Examples.PresheafSetting
