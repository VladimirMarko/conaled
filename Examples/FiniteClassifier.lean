import Examples.FiniteSetting
import SquareKit.Internal.FiniteClassifierComparison

/-! The varying finite model passes through the categorical classifier and
returns its original dependent choices, including the bound witness. -/
noncomputable section
set_option autoImplicit false
namespace Examples.FiniteSetting
open CategoryTheory CategoryTheory.Limits SquareKit.Internal SquareKit.Internal.FiniteSetting

/-- Recover the original dependent section from the new classifier section. -/
def recoveredSection : Section varying :=
  overSection varying
    ((Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal).hom ≫
      modelClassifierSectionEquiv varying varyingModel ≫ (formedClassifierIso varying).inv)

theorem recoveredSection_eq : recoveredSection = varyingSection := by
  change (sectionOverEquiv varying).symm
    ((Over.mkIdTerminal.uniqueUpToIso terminalIsTerminal).hom ≫
      modelClassifierSectionEquiv varying varyingModel ≫ (formedClassifierIso varying).inv) = _
  have he := (modelClassifierSectionEquiv varying).left_inv varyingModel
  change (modelSectionEquiv varying).symm _ = varyingModel at he
  apply (modelSectionEquiv varying).symm.injective
  exact he.trans (by simpa using congrArg (modelSectionEquiv varying).symm varying_correspondence)

/-- The false point retains its left proof witness. -/
theorem recovered_false : recoveredSection false = .inl ⟨rfl⟩ := by
  rw [recoveredSection_eq]
  rfl

/-- The true point retains the independent right singleton. -/
theorem recovered_true : recoveredSection true = .inr () := by
  rw [recoveredSection_eq]
  rfl

/-- The categorical model comparison assembles exactly the same classifier section. -/
theorem varying_classifier_section :
    ((modelPartitionEquivalence varying).functor.obj varyingModel).toSection =
      modelClassifierSectionEquiv varying varyingModel :=
  PartitionSection.ofSection_section _ _
end Examples.FiniteSetting
