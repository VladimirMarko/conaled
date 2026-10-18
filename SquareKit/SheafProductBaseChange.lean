import SquareKit.DependentBaseChange
import SquareKit.SheafProjectionConstant

/-! Experimental dependent-product base change from terminal maps to ordinary
sheaf product projections. All maps are the canonical mates of the fixed
adjunctions, in the supported Type(max u v) section universe. -/
noncomputable section
namespace SquareKit.SheafProductBaseChange
open CategoryTheory Limits SheafRelation
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (A Γ : Sheaf J (Type (max u v)))

abbrev square := SheafProjectionProduct.projectionSquare A Γ
abbrev mate := DependentBaseChange.WithAdjunction.mate (square A Γ)
  (SheafTerminalProduct.adjunction A) (SheafProjectionProduct.adjunction A Γ)
abbrev iso := DependentBaseChange.WithAdjunction.iso (square A Γ)
  (SheafTerminalProduct.adjunction A) (SheafProjectionProduct.adjunction A Γ)

/-- The commuting pullback map respects the explicit argument/parameter comparison. -/
theorem parameter_comparison
    (X : Over (CategoryTheory.MonoidalCategory.tensorUnit (Sheaf J (Type (max u v))))) :
    (SheafProjectionProduct.parameterIso A Γ
      ((Over.pullback (SheafTerminalProduct.terminalMap Γ)).obj X)).inv ≫
        ((DependentBaseChange.pullbackComparison (square A Γ)).app X).left ≫
          pullback.fst (pullback.snd X.hom (SheafTerminalProduct.terminalMap A)) (fst A Γ) =
    SheafFunction.parameterMap A (pullback.fst X.hom (SheafTerminalProduct.terminalMap Γ)) ≫
      (SheafSections.parameterComparison A X.left).hom ≫
        ((TerminalProduct.pullbackComparison A).inv.app X).left := by
  apply pullback.hom_ext
  · have ht : ((TerminalProduct.pullbackComparison A).inv.app X).left ≫
        pullback.fst X.hom (SheafTerminalProduct.terminalMap A) =
      CartesianMonoidalCategory.fst X.left A := by
      exact (Iso.inv_comp_eq ((Over.forget A).mapIso ((TerminalProduct.pullbackComparison A).app X))).2
        (TerminalProduct.comparison_fst A X).symm
    have hp := SheafProjectionProduct.parameterIso_parameter A Γ
      ((Over.pullback (SheafTerminalProduct.terminalMap Γ)).obj X)
    simp only [Category.assoc, DependentBaseChange.comparison_value, ht,
      SheafSections.parameterComparison_fst]
    erw [← hp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  · have ht : ((TerminalProduct.pullbackComparison A).inv.app X).left ≫
        pullback.snd X.hom (SheafTerminalProduct.terminalMap A) =
      CartesianMonoidalCategory.snd X.left A := by
      exact (Iso.inv_comp_eq ((Over.forget A).mapIso ((TerminalProduct.pullbackComparison A).app X))).2
        (TerminalProduct.comparison_snd A X).symm
    have hp := SheafProjectionProduct.parameterIso_argument A Γ
      ((Over.pullback (SheafTerminalProduct.terminalMap Γ)).obj X)
    simp only [Category.assoc, DependentBaseChange.comparison_argument, ht,
      SheafSections.parameterComparison_snd]
    erw [← hp]
    simp only [Iso.inv_hom_id_assoc]
    rfl

variable (B : Sheaf J (Type (max u v)))

/-- Base change of the constant input family, preserving the actual display. -/
def inputIso : (Over.pullback (fst A Γ)).obj (Over.mk (snd B A)) ≅
    Over.mk (snd B (product A Γ)) :=
  Over.isoMk (SheafFamily.constantIso B (fst A Γ)) (SheafFamily.constantIso_display _ _)

/-- Evaluation compatibility, specialized without changing the constructed adjunction. -/
abbrev evaluation := DependentBaseChange.WithAdjunction.evaluation (square A Γ)
  (SheafTerminalProduct.adjunction A) (SheafProjectionProduct.adjunction A Γ)

/-- Transposed family maps commute with this base change. -/
abbrev curry_baseChange := DependentBaseChange.WithAdjunction.curry_baseChange (square A Γ)
  (SheafTerminalProduct.adjunction A) (SheafProjectionProduct.adjunction A Γ)

end SquareKit.SheafProductBaseChange
