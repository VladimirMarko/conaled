import SquareKit.SheafDependentProduct
import Examples.ProjectionProducts
import Examples.FalsePointBaseChange

/-! Experimental reuse of terminal/projection consumers through the arbitrary
sheaf-map product comparisons, including a nonconstant E input. -/
noncomputable section
namespace Examples.DependentProducts
open CategoryTheory Limits Opposite SquareKit
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange

abbrev projectionName := SheafDependentProduct.curry ProjectionProducts.projection
  ProjectionProducts.negationBody

theorem projection_name : projectionName ≫
    (SheafDependentProduct.projectionComparison D D).hom.app ProjectionProducts.constantFamily =
      ProjectionProducts.negationProduct :=
  SheafDependentProduct.projection_curry D D ProjectionProducts.negationBody

/-- The previous constant-family/function-space interpretation is retained. -/
abbrev projection_function :=
  (congrArg (fun k : ProjectionProducts.parameters ⟶ ProjectionProducts.result =>
    k.left ≫ (SheafProjectionProduct.constantIso D D D).hom.left ≫
      SheafRelation.fst (SheafFunction.exponential D D) D) projection_name).trans
        ProjectionProducts.negation_comparison

/-- Both actual counits, for every family, are related by the canonical map. -/
abbrev projection_evaluation := SheafDependentProduct.projection_evaluation D D

abbrev nonconstantInput : Over E := Over.mk (SheafRelation.snd D E)
abbrev nonconstantResult :=
  (SheafDependentProduct.pi (SheafTerminalProduct.terminalMap E)).obj nonconstantInput

/-- The nonconstant E-to-D function space is recovered through the old
terminal-product and section-object comparisons. -/
def nonconstantIso : nonconstantResult.left ≅ SheafFunction.exponential E D :=
  (Over.forget _).mapIso ((SheafDependentProduct.terminalComparison E).app nonconstantInput) ≪≫
    SheafTerminalProduct.sectionsIso (SheafRelation.snd D E) ≪≫
      SheafSections.constantIso E D

def nonconstantName (b : Bool) : SheafImage.terminal ⟶ nonconstantResult.left :=
  Examples.SheafFunctions.constantName b ≫ nonconstantIso.inv

theorem nonconstant_names_distinct :
    (nonconstantName false).hom.app (op X) () ≠ (nonconstantName true).hom.app (op X) () := by
  intro h
  apply Examples.SheafFunctions.constants_distinct_at_X
  have hh := congrArg (fun z => nonconstantIso.hom.hom.app (op X) z) h
  have he (b : Bool) : nonconstantName b ≫ nonconstantIso.hom = Examples.SheafFunctions.constantName b := by
    simp [nonconstantName]
  exact (congrArg (fun k => k.hom.app (op X) ()) (he false)).symm.trans
    (hh.trans (congrArg (fun k => k.hom.app (op X) ()) (he true)))

/-- This is an operation comparison on the nonconstant input, not only an
isomorphism of result objects. -/
abbrev nonconstant_evaluation := SheafDependentProduct.terminal_evaluation E nonconstantInput

/-- For any old transposed E-family map, the arbitrary-map transpose recovers it. -/
theorem nonconstant_curry {Z : Over (MonoidalCategory.tensorUnit (Sheaf topology Type))}
    (k : (Over.pullback (SheafTerminalProduct.terminalMap E)).obj Z ⟶ nonconstantInput) :
    SheafDependentProduct.curry (SheafTerminalProduct.terminalMap E) k ≫
      (SheafDependentProduct.terminalComparison E).hom.app nonconstantInput =
        (SheafTerminalProduct.adjunction E).homEquiv Z nonconstantInput k :=
  SheafDependentProduct.terminal_curry E k

end Examples.DependentProducts
