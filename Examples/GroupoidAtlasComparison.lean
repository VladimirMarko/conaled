import SquareKit.SheafGroupoidCompletionRecovery
import Examples.ActionMorita

/-! The original two open disk atlases and their common refinement through actual-arrow charts. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.GroupoidAtlasComparison
open CategoryTheory Opposite SquareKit SmoothOpenSite ActionMorita
open scoped CategoryTheory.Pseudofunctor.StrongTrans

abbrev operations := SheafGroupoidCompletion.operations action (Iso.refl _)
abbrev firstChart := SheafGroupoid.Chart.canonical operations atlas.cover atlas.cover
abbrev secondChart := SheafGroupoid.Chart.canonical operations otherAtlas.cover otherAtlas.cover
abbrev commonChart := SheafGroupoid.Chart.canonical operations commonAtlas.cover commonAtlas.cover

theorem left_commutes : commonLeft.total ≫ atlas.cover = commonAtlas.cover := by
  simpa only [Category.comp_id, ActionMorita.atlas, commonAtlas, SmoothQuarterTurnArcs.diskSheaf]
    using commonLeft.total_cover

theorem right_commutes : commonRight.total ≫ otherAtlas.cover = commonAtlas.cover := by
  simpa only [Category.comp_id, otherAtlas, commonAtlas, SmoothQuarterTurnArcs.diskSheaf]
    using commonRight.total_cover

def toFirst (X : Sheaf topology Type) : commonChart.Object X ⥤ firstChart.Object X :=
  commonChart.atlasMap firstChart commonLeft.total left_commutes

def toSecond (X : Sheaf topology Type) : commonChart.Object X ⥤ secondChart.Object X :=
  commonChart.atlasMap secondChart commonRight.total right_commutes

/-- The first common-atlas route recovers the original map, under its original assumptions. -/
theorem first_recovery (X : Sheaf topology Type) :
    toFirst X ⋙ (SheafGroupoidCompletion.actionRefinementEquivalence action atlas.cover).functor =
      (SheafGroupoidCompletion.actionRefinementEquivalence action commonAtlas.cover).functor ⋙
        commonToFirst X :=
  SheafGroupoidCompletion.actionRefinementEquivalence_map action commonLeft.total left_commutes

theorem second_recovery (X : Sheaf topology Type) :
    toSecond X ⋙
        (SheafGroupoidCompletion.actionRefinementEquivalence action otherAtlas.cover).functor =
      (SheafGroupoidCompletion.actionRefinementEquivalence action commonAtlas.cover).functor ⋙
        commonToSecond X :=
  SheafGroupoidCompletion.actionRefinementEquivalence_map action commonRight.total right_commutes

/-- Both independently defined atlas routes retain the same complete quotient functor. -/
theorem common_quotient (X : Sheaf topology Type) :
    toFirst X ⋙ SheafGroupoidCompletion.chartQuotient action (Iso.refl _) firstChart =
      toSecond X ⋙ SheafGroupoidCompletion.chartQuotient action (Iso.refl _) secondChart :=
  (SheafGroupoidCompletion.atlasMap_quotient action (Iso.refl _) commonChart firstChart
    commonLeft.total left_commutes).trans
    (SheafGroupoidCompletion.atlasMap_quotient action (Iso.refl _) commonChart secondChart
      commonRight.total right_commutes).symm

/-- Common refinement agrees also as a modification of the full completion units. -/
def common_unit : PseudofunctorCoherence.ModificationIso
    (Pseudofunctor.StrongTrans.vcomp
      (commonChart.atlasTransformation firstChart commonLeft.total left_commutes)
      (SheafGroupoidCompletion.chartUnit action (Iso.refl _) firstChart))
    (Pseudofunctor.StrongTrans.vcomp
      (commonChart.atlasTransformation secondChart commonRight.total right_commutes)
      (SheafGroupoidCompletion.chartUnit action (Iso.refl _) secondChart)) :=
  SheafGroupoidCompletion.atlasUnitComparison action (Iso.refl _) commonChart firstChart
    commonLeft.total left_commutes ≪≫
  (SheafGroupoidCompletion.atlasUnitComparison action (Iso.refl _) commonChart secondChart
    commonRight.total right_commutes).symm

variable (T : Pseudofunctor (LocallyDiscrete (Sheaf topology Type)ᵒᵖ) Cat.{0,1})
  [T.IsStack (SheafCover.topology (J := topology))]

/-- This is the actual precomposition map between the two universal mapping functors. -/
def first_mapping_comparison :
    (SheafGroupoidCompletion.chartUniversalEquivalence action (Iso.refl _) firstChart T).functor ⋙
      StackLocalGeneration.restriction
        (commonChart.atlasTransformation firstChart commonLeft.total left_commutes) T ≅
    (SheafGroupoidCompletion.chartUniversalEquivalence action (Iso.refl _) commonChart T).functor :=
  SheafGroupoidCompletion.atlasRestrictionComparison action (Iso.refl _) commonChart firstChart
    commonLeft.total left_commutes T

def second_mapping_comparison :
    (SheafGroupoidCompletion.chartUniversalEquivalence action (Iso.refl _) secondChart T).functor ⋙
      StackLocalGeneration.restriction
        (commonChart.atlasTransformation secondChart commonRight.total right_commutes) T ≅
    (SheafGroupoidCompletion.chartUniversalEquivalence action (Iso.refl _) commonChart T).functor :=
  SheafGroupoidCompletion.atlasRestrictionComparison action (Iso.refl _) commonChart secondChart
    commonRight.total right_commutes T

end Examples.GroupoidAtlasComparison
