import SquareKit.SheafGroupoidAtlasComparison
import SquareKit.SheafGroupoidStackificationRecovery
import Examples.ActionMorita
import Examples.GroupoidCompletion
import Examples.IndependentBranchCompletion

/-! General completion on actual disk-atlas groupoids, ineffective arrows,
nontrivial local data and an already-stack input. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.GeneralGroupoidCompletion
open CategoryTheory Opposite SquareKit
open SmoothOpenSite SmoothQuarterTurnQuotient Orbifolds.QuarterTurn
open scoped CategoryTheory.Pseudofunctor.StrongTrans
namespace Disk

abbrev ambient := SheafGroupoidCompletion.operations ActionMorita.action (Iso.refl _)
def firstChart := SheafGroupoid.Chart.canonical ambient ActionMorita.atlas.cover ActionMorita.atlas.cover
def secondChart := SheafGroupoid.Chart.canonical ambient ActionMorita.otherAtlas.cover ActionMorita.otherAtlas.cover
def commonChart := SheafGroupoid.Chart.canonical ambient ActionMorita.commonAtlas.cover ActionMorita.commonAtlas.cover

/-- These inputs have the actual atlas totals as objects and pullbacks of all arrows. -/
abbrev first := firstChart.atlasOperations
abbrev second := secondChart.atlasOperations
abbrev common := commonChart.atlasOperations
abbrev firstOutput := SheafGroupoid.Bundle.pseudofunctor first
abbrev secondOutput := SheafGroupoid.Bundle.pseudofunctor second
abbrev commonOutput := SheafGroupoid.Bundle.pseudofunctor common

example : first.objects = ActionMorita.atlas.total := rfl
example : second.objects = ActionMorita.otherAtlas.total := rfl
example : firstOutput.IsStack (SheafCover.topology (J := topology)) := inferInstance

/-- Actual common-refinement input maps are constructed before their completed effects. -/
def commonLeft := commonChart.representedMap firstChart ActionMorita.commonLeft.total
  (by simpa only [Category.comp_id, ActionMorita.atlas, ActionMorita.commonAtlas, SmoothQuarterTurnArcs.diskSheaf]
    using ActionMorita.commonLeft.total_cover)
def commonRight := commonChart.representedMap secondChart ActionMorita.commonRight.total
  (by simpa only [Category.comp_id, ActionMorita.otherAtlas, ActionMorita.commonAtlas, SmoothQuarterTurnArcs.diskSheaf]
    using ActionMorita.commonRight.total_cover)

def completedLeft : commonOutput ⟶ firstOutput := SheafGroupoid.Bundle.completeMap commonLeft
def completedRight : commonOutput ⟶ secondOutput := SheafGroupoid.Bundle.completeMap commonRight

def commonLeft_unit : SheafGroupoid.Bundle.unit common ≫ completedLeft ≅
    commonLeft ≫ SheafGroupoid.Bundle.unit first := SheafGroupoid.Bundle.completeMap_unit commonLeft

def commonRight_unit : SheafGroupoid.Bundle.unit common ≫ completedRight ≅
    commonRight ≫ SheafGroupoid.Bundle.unit second := SheafGroupoid.Bundle.completeMap_unit commonRight

/-- The two completed common-refinement routes agree on the full ambient bundle stack. -/
def commonComparison : completedLeft ≫ firstChart.completedAmbient ≅
    completedRight ≫ secondChart.completedAmbient :=
  firstChart.completedCommonRefinement secondChart commonChart
    ActionMorita.commonLeft.total
    (by simpa only [Category.comp_id, ActionMorita.atlas, ActionMorita.commonAtlas,
      SmoothQuarterTurnArcs.diskSheaf] using ActionMorita.commonLeft.total_cover)
    ActionMorita.commonRight.total
    (by simpa only [Category.comp_id, ActionMorita.otherAtlas, ActionMorita.commonAtlas,
      SmoothQuarterTurnArcs.diskSheaf] using ActionMorita.commonRight.total_cover)

def origin (i : Bool) : first.Object realBase := ⟨ActionMorita.originLift i⟩

/-- Every arrow between distinct atlas lifts is retained before completion. -/
def originArrowEquiv (i j : Bool) : (origin i ⟶ origin j) ≃ C4 :=
  (firstChart.atlasPresentationEquivalence.fullyFaithfulFunctor.homEquiv.trans
    (SheafGroupoidCompletion.refinementEquivalence ActionMorita.action (Iso.refl _) firstChart).fullyFaithfulFunctor.homEquiv).trans
      (ActionMorita.originArrowEquiv i j)

theorem origin_arrow_count (i j : Bool) : Nat.card (origin i ⟶ origin j) = 4 := by
  rw [Nat.card_congr (originArrowEquiv i j)]
  exact card_C4

theorem distinct_lifts : origin false ≠ origin true := by
  intro h
  apply ActionMorita.originObjects_distinct
  exact congrArg (fun m : first.Object realBase =>
    (⟨m.map⟩ : SheafActionRefinement.Object ActionMorita.action ActionMorita.atlas.cover realBase)) h

/-- The actual new unit retains different labels even between different lifts. -/
theorem completed_arrows_distinct :
    (SheafGroupoid.Bundle.regularFunctor first).map ((originArrowEquiv false true).symm quarterTurn) ≠
      (SheafGroupoid.Bundle.regularFunctor first).map ((originArrowEquiv false true).symm 1) := by
  intro h
  have he := (SheafGroupoid.Bundle.regularFullyFaithful first).map_injective h
  have hg := (originArrowEquiv false true).symm.injective he
  exact SmoothTorsors.nonidentity_loop (congrArg SheafTorsor.regularArrow
    (congrArg (constantSection realBase) hg))

/-- Passing to a discrete observation loses arrows retained by the new completion. -/
theorem discrete_observation_not_faithful {B : Type}
    (F : SheafGroupoid.Bundle.Principal first realBase ⥤ Discrete B) : ¬ F.Faithful := by
  intro hF
  let := hF
  apply completed_arrows_distinct
  apply F.map_injective
  exact Subsingleton.elim _ _

end Disk

namespace IndependentCoordinates
abbrev fixed := IndependentBranchCompletion.fixedChart
abbrev switched := IndependentBranchCompletion.switchedChart

/-- Independent smooth arrow-coordinate systems enter as actual represented groupoids. -/
def changeInput := fixed.representedMap switched (𝟙 _) (Category.id_comp _)
def changeOutput := fixed.completedCoordinateChange switched

def unitComparison : SheafGroupoid.Bundle.unit fixed.atlasOperations ≫ changeOutput ≅
    changeInput ≫ SheafGroupoid.Bundle.unit switched.atlasOperations :=
  fixed.completedMap_unit switched (𝟙 _) (Category.id_comp _)

def roundtrip : changeOutput ≫ switched.completedCoordinateChange fixed ≅
    𝟙 (SheafGroupoid.Bundle.pseudofunctor fixed.atlasOperations) :=
  fixed.completedCoordinateRoundtrip switched

end IndependentCoordinates

namespace Ineffective
abbrev operations := SheafGroupoidCompletion.operations GroupoidCompletion.action (Iso.refl _)
abbrev output := SheafGroupoid.Bundle.pseudofunctor operations
abbrev unit := SheafGroupoid.Bundle.unit operations

/-- Input local data are mapped through the new unit and glued by general bundle descent. -/
def localData := (StackDescentTransformation.map unit
  (fun _ : Unit => (GroupoidCompletion.localPresentation (Iso.refl _)).cover)).obj
    (GroupoidCompletion.localData (Iso.refl _))

def glued := SheafGroupoid.Bundle.Descent.principal (SheafGroupoid.Bundle.Stack.datum localData)

/-- The constructed bundle has no global object in the original represented groupoid. -/
theorem no_global_chart : ¬ ∃ m : operations.Object SmoothClutching.base,
    Nonempty ((SheafGroupoid.Bundle.regularFunctor operations).obj m ≅ glued) := by
  rintro ⟨m, ⟨hm⟩⟩
  apply GroupoidCompletion.no_global_chart (Iso.refl _)
  refine ⟨m, ⟨?_⟩⟩
  apply (StackDescentTransformation.mapFullyFaithful unit
    (fun _ => SheafGroupoid.Bundle.regularFullyFaithful operations)).preimageIso
  exact StackDescentTransformation.canonicalObjIso unit _ m ≪≫
    (output.toDescentData _).mapIso hm ≪≫ SheafGroupoid.Bundle.Stack.localComparison localData

/-- Ineffective isotropy survives the actual new regular-bundle unit. -/
theorem ineffective_retained :
    (SheafGroupoid.Bundle.regularFunctor operations).map (GroupoidCompletion.loop (Iso.refl _) quarterTurn) ≠
      (SheafGroupoid.Bundle.regularFunctor operations).map (GroupoidCompletion.loop (Iso.refl _) 1) := by
  intro h
  exact GroupoidCompletion.loop_distinct (Iso.refl _)
    ((SheafGroupoid.Bundle.regularFullyFaithful operations).map_injective h)

end Ineffective

namespace AlreadyStack
abbrev operations := SheafGroupoidCompletion.operations GroupoidCompletion.TrivialGroup.action
  GroupoidCompletion.TrivialGroup.arrowIso

def recovery (X : Sheaf topology Type) : operations.Object X ≌ SheafGroupoid.Bundle.Principal operations X :=
  SheafGroupoid.Bundle.alreadyStack operations X

/-- This is the actual new unit, not an identity functor on a completed object. -/
example (X : Sheaf topology Type) : (recovery X).functor = SheafGroupoid.Bundle.regularFunctor operations := rfl
end AlreadyStack

end Examples.GeneralGroupoidCompletion
