import SquareKit.Internal.PathTransport.TwoFamilyClosedSections
import Examples.TwoFamilyLowerPath
/-! Closed ordinary loops and their actual source transport in the same full
model as the selected higher witness. The input path has label zero. -/
noncomputable section
namespace Examples.TwoFamilyLowerClosed
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport HigherInterpretation
open Examples.GroupoidTransport Examples.TwoFamilyModelData Examples.TwoFamilyLowerPath
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
abbrev identityFamily : Family Context.empty := lowerModel.identity emptyA ⟨fixed⟩ ⟨fixed⟩
def loop (n : ZMod 4) : ULift (TwoFamily.Section identityFamily.data) :=
  ⟨closedSection identityFamily ⟨⟨label n⟩⟩⟩
abbrev inputFamily : Family Context.empty := lowerModel.subTy emptyB (lowerModel.sectionSub emptyA ⟨fixed⟩)
def inputValue : ULift (TwoFamily.Section inputFamily.data) :=
  ⟨closedSection inputFamily ⟨⟨label 0⟩⟩⟩
def output (n : ZMod 4) := transportValue lowerModel emptyA emptyB ⟨fixed⟩ ⟨fixed⟩ (loop n) inputValue
set_option linter.defProp false
def loop_value (n : ZMod 4) := closedSection_value identityFamily (show identityFamily.data.obj emptyPoint from ⟨⟨label n⟩⟩)
def input_value := closedSection_value inputFamily (show inputFamily.data.obj emptyPoint from ⟨⟨label 0⟩⟩)
end Examples.TwoFamilyLowerClosed
