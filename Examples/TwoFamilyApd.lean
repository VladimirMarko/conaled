import Examples.TwoFamilyFullModel
import SquareKit.Internal.PathTransport.TwoFamilyModelApdRoot
namespace Examples.TwoFamilyApd
open CategoryTheory Bicategory SquareKit.Internal.PathTransport HigherInterpretation TwoFamily
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open Examples.TwoFamilyModelData Examples.TwoFamilyStructuralModel Examples.TwoFamilyFullModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
noncomputable def copyFamily := display.reindex (Δ := display.total) (projectionHigher display.data)
noncomputable def copy : ULift.{1} (TwoFamily.Section copyFamily.data) := ⟨variableSection display.data⟩
noncomputable def selectedAction := apdSectionValue completeModel display copyFamily chosen copy
example : HEq (completeModel.subTm selectedAction (completeModel.toStructuralModel.rootSub display chosen))
 (completeModel.reflexivity _ (completeModel.subTm copy (completeModel.toStructuralModel.sectionSub display chosen))) :=
 apdSectionValue_root completeModel display copyFamily chosen copy
example : JValueFormula integerContext integerContext display chosen
 (apdMotiveValue completeModel display copyFamily chosen copy)
 (apdBranchValue completeModel display copyFamily chosen copy) selectedAction :=
 apdSection_objects integerContext integerContext display copyFamily chosen copy
example : SectionRootIdentity
 (apdMotiveValue completeModel display copyFamily chosen copy) selectedAction
 (completeModel.toStructuralModel.rootSub display chosen).down
 (completeModel.subTy copyFamily (completeModel.toStructuralModel.sectionSub display chosen))
 (completeModel.subTm copy (completeModel.toStructuralModel.sectionSub display chosen)) :=
 apdSection_root_identity integerContext integerContext display copyFamily chosen copy
end Examples.TwoFamilyApd
