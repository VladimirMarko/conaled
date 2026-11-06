import SquareKit.Internal.PathTransport.TwoFamilyModelApdObjects
import SquareKit.Internal.PathTransport.TwoFamilyClosedComparisonComponent
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ) (B : Family A.total)
variable (x : ULift.{u+1} (TwoFamily.Section A.data))
variable (t : ULift.{u+1} (TwoFamily.Section B.data))
local notation "M" => fullModel C D
noncomputable def apdSectionComparison :=
 closedComparison (motive M A B x).data
  (transportSection M A B x ((M).subTm t ((M).toStructuralModel.sectionSub A x))).down
  ((M).subTm t ((M).weaken _ ((M).toStructuralModel.pathFamily A x))).down
  (apdSectionValue M A B x t).down
 theorem apdSection_components :
 ClosedComparisonComponentFormula (motive M A B x).data
  (transportSection M A B x ((M).subTm t ((M).toStructuralModel.sectionSub A x))).down
  ((M).subTm t ((M).weaken _ ((M).toStructuralModel.pathFamily A x))).down
  (apdSectionValue M A B x t).down (apdSectionComparison C D A B x t) :=
 closedComparison_components _ _ _ _
end SquareKit.Internal.PathTransport.HigherInterpretation
