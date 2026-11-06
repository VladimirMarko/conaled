import SquareKit.Internal.DependentJudgments.ApdSectionSemantics
import SquareKit.Internal.PathTransport.TwoFamilyModelJValueObjects
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ) (B : Family A.total)
variable (x y : ULift.{u+1} (TwoFamily.Section A.data))
variable (p : ULift.{u+1} (TwoFamily.Section (TwoFamily.closedId A.data x.down y.down)))
variable (t : ULift.{u+1} (TwoFamily.Section B.data))
local notation "M" => fullModel C D
theorem apdSection_objects :
 JValueFormula C D A x (apdMotiveValue M A B x t)
  (apdBranchValue M A B x t) (apdSectionValue M A B x t) :=
 j_value_objects C D A x (apdMotiveValue M A B x t) (apdBranchValue M A B x t)
theorem apdValue_objects :
 JReindexedValueFormula C D A x (apdMotiveValue M A B x t)
  (apdBranchValue M A B x t) ((M).toStructuralModel.endpointSub A x y p)
  ((M).identity ((M).subTy B ((M).toStructuralModel.sectionSub A y))
   (transportValue M A B x y p ((M).subTm t ((M).toStructuralModel.sectionSub A x)))
   ((M).subTm t ((M).toStructuralModel.sectionSub A y)))
  (apdValue M A B x y p t) := by
 have h := JValueFormula.reindex_cast C D A x (apdMotiveValue M A B x t)
  (apdBranchValue M A B x t) (apdSectionValue M A B x t)
  (apdSection_objects C D A B x t) ((M).toStructuralModel.endpointSub A x y p)
  _ (apdMotive_endpoint M A B x y p t)
 exact (congrArg (JReindexedValueFormula C D A x (apdMotiveValue M A B x t)
  (apdBranchValue M A B x t) ((M).toStructuralModel.endpointSub A x y p) _)
  (apdValue_section M A B x y p t)).mpr h
end SquareKit.Internal.PathTransport.HigherInterpretation
