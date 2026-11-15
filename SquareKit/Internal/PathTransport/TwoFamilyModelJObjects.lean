import SquareKit.Internal.PathTransport.TwoFamilyFullModel
import SquareKit.Internal.PathTransport.TwoFamilyContractionObjects
import SquareKit.Internal.DependentJudgments.DerivedPathSemantics
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
set_option backward.dsimp.instances true
set_option maxHeartbeats 1000000
universe u
variable (C D : Context.{u})
local notation "M" => structuralModel C D
variable {Γ : Context.{u}} (A : Family Γ) (x : ULift.{u+1} (TwoFamily.Section A.data))
variable (E : Family (((A.reindex (Δ := A.total) (TwoFamily.projectionHigher A.data)).identity
  (x.down.reindex A.data (TwoFamily.projectionHigher A.data)) (TwoFamily.variableSection A.data)).total))
theorem j_objects : (rootContraction C D A x).val.SectionFormula E
    (fun d => ((fullModel C D).j A x .nil E ⟨d⟩).down) :=
  @SourceContraction.sectionFormula ((M).pathContext A x) Γ ((M).rootSub A x).down
    (rootContraction C D A x).val E
end SquareKit.Internal.PathTransport.HigherInterpretation
