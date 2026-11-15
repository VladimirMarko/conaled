import SquareKit.Internal.PathTransport.TwoFamilyModelJObjects
import SquareKit.Internal.PathTransport.TwoFamilyBranchObjects
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
private theorem sectionCast_up {Γ : Context.{u}} {A B : Family Γ} (e : A = B)
    (b : TwoFamily.Section A.data) :
    cast (congrArg (fun F => ULift.{u+1} (TwoFamily.Section F.data)) e) (ULift.up b) =
      ULift.up (TwoFamily.Section.cast (congrArg Family.data e) b) := by
  cases e
  rfl
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ) (B : Family A.total)
variable (x : ULift.{u+1} (TwoFamily.Section A.data))
local notation "M" => fullModel C D
set_option maxHeartbeats 1000000 in
theorem transportSection_objects :
    (rootContraction C D A x).val.BranchFormula (motive M A B x)
      ((M).subTy B ((M).toStructuralModel.sectionSub A x)) (motive_root M A B x).symm
      (fun b => (transportSection M A B x ⟨b⟩).down) := by
  have h := @SourceContraction.SectionFormula.cast_input
    ((M).toStructuralModel.pathContext A x) Γ ((M).toStructuralModel.rootSub A x).down
    (rootContraction C D A x).val (motive M A B x)
    (fun d => ((M).j A x .nil (motive M A B x) ⟨d⟩).down)
    (j_objects C D A x (motive M A B x))
    ((M).subTy B ((M).toStructuralModel.sectionSub A x)) (motive_root M A B x).symm
  have e : (fun b => (transportSection M A B x ⟨b⟩).down) =
      (fun d => ((M).j A x .nil (motive M A B x)
        ⟨TwoFamily.Section.cast (congrArg Family.data (motive_root M A B x).symm) d⟩).down) := by
    funext b
    unfold transportSection
    apply congrArg (fun d => ((M).j A x .nil (motive M A B x) d).down)
    exact sectionCast_up (motive_root M A B x).symm b
  rw [e]
  exact h
end SquareKit.Internal.PathTransport.HigherInterpretation
