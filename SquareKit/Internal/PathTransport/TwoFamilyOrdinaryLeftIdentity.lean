import SquareKit.Internal.PathTransport.TwoFamilyRootedSectionAction
import SquareKit.Internal.PathTransport.TwoFamilyModelOrdinaryAction
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A B : Family Γ)
variable (t : ULift.{u+1} (TwoFamily.Section (reindex (projectionHigher A.data) B.data)))
variable (x : ULift.{u+1} (TwoFamily.Section A.data))
local notation "M" => fullModel C D
def OrdinaryApLeftIdentityFormula : Prop :=
 ∀ z, HEq (((ordinaryApLeft M A B t x).down.normalMap
  (motive M A ((M).subTy B ((M).weaken Γ A)) x).data
  ((rootContraction C D A x).val.homotopy.app z)).fiber)
  (𝟙 ((ordinaryApply M A B t x).down.normalObj B.data z.base.base).fiber)
theorem ordinaryApLeft_identity : OrdinaryApLeftIdentityFormula C D A B t x := by
 have h := rootContraction_section_action C D A B x (ordinaryApply M A B t x).down
 run_tac Lean.Elab.Tactic.withMainContext do
  let d ← Lean.Meta.getLocalDeclFromUserName `h
  (← Lean.Elab.Tactic.getMainGoal).assign d.toExpr
  Lean.Elab.Tactic.replaceMainGoal []
end SquareKit.Internal.PathTransport.HigherInterpretation
