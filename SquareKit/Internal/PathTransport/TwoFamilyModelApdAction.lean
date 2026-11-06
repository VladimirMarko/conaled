import SquareKit.Internal.PathTransport.TwoFamilyModelApdObjects
import SquareKit.Internal.PathTransport.TwoFamilyIdentityActionObjects
/-! The exact J-derived source action as conjugation of its selected branch. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SourceContraction
variable {Γ Δ : Context.{u}} {i : StrictPseudofunctor Δ Γ} (c : SourceContraction i)
variable (F : Family Γ) (s t : TwoFamily.Section F.data)
variable (d : TwoFamily.Section (reindex i (closedId F.data s t)))
variable (p : TwoFamily.Section (closedId F.data s t))
theorem ValueFormula.identityAction (h : c.ValueFormula (F.identity s t) d p) :
 IdentityActionFormula i c.retraction c.homotopy F.data s t d p := by
 intro z
 exact (congrArg LocallyDiscrete.as (h z)).trans (closedId_map_obj F.data s t (c.homotopy.app z) _)
end SourceContraction
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ) (B : Family A.total)
variable (x : ULift.{u+1} (TwoFamily.Section A.data)) (t : ULift.{u+1} (TwoFamily.Section B.data))
local notation "M" => fullModel C D
def ApdSectionActionFormula : Prop :=
 IdentityActionFormula ((M).toStructuralModel.rootSub A x).down
  (rootContraction C D A x).val.retraction (rootContraction C D A x).val.homotopy
  (motive M A B x).data
  (transportSection M A B x ((M).subTm t ((M).toStructuralModel.sectionSub A x))).down
  ((M).subTm t ((M).weaken _ ((M).toStructuralModel.pathFamily A x))).down
  (apdBranchValue M A B x t).down (apdSectionValue M A B x t).down
theorem apdSection_action : ApdSectionActionFormula C D A B x t :=
 SourceContraction.ValueFormula.identityAction (rootContraction C D A x).val
  (motive M A B x) _ _ _ _ (apdSection_objects C D A B x t)
end SquareKit.Internal.PathTransport.HigherInterpretation
