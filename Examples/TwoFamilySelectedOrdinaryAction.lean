import SquareKit.Internal.PathTransport.TwoFamilyOrdinaryLeftIdentity
import Examples.FrozenOrdinaryActionSemantics
import SquareKit.Internal.PathTransport.TwoFamilyOrdinaryEndpointAction
import SquareKit.Internal.PathTransport.TwoFamilyOrdinaryBranchValues
namespace Examples.SelectedOrdinaryAction
open CategoryTheory Bicategory SquareKit.Internal.PathTransport HigherInterpretation
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open Examples.FrozenMemoStages
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (M : Typed.Model.{u}) (R : SelectedPaths M.toStructuralModel)
def pathType := M.identity R.family R.x R.y
def transport := fixedPathTransportSection M R.family R.x R.y
def action := ordinaryApValue M (pathType M R) (pathType M R) (transport M R) R.p R.p' R.h
end Examples.SelectedOrdinaryAction
namespace Examples.TwoFamilySelectedOrdinaryAction
open CategoryTheory Bicategory SquareKit.Internal.PathTransport HigherInterpretation
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open Examples.FrozenMemoStages Examples.SelectedOrdinaryAction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) (R : SelectedPaths (structuralModel C D))
local notation "M" => fullModel C D
def ActionFormula : Prop :=
 OrdinaryApEndpointActionFormula C D (pathType M R) (pathType M R) (transport M R) R.p R.p' R.h
theorem action_formula : ActionFormula C D R :=
 ordinaryApValue_action C D (pathType M R) (pathType M R) (transport M R) R.p R.p' R.h
def LeftIdentityFormula : Prop :=
 OrdinaryApLeftIdentityFormula C D (pathType M R) (pathType M R) (transport M R) R.p
theorem left_identity : LeftIdentityFormula C D R :=
 ordinaryApLeft_identity C D (pathType M R) (pathType M R) (transport M R) R.p
def BranchIdentityFormula : Prop :=
 SectionIdentityValues ((M).subTy (ordinaryApMotive M (pathType M R) (pathType M R) (transport M R) R.p)
   ((M).toStructuralModel.rootSub (pathType M R) R.p)) (pathType M R)
  (ordinaryApBranch M (pathType M R) (pathType M R) (transport M R) R.p)
  (ordinaryApply M (pathType M R) (pathType M R) (transport M R) R.p)
theorem branch_identity : BranchIdentityFormula C D R :=
 ordinaryApBranch_identity C D (pathType M R) (pathType M R) (transport M R) R.p
end Examples.TwoFamilySelectedOrdinaryAction
