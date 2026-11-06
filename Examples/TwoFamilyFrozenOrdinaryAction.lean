import Examples.TwoFamilyFrozenPoint
import Examples.TwoFamilySelectedOrdinaryAction
namespace Examples.TwoFamilyFrozenOrdinaryAction
open CategoryTheory Bicategory SquareKit.Internal.PathTransport HigherInterpretation
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open Examples.TwoFamilyModelData Examples.TwoFamilyFrozenPoint Examples.FrozenMemoStages
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 3000
noncomputable section
abbrev M := fullModel integerContext integerContext
def paths := inputPaths M.toStructuralModel emptyA emptyB
def pathType := SelectedOrdinaryAction.pathType M paths
def T := SelectedOrdinaryAction.transport M paths
def sourceAction := SelectedOrdinaryAction.action M paths
set_option linter.defProp false
def action_formula := TwoFamilySelectedOrdinaryAction.action_formula integerContext integerContext paths
end
end Examples.TwoFamilyFrozenOrdinaryAction
