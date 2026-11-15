import Examples.FrozenOrdinaryActionEvaluation
import Examples.FrozenMemoDisplayRealization
namespace Examples.FrozenOrdinaryAction
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open Examples.GuardedGroupoidMemo Examples.FrozenMemoStages
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.defProp false
universe u
variable (M : Model.{u}) (A : M.Family M.empty) (B : M.Family (M.extend M.empty A))
local notation "env" => Examples.FrozenMemoSignature.environment M A B
noncomputable section
/-- The original source action after the original first frozen substitution. -/
def source_action_sigma :=
 subTm_eval M env signature.input.pathAction signature.sigma
  (paths M A B).context (sigmaData M A B).display.total _ (action M A B)
  (sigmaData M A B).map (source_action M A B) (sigmaData M A B).map_eval
/-- The original source action after both original frozen substitutions. -/
def source_action_twice :=
 subTm_eval M env (Contextual.subTm signature.input.pathAction signature.sigma) signature.tau
  (sigmaData M A B).display.total (tauData M A B).display.total _
  (M.subTm (action M A B) (sigmaData M A B).map)
  (tauData M A B).map (source_action_sigma M A B) (tauData M A B).map_eval
end
end Examples.FrozenOrdinaryAction
