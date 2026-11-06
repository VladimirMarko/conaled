import Examples.FrozenOrdinaryActionSemantics
import Examples.FixedPathTransportEvaluation
import SquareKit.Internal.DependentJudgments.FrozenPathAction
import SquareKit.Internal.DependentJudgments.OrdinaryActionEvaluation
/-! Evaluate the typed ordinary action on the unchanged frozen input. -/
namespace Examples.FrozenOrdinaryAction
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open Examples.GuardedGroupoidMemo Examples.FrozenMemoStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (M : Model.{u}) (A : M.Family M.empty) (B : M.Family (M.extend M.empty A))
theorem source_action :
 signature.input.pathAction.eval (Contextual.algebra M) (Examples.FrozenMemoSignature.environment M A B) =
 .term (paths M A B).context _ (action M A B) := by
 let e := inputPaths_eval M A B
 have ht := Examples.FixedPathTransportEvaluation.fixedPathTransport_eval M
  (Examples.FrozenMemoSignature.environment M A B) signature.input.Γ signature.input.A
  signature.input.x signature.input.y (paths M A B).context (paths M A B).family
  (paths M A B).x (paths M A B).y e.context_eval e.family_eval e.x_eval e.y_eval
 exact ordinaryAp_eval M (Examples.FrozenMemoSignature.environment M A B)
  signature.input.Γ (Contextual.identity signature.input.A signature.input.x signature.input.y)
  (Contextual.identity signature.input.A signature.input.x signature.input.y)
  signature.input.p signature.input.p' signature.input.h
  (Contextual.fixedPathTransportTerm signature.input.Γ signature.input.A signature.input.x signature.input.y)
  (paths M A B).context (pathType M A B) (pathType M A B) (transport M A B)
  (paths M A B).p (paths M A B).p' (paths M A B).h
  e.context_eval e.toPointsEvaluation.path_eval e.toPointsEvaluation.path_eval
  e.p_eval e.p'_eval e.h_eval ht
end Examples.FrozenOrdinaryAction
