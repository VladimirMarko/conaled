import Examples.FrozenMemoSelectedPaths
import SquareKit.Internal.DependentJudgments.FixedPathTransportSemantics
import SquareKit.Internal.DependentJudgments.OrdinaryActionSemantics
namespace Examples.FrozenOrdinaryAction
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open Examples.FrozenMemoStages
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (M : Model.{u}) (A : M.Family M.empty) (B : M.Family (M.extend M.empty A))
def paths := inputPaths M.toStructuralModel A B
def pathType := M.identity (paths M A B).family (paths M A B).x (paths M A B).y
def transport := fixedPathTransportSection M (paths M A B).family (paths M A B).x (paths M A B).y
def action := ordinaryApValue M (pathType M A B) (pathType M A B)
 (transport M A B) (paths M A B).p (paths M A B).p' (paths M A B).h
end Examples.FrozenOrdinaryAction
