import SquareKit.Internal.PathTransport.TwoFamilyPathTransportFunctor
import SquareKit.Internal.PathTransport.TwoFamilyPathBetaComparison
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
open DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ)
 (x : ULift.{u+1} (TwoFamily.Section A.data)) (γ : Total A.data)
local notation "M" => fullModel C D
noncomputable def pathBetaNatural :=
 identityFiberBeta (A.reindex (Δ := A.total) (projectionHigher A.data))
  (x.down.reindex A.data (projectionHigher A.data)) (variableSection A.data) γ
  (pathTransportSection M A x).down (pathBetaSection M A x).down
end SquareKit.Internal.PathTransport.HigherInterpretation
