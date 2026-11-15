import SquareKit.Internal.PathTransport.TwoFamilyFullModel
import SquareKit.Internal.PathTransport.TwoFamilyClosedComparison
import SquareKit.Internal.DependentJudgments.PathFamilyConjugationSemantics
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
open DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u
variable (C D : Context.{u})
local notation "M" => fullModel C D
noncomputable def pathBetaHigher {Γ : Context.{u}} (A : Family Γ)
    (x : ULift.{u+1} (TwoFamily.Section A.data)) :=
  (pathBetaSection M A x).down
noncomputable def sourceIdentityComparison {Γ : Context.{u}} (A : Family Γ)
    (x y : ULift.{u+1} (TwoFamily.Section A.data))
    (p : ULift.{u+1} (TwoFamily.Section (TwoFamily.closedId A.data x.down y.down))) :=
  TwoFamily.closedComparison A.data x.down y.down p.down
noncomputable def pathBetaComparison {Γ : Context.{u}} (A : Family Γ)
    (x : ULift.{u+1} (TwoFamily.Section A.data)) :=
  sourceIdentityComparison (motive M A ((M).toStructuralModel.pathFamily A x) x)
    (pathTransportSection M A x) (pathWitnessSection M A x)
    (pathBetaSection M A x)
end SquareKit.Internal.PathTransport.HigherInterpretation
