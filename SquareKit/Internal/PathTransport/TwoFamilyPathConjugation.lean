import SquareKit.Internal.PathTransport.TwoFamilyIdentityConjugationLaw
import SquareKit.Internal.PathTransport.TwoFamilyPathBetaNatural
import SquareKit.Internal.PathTransport.TwoFamilyPathBetaComparison
/-! Conjugation for the interpreted transport section and its J-derived comparison.
The arrow action is the induced fiber functor; comparison with a separately
defined source `ap` term requires its own semantic theorem. -/
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
theorem pathTransport_conjugation :
 IdentityFiberConjugation (A.reindex (Δ := A.total) (projectionHigher A.data))
  (x.down.reindex A.data (projectionHigher A.data)) (variableSection A.data) γ
  (pathTransportSection M A x).down (pathBetaSection M A x).down :=
 identityFiberConjugation (A.reindex (Δ := A.total) (projectionHigher A.data))
  (x.down.reindex A.data (projectionHigher A.data)) (variableSection A.data) γ
  (pathTransportSection M A x).down (pathBetaSection M A x).down
noncomputable def pathConjugated :=
 @identityFiberConjugated A.total (A.reindex (Δ := A.total) (projectionHigher A.data))
  (x.down.reindex A.data (projectionHigher A.data)) (variableSection A.data) γ
  (pathTransportSection M A x).down (pathBetaSection M A x).down
theorem pathConjugated_eq
 {a b : ((x.down.reindex A.data (projectionHigher A.data)).normalObj (reindex (projectionHigher A.data) A.data) γ).fiber ⟶
 ((variableSection A.data).normalObj (reindex (projectionHigher A.data) A.data) γ).fiber}
 (h : a ⟶ b) : pathConjugated C D A x γ h = h :=
 identityFiberConjugated_eq (A.reindex (Δ := A.total) (projectionHigher A.data))
  (x.down.reindex A.data (projectionHigher A.data)) (variableSection A.data) γ
  (pathTransportSection M A x).down (pathBetaSection M A x).down h
end SquareKit.Internal.PathTransport.HigherInterpretation
