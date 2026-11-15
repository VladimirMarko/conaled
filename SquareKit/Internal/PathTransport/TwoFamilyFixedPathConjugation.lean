import SquareKit.Internal.PathTransport.TwoFamilyFullModel
import SquareKit.Internal.PathTransport.TwoFamilyIdentityConjugationLaw
import SquareKit.Internal.DependentJudgments.FixedPathBetaSemantics
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
open DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ)
 (x y : ULift.{u+1} (TwoFamily.Section A.data)) (γ : Γ)
local notation "M" => fullModel C D
noncomputable def fixedPathConjugated :=
 @identityFiberConjugated Γ A x.down y.down γ
  (fixedPathTransportSection M A x y).down (fixedPathBetaSection M A x y).down
theorem fixedPathConjugated_eq
 {a b : (x.down.normalObj A.data γ).fiber ⟶ (y.down.normalObj A.data γ).fiber}
 (h : a ⟶ b) : fixedPathConjugated C D A x y γ h = h :=
 identityFiberConjugated_eq A x.down y.down γ
  (fixedPathTransportSection M A x y).down (fixedPathBetaSection M A x y).down h
end SquareKit.Internal.PathTransport.HigherInterpretation
