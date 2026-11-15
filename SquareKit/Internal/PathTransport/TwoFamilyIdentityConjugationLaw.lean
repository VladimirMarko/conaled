import SquareKit.Internal.PathTransport.TwoFamilyIdentityFiber
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Context.{u}} (A : Family Γ) (x y : TwoFamily.Section A.data) (γ : Γ)
variable (s : TwoFamily.Section (reindex (projectionHigher (A.identity x y).data) (A.identity x y).data))
variable (p : TwoFamily.Section (closedId (reindex (projectionHigher (A.identity x y).data) (A.identity x y).data) s (variableSection (A.identity x y).data)))
noncomputable def identityFiberConjugated
 {a b : (x.normalObj A.data γ).fiber ⟶ (y.normalObj A.data γ).fiber} (h : a ⟶ b) : a ⟶ b :=
 inv ((identityFiberBeta A x y γ s p).app a) ≫
  (identityFiberFunctor A x y γ s).map h ≫ (identityFiberBeta A x y γ s p).app b
theorem identityFiberConjugated_eq
 {a b : (x.normalObj A.data γ).fiber ⟶ (y.normalObj A.data γ).fiber} (h : a ⟶ b) :
 identityFiberConjugated A x y γ s p h = h := identityFiber_conjugation A x y γ s p h
/-- The entire conjugation equation, quantified over every arrow of the identity fiber. -/
def IdentityFiberConjugation : Prop :=
 ∀ {a b : (x.normalObj A.data γ).fiber ⟶ (y.normalObj A.data γ).fiber} (h : a ⟶ b),
 inv ((identityFiberBeta A x y γ s p).app a) ≫
  (identityFiberFunctor A x y γ s).map h ≫ (identityFiberBeta A x y γ s p).app b = h
theorem identityFiberConjugation : IdentityFiberConjugation A x y γ s p :=
 identityFiber_conjugation A x y γ s p
end SquareKit.Internal.PathTransport.HigherInterpretation
