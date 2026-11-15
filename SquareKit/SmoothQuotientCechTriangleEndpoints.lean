import SquareKit.SmoothQuotientCechPrimitiveTriangle

/-! Normalization of the six generated triangle endpoints, one at a time. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

theorem firstSecondComparison_triangle (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    restrictedComparison a A hΓ (SplitSheaf.Cech.firstSecond A) =
      alignedContextComparison (primitiveTriangle a A).η
        (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
        (family a (SplitSheaf.Cech.triple A))
        (primitiveTriangle a A).α (primitiveTriangle a A).β
        (primitiveTriangle a A).squareη hΓ := rfl

theorem secondThirdComparison_triangle (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    restrictedComparison a A hΓ (SplitSheaf.Cech.secondThird A) =
      alignedContextComparison (primitiveTriangle a A).θ
        (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
        (family a (SplitSheaf.Cech.triple A))
        (primitiveTriangle a A).β' (primitiveTriangle a A).δ
        (primitiveTriangle a A).squareθ hΓ := rfl

theorem firstThirdComparison_triangle (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    restrictedComparison a A hΓ (SplitSheaf.Cech.firstThird A) =
      alignedContextComparison (primitiveTriangle a A).ζ
        (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
        (family a (SplitSheaf.Cech.triple A))
        (primitiveTriangle a A).α' (primitiveTriangle a A).δ'
        (primitiveTriangle a A).squareζ hΓ := rfl

theorem tripleMiddleIso_triangle (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    eqToIso (tripleMiddleMap a A hΓ) =
      eqToIso (alignedGenerated_eq
        (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
        (family a (SplitSheaf.Cech.triple A))
        (primitiveTriangle a A).hm (primitiveTriangle a A).hb hΓ) := rfl

theorem tripleFirstIso_triangle (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    eqToIso (tripleFirstMap a A hΓ) =
      eqToIso (alignedGenerated_eq
        (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
        (family a (SplitSheaf.Cech.triple A))
        (primitiveTriangle a A).hf (primitiveTriangle a A).ha hΓ) := rfl

set_option backward.isDefEq.respectTransparency.types true in
theorem tripleLastIso_triangle (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    eqToIso (tripleLastMap a A hΓ) =
      eqToIso (alignedGenerated_eq
        (SmoothQuotientDeformations.Cech.family (a := a) (A := A))
        (family a (SplitSheaf.Cech.triple A))
        (primitiveTriangle a A).hl (primitiveTriangle a A).hd hΓ) := rfl

end SquareKit.SmoothQuotientCechLocal
