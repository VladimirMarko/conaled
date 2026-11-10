import SquareKit.SmoothQuotientCechTriangleEndpoints

/-! Generated overlap comparisons retain the primitive diagonal and cocycle. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory CategoryTheory.Functor SheafActionQuotient SmoothOpenSite
open SmoothQuotientDeformations Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

theorem restrictedComparison_cocycle (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    restrictedComparison a A hΓ (SplitSheaf.Cech.firstSecond A) ≪≫
      eqToIso (tripleMiddleMap a A hΓ) ≪≫
      restrictedComparison a A hΓ (SplitSheaf.Cech.secondThird A) =
    eqToIso (tripleFirstMap a A hΓ) ≪≫
      restrictedComparison a A hΓ (SplitSheaf.Cech.firstThird A) ≪≫
      (eqToIso (tripleLastMap a A hΓ)).symm := by
  rw [firstSecondComparison_triangle, secondThirdComparison_triangle, firstThirdComparison_triangle,
    tripleMiddleIso_triangle, tripleFirstIso_triangle, tripleLastIso_triangle]
  exact (primitiveTriangle a A).generatedCocycle hΓ

end SquareKit.SmoothQuotientCechLocal
