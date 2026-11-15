import SquareKit.Internal.PathTransport.TwoFamilySigmaHigherNaturality
import Examples.TwoFamilySigmaNaturality

namespace Examples.TwoFamilySigmaHigherNaturality
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Higher naturality accepts independently chosen base, first-fiber and second-fiber integers. -/
theorem three_integer_naturality (k m n : ℤ) :
    (TwoFamily.sigmaMap integerFamily laterFamily arrow).map₂ (pairCell m n) ▷
        TwoFamily.sigmaCellComponent integerFamily laterFamily
          (show arrow ⟶ arrow from Multiplicative.ofAdd k) pairPoint ≫
        eqToHom (TwoFamily.sigmaCellComponent_naturality integerFamily laterFamily
          (show arrow ⟶ arrow from Multiplicative.ofAdd k) pairArrow) =
      eqToHom (TwoFamily.sigmaCellComponent_naturality integerFamily laterFamily
          (show arrow ⟶ arrow from Multiplicative.ofAdd k) pairArrow) ≫
        TwoFamily.sigmaCellComponent integerFamily laterFamily
          (show arrow ⟶ arrow from Multiplicative.ofAdd k) pairPoint ◁
          (TwoFamily.sigmaMap integerFamily laterFamily arrow).map₂ (pairCell m n) :=
  TwoFamily.sigmaCellComponent_naturality₂ integerFamily laterFamily _ (pairCell m n)

/-- The higher naturality equation does not identify distinct second-fiber cells. -/
example :
    (TwoFamily.sigmaMap integerFamily laterFamily arrow).map₂ (pairCell 0 1) ≠
      (TwoFamily.sigmaMap integerFamily laterFamily arrow).map₂ (pairCell 0 0) :=
  Examples.TwoFamilySigmaAction.transported_second_cells_distinct

/-- The full higher transformation uses the already checked genuine component. -/
example (k : ℤ) :
    (TwoFamily.sigmaCell integerFamily laterFamily
      (show arrow ⟶ arrow from Multiplicative.ofAdd k)).app pairPoint =
    TwoFamily.sigmaCellComponent integerFamily laterFamily
      (show arrow ⟶ arrow from Multiplicative.ofAdd k) pairPoint := rfl

end Examples.TwoFamilySigmaHigherNaturality
