import SquareKit.Internal.PathTransport.TwoFamilySigmaNaturality
import Examples.TwoFamilySigmaCells

namespace Examples.TwoFamilySigmaNaturality
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- An arbitrary integer base cell induces a natural component on actual pair arrows. -/
theorem integer_component_naturality (k : ℤ) :
    (TwoFamily.sigmaMap integerFamily laterFamily arrow).map pairArrow ≫
      TwoFamily.sigmaCellComponent integerFamily laterFamily
        (show arrow ⟶ arrow from Multiplicative.ofAdd k) pairPoint =
    TwoFamily.sigmaCellComponent integerFamily laterFamily
        (show arrow ⟶ arrow from Multiplicative.ofAdd k) pairPoint ≫
      (TwoFamily.sigmaMap integerFamily laterFamily arrow).map pairArrow :=
  TwoFamily.sigmaCellComponent_naturality integerFamily laterFamily _ pairArrow

/-- The packaged transformation uses the constructed component. -/
example (k : ℤ) :
    (TwoFamily.sigmaCellNaturalTransformation integerFamily laterFamily
      (show arrow ⟶ arrow from Multiplicative.ofAdd k)).app pairPoint =
    TwoFamily.sigmaCellComponent integerFamily laterFamily
      (show arrow ⟶ arrow from Multiplicative.ofAdd k) pairPoint := rfl

end Examples.TwoFamilySigmaNaturality
