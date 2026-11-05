import SquareKit.Internal.PathTransport.TwoFamilyHigher
import Examples.TwoFamily

/-! The actual higher extension projection retains the nonzero base action. -/
namespace Examples.TwoFamilyHigher
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoFamily

theorem projection_retains_base :
    (TwoFamily.projectionHigher pathFamily).map₂
      (cell (TwoGroupoidPath.comparison 1 0)) = Multiplicative.ofAdd (1 : ℤ) := rfl

end Examples.TwoFamilyHigher
