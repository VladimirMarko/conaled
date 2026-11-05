import SquareKit.Internal.PathTransport.TwoFamilyMap
import Examples.TwoFamily

/-! Coherent total maps retain the nonzero base action of the path family. -/
namespace Examples.TwoFamilyMap
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev identityTransformation := Pseudofunctor.StrongTrans.id TwoFamily.pathFamily.toPseudofunctor

theorem mapped_path_cell_retains_one :
    (SquareKit.Internal.PathTransport.TwoFamily.StrongMap.map₂ identityTransformation
      (TwoFamily.cell (TwoGroupoidPath.comparison 1 0))).base =
      Multiplicative.ofAdd (1 : ℤ) := rfl

theorem mapped_path_arrows_compose (m n : ℤ) :
    (SquareKit.Internal.PathTransport.TwoFamily.StrongMap.toFunctor identityTransformation).map
      (TwoFamily.arrow m ≫ TwoFamily.arrow n) =
    (SquareKit.Internal.PathTransport.TwoFamily.StrongMap.toFunctor identityTransformation).map
      (TwoFamily.arrow m) ≫
    (SquareKit.Internal.PathTransport.TwoFamily.StrongMap.toFunctor identityTransformation).map
      (TwoFamily.arrow n) :=
  Functor.map_comp _ _ _

end Examples.TwoFamilyMap
