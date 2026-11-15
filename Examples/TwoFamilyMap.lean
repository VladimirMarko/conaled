import SquareKit.Internal.PathTransport.TwoFamilyMap
import Examples.TwoFamily
import Examples.TwoFamilyCoherence

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

/-- Two nonzero path comparisons retain their composite under the general action. -/
theorem mapped_path_cells_compose (m n k : ℤ) :
    SquareKit.Internal.PathTransport.TwoFamily.StrongMap.map₂ identityTransformation
      (TwoFamily.cell (TwoGroupoidPath.comparison m n) ≫
        TwoFamily.cell (TwoGroupoidPath.comparison n k)) =
    SquareKit.Internal.PathTransport.TwoFamily.StrongMap.map₂ identityTransformation
      (TwoFamily.cell (TwoGroupoidPath.comparison m n)) ≫
    SquareKit.Internal.PathTransport.TwoFamily.StrongMap.map₂ identityTransformation
      (TwoFamily.cell (TwoGroupoidPath.comparison n k)) :=
  SquareKit.Internal.PathTransport.TwoFamily.StrongMap.map₂_comp _ _ _

abbrev higherUniversal := SquareKit.Internal.PathTransport.TwoFamily.StrongMap.toHigher
  (Pseudofunctor.StrongTrans.id TwoFamilyCoherence.universal.toPseudofunctor)

/-- The constructed higher map keeps the selected nonzero fiber cell. -/
theorem higher_retains_fiber (n : ℤ) :
    (higherUniversal.map₂ (TwoFamilyCoherence.cell n)).fiber = Multiplicative.ofAdd n := by
  dsimp [higherUniversal, SquareKit.Internal.PathTransport.TwoFamily.StrongMap.toHigher,
    SquareKit.Internal.PathTransport.TwoFamily.StrongMap.map₂, TwoFamilyCoherence.cell]
  simp only [Category.comp_id]
  rfl

end Examples.TwoFamilyMap
