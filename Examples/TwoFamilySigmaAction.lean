import SquareKit.Internal.PathTransport.TwoFamilySigmaAction
import Examples.TwoFamilyFiber

namespace Examples.TwoFamilySigmaAction
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The first integer is retained by transport of the dependent pair. -/
theorem transport_first_integer (m n : ℤ) :
    ((TwoFamily.sigmaMap integerFamily laterFamily arrow).map₂ (pairCell m n)).base =
      Multiplicative.ofAdd m := rfl

/-- The later integer is retained independently of the first. -/
theorem transport_second_integer (m n : ℤ) :
    HEq ((TwoFamily.sigmaMap integerFamily laterFamily arrow).map₂ (pairCell m n)).fiber
      (Multiplicative.ofAdd n) :=
  TwoFamily.sigmaMap_cell_fiber_heq integerFamily laterFamily arrow (pairCell m n)

/-- Cartesian naturality applies to a genuine, arbitrary integer cell. -/
example (k : ℤ) :
    (TwoFamily.fiberInclusion integerFamily point).map₂
        (show arrow ⟶ arrow from Multiplicative.ofAdd k) ▷
        TwoFamily.cartesianLift integerFamily arrow point ≫
        eqToHom (TwoFamily.cartesianLift_naturality integerFamily arrow arrow) =
      eqToHom (TwoFamily.cartesianLift_naturality integerFamily arrow arrow) ≫
        TwoFamily.cartesianLift integerFamily arrow point ◁
        (TwoFamily.fiberInclusion integerFamily point).map₂ (Multiplicative.ofAdd k) :=
  TwoFamily.cartesianLift_naturality₂ integerFamily arrow (Multiplicative.ofAdd k)

/-- A nonzero later cell remains distinguishable after transport. -/
theorem transported_second_cells_distinct :
    (TwoFamily.sigmaMap integerFamily laterFamily arrow).map₂ (pairCell 0 1) ≠
      (TwoFamily.sigmaMap integerFamily laterFamily arrow).map₂ (pairCell 0 0) := by
  intro h
  have hh := congr_arg_heq (fun α => α.fiber) h
  have hi : Multiplicative.ofAdd (1 : ℤ) = Multiplicative.ofAdd 0 :=
    eq_of_heq ((transport_second_integer 0 1).symm.trans (hh.trans (transport_second_integer 0 0)))
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd hi)

/-- The cartesian comparison does not discard a nonzero base cell. -/
example (k : ℤ) :
    (TwoFamily.cartesianLiftCell integerFamily
      (show arrow ⟶ arrow from Multiplicative.ofAdd k) point).base = Multiplicative.ofAdd k := rfl

end Examples.TwoFamilySigmaAction
