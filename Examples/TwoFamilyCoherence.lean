import SquareKit.Internal.PathTransport.TwoFamilyCoherence
import SquareKit.DoubleDelooping
import Mathlib.Algebra.Group.Int.Defs

/-!
# A non-discrete total fiber

The universal family includes the double delooping of the additive integers. Its
selected fiber cells remain distinct and both whiskerings retain their integer values.
-/

namespace Examples.TwoFamilyCoherence
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev universal : TwoFamily.Family StrictTwoCategory := StrictPseudofunctor.id _
abbrev integerFiber : StrictTwoCategory := ⟨DoubleDelooping.Space (Multiplicative ℤ)⟩
def point : TwoFamily.Total universal := ⟨integerFiber, DoubleDelooping.point (Multiplicative ℤ)⟩
def arrow : TwoFamily.Hom universal point point := TwoFamily.identity universal point

def cell (n : ℤ) : arrow ⟶ arrow :=
  TwoGroupoidHom.cell (𝟙 arrow.base) (Multiplicative.ofAdd n)

theorem retains_fiber (n : ℤ) : (cell n).fiber = Multiplicative.ofAdd n := rfl

theorem nontrivial_fiber : cell 1 ≠ cell 0 := by
  intro h
  have := congrArg (fun c : arrow ⟶ arrow => Multiplicative.toAdd c.fiber) h
  exact Int.one_ne_zero this

theorem left_vertical :
    TwoFamily.whiskerLeft universal arrow (cell 1 ≫ cell 2) =
      TwoFamily.whiskerLeft universal arrow (cell 1) ≫
        TwoFamily.whiskerLeft universal arrow (cell 2) :=
  TwoFamily.whiskerLeft_vertical universal arrow (cell 1) (cell 2)

theorem right_vertical :
    TwoFamily.whiskerRight universal (cell 1 ≫ cell 2) arrow =
      TwoFamily.whiskerRight universal (cell 1) arrow ≫
        TwoFamily.whiskerRight universal (cell 2) arrow :=
  TwoFamily.vertical_whiskerRight universal (cell 1) (cell 2) arrow
theorem left_retains_one :
    (TwoFamily.whiskerLeft universal arrow (cell 1)).fiber = Multiplicative.ofAdd (1 : ℤ) := rfl

theorem right_retains_one :
    (TwoFamily.whiskerRight universal (cell 1) arrow).fiber = Multiplicative.ofAdd (1 : ℤ) := rfl

/-- Interchange applies to nonzero fiber cells through the constructed instance. -/
theorem exchange :
    TwoFamily.whiskerLeft universal arrow (cell 2) ≫
      TwoFamily.whiskerRight universal (cell 1) arrow =
    TwoFamily.whiskerRight universal (cell 1) arrow ≫
      TwoFamily.whiskerLeft universal arrow (cell 2) :=
  @Bicategory.whisker_exchange (TwoFamily.Total universal) _
    point point point arrow arrow arrow arrow (cell 1) (cell 2)

example : Bicategory.Strict (TwoFamily.Total universal) := inferInstance

end Examples.TwoFamilyCoherence
