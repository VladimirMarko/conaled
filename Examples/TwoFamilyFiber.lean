import SquareKit.Internal.PathTransport.TwoFamilyFiber
import Examples.TwoOpenIdentityHigher

/-! Fiber inclusion and iterated total fibers retain two independent integer cell components. -/
namespace Examples.TwoFamilyFiber
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local instance : IsGroupoid B where
  all_isIso f := by
    obtain ⟨g, h, k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g, h, k⟩⟩
local instance : ∀ x, IsGroupoid (integerFamily.obj x) := fun _ => inferInstanceAs (IsGroupoid B)
local instance : ∀ x, IsLocallyGroupoid (integerFamily.obj x) := fun _ =>
  inferInstanceAs (IsLocallyGroupoid B)

/-- A higher fiber cell is not erased by inclusion into the total context. -/
theorem inclusion_retains_integer (k : ℤ) :
    HEq ((TwoFamily.fiberInclusion integerFamily point).map₂
      (show arrow ⟶ arrow from Multiplicative.ofAdd k)).fiber (Multiplicative.ofAdd k) :=
  TwoFamily.fiberInclusionCell_fiber_heq integerFamily point _

/-- An admitted family over the full earlier context. -/
def laterFamily : TwoFamily.Family (TwoFamily.Total integerFamily) :=
  TwoFamily.reindex (TwoFamily.projectionHigher integerFamily) integerFamily

local instance : ∀ x, IsGroupoid (laterFamily.obj x) := fun x =>
  inferInstanceAs (IsGroupoid (integerFamily.obj x.base))
local instance : ∀ x, IsLocallyGroupoid (laterFamily.obj x) := fun x =>
  inferInstanceAs (IsLocallyGroupoid (integerFamily.obj x.base))

abbrev pairFiber := TwoFamily.sigmaFiber integerFamily point laterFamily
def pairPoint : pairFiber := ⟨point, point⟩
def pairArrow : pairPoint ⟶ pairPoint := ⟨arrow, arrow⟩

/-- Both levels of the dependent pair have independent genuine integer 2-cells. -/
def pairCell (m n : ℤ) : pairArrow ⟶ pairArrow :=
  ⟨Multiplicative.ofAdd m, Multiplicative.ofAdd n⟩

theorem retained_first_cell (m n : ℤ) : (pairCell m n).base = Multiplicative.ofAdd m := rfl

theorem retained_second_cell (m n : ℤ) : (pairCell m n).fiber = Multiplicative.ofAdd n := rfl

theorem distinct_second_cells : pairCell 0 1 ≠ pairCell 0 0 := by
  intro h
  have hh := congr_arg_heq (fun α : pairArrow ⟶ pairArrow => α.fiber) h
  have hi : (Multiplicative.ofAdd (1 : ℤ)) = Multiplicative.ofAdd 0 := eq_of_heq hh
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd hi)

example : IsGroupoid pairFiber := inferInstance
example : IsLocallyGroupoid pairFiber := inferInstance

end Examples.TwoFamilyFiber
