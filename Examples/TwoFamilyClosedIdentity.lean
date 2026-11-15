import SquareKit.Internal.PathTransport.TwoFamilyClosedIdentity
import Examples.TwoFamilyEndpointSections
/-! The closed identity fiber retains the integer-valued higher witnesses. -/
namespace Examples.TwoFamilyClosedIdentity
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyEndpointSections
open TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
local instance : IsGroupoid B where
  all_isIso f := by
    obtain ⟨g,h,k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g,h,k⟩⟩
local instance : ∀ x, IsGroupoid (integerFamily.obj x) := fun _ => inferInstanceAs (IsGroupoid B)
local instance : ∀ x, IsLocallyGroupoid (integerFamily.obj x) := fun _ =>
  inferInstanceAs (IsLocallyGroupoid B)

def identityPoint : (closedId displayed selected selected).obj totalPoint := ⟨arrow⟩
def selectedHigherPath (h : ℤ) : identityPoint ⟶ identityPoint := ⟨Multiplicative.ofAdd h⟩

example : selectedHigherPath 1 ≠ selectedHigherPath 0 := by
  intro h
  have hi : Multiplicative.ofAdd (1:ℤ) = Multiplicative.ofAdd 0 := congrArg (fun p => p.as) h
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd hi)

example : HEq (((closedReflexivity displayed selected).lift.obj totalPoint).fiber)
    identityPoint := closedReflexivity_obj displayed selected totalPoint
end Examples.TwoFamilyClosedIdentity
