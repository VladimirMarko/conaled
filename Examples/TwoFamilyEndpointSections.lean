import SquareKit.Internal.PathTransport.TwoFamilyEndpointSections
import Examples.TwoOpenIdentityHigher
/-! Paired sections and their projections retain genuine endpoint cells. -/
namespace Examples.TwoFamilyEndpointSections
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher
open TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

example (m n : ℤ) : ((endpointProjection integerFamily true).map₂ (endpointCell m n)).fiber =
    Multiplicative.ofAdd m := rfl
example (m n : ℤ) : ((endpointProjection integerFamily false).map₂ (endpointCell m n)).fiber =
    Multiplicative.ofAdd n := rfl

abbrev displayed := reindex (projectionHigher integerFamily) integerFamily
abbrev selected := variableSection integerFamily

def totalPoint : Total integerFamily := ⟨point,point⟩
def totalArrow : totalPoint ⟶ totalPoint := ⟨arrow,arrow⟩
def totalCell (k m : ℤ) : totalArrow ⟶ totalArrow :=
  ⟨Multiplicative.ofAdd k,Multiplicative.ofAdd m⟩

theorem selected_second_retained (k m : ℤ) :
    HEq ((((endpointPair displayed selected selected).lift.comp
      (endpointProjection displayed false)).map₂ (totalCell k m)).fiber)
      (Multiplicative.ofAdd m) := by
  rw [endpointPair_second]
  rfl

example : ¬ HEq ((((endpointPair displayed selected selected).lift.comp
    (endpointProjection displayed false)).map₂ (totalCell 0 1)).fiber)
      (Multiplicative.ofAdd (0:ℤ)) := by
  intro h
  have hi : Multiplicative.ofAdd (1:ℤ) = Multiplicative.ofAdd 0 :=
    eq_of_heq ((selected_second_retained 0 1).symm.trans h)
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd hi)
end Examples.TwoFamilyEndpointSections
