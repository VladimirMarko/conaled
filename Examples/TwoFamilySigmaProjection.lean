import SquareKit.Internal.PathTransport.TwoFamilySigmaProjection
import Examples.TwoFamilySigmaLaws
/-! First projection retains the ambient and first fiber integer cells. -/
namespace Examples.TwoFamilySigmaProjection
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def totalPoint : TwoFamily.Total (TwoFamily.sigmaFamily integerFamily laterFamily) := ⟨point,pairPoint⟩
def totalArrow : totalPoint ⟶ totalPoint := ⟨arrow,pairArrow⟩
def totalCell (k m n : ℤ) : totalArrow ⟶ totalArrow :=
  ⟨Multiplicative.ofAdd k, ⟨Multiplicative.ofAdd m,Multiplicative.ofAdd n⟩⟩

example (k m n : ℤ) :
    (((TwoFamily.sigmaFirst integerFamily laterFamily).map₂ (totalCell k m n)).base,
      ((TwoFamily.sigmaFirst integerFamily laterFamily).map₂ (totalCell k m n)).fiber) =
        (Multiplicative.ofAdd k,Multiplicative.ofAdd m) := rfl

example (n : ℤ) :
    (TwoFamily.sigmaFirst integerFamily laterFamily).map₂ (totalCell 0 1 n) ≠
      (TwoFamily.sigmaFirst integerFamily laterFamily).map₂ (totalCell 0 0 n) := by
  intro h
  have hh := congr_arg_heq (fun α => α.fiber) h
  have hi : Multiplicative.ofAdd (1:ℤ) = Multiplicative.ofAdd 0 := eq_of_heq hh
  exact Int.one_ne_zero (congrArg Multiplicative.toAdd hi)
end Examples.TwoFamilySigmaProjection
