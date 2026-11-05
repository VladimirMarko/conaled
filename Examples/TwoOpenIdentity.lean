import SquareKit.Internal.PathTransport.TwoOpenIdentity
import Examples.TwoFamily

/-! The general open identity transport acts on the selected integer path. -/
namespace Examples.TwoOpenIdentity
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
open Examples.TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
local instance : IsGroupoid (LocallyDiscrete TwoGroupoidPath.Fiber) where
  all_isIso f := by
    refine ⟨⟨Discrete.mk (inv f.as), ?_, ?_⟩⟩
    · apply Discrete.ext; exact IsIso.hom_inv_id f.as
    · apply Discrete.ext; exact IsIso.inv_hom_id f.as
local instance : ∀ x, IsGroupoid (pathFamily.obj x) := fun _ =>
  inferInstanceAs (IsGroupoid (LocallyDiscrete TwoGroupoidPath.Fiber))

def endpoints : TwoFamily.Total (TwoFamily.endpointFamily pathFamily) :=
  ⟨point.base, (point.fiber,point.fiber)⟩
def endpointArrow (m n : ℤ) : endpoints ⟶ endpoints :=
  ⟨DoubleDelooping.arrow _, (Discrete.mk (Multiplicative.ofAdd m), Discrete.mk (Multiplicative.ofAdd n))⟩

/-- Distinct endpoint arrows change the selected path by endpoint conjugation. -/
theorem transported_integer (m n k : ℤ) :
    ((TwoFamily.openIdMap pathFamily (endpointArrow m n)).obj
      (Discrete.mk (Multiplicative.ofAdd k))).as = Multiplicative.ofAdd (-m + k + n) := by
  have hi : @inv (LocallyDiscrete TwoGroupoidPath.Fiber) _ point.fiber point.fiber
      (Discrete.mk (Multiplicative.ofAdd m)) _ =
      (Discrete.mk (Multiplicative.ofAdd (-m)) : point.fiber ⟶ point.fiber) := by
    apply IsIso.inv_eq_of_hom_inv_id
    apply Discrete.ext
    change Multiplicative.ofAdd (-m) * Multiplicative.ofAdd m = 1
    simp
  change (@inv (LocallyDiscrete TwoGroupoidPath.Fiber) _ point.fiber point.fiber
      (Discrete.mk (Multiplicative.ofAdd m)) _ ≫
    (Discrete.mk (Multiplicative.ofAdd k) ≫ Discrete.mk (Multiplicative.ofAdd n))).as = _
  rw [hi]
  change Multiplicative.ofAdd n * Multiplicative.ofAdd k * Multiplicative.ofAdd (-m) = _
  simp [mul_assoc, mul_comm]

end Examples.TwoOpenIdentity
