import SquareKit.Internal.PathTransport.TwoFamilyEndpoints
import Examples.TwoFamily
import Examples.TwoIdentityTransport

/-! Endpoint formation retains the base action and independent fiber 2-cells. -/
namespace Examples.TwoFamilyEndpoints
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Both endpoints retain the selected nonzero base action. -/
theorem endpoint_action (n : ℤ) :
    ((TwoFamily.endpointFamily Examples.TwoFamily.pathFamily).map₂
      (a := DoubleDelooping.point _) (b := DoubleDelooping.point _)
      (f := DoubleDelooping.arrow _) (g := DoubleDelooping.arrow _)
      (Multiplicative.ofAdd n)).app
        (TwoGroupoidHom.pathTarget, TwoGroupoidHom.pathTarget) =
      (Discrete.mk (Multiplicative.ofAdd n), Discrete.mk (Multiplicative.ofAdd n)) := rfl

/-- Endpoint products retain two independent genuine fiber 2-cells. -/
theorem retains_two_cells (m n : ℤ) :
    (TwoFamily.doubleFunctor (StrictPseudofunctor.id Examples.TwoIdentityTransport.B)).map₂
      (a := (Examples.TwoIdentityTransport.point, Examples.TwoIdentityTransport.point))
      (b := (Examples.TwoIdentityTransport.point, Examples.TwoIdentityTransport.point))
      (f := (Examples.TwoIdentityTransport.arrow, Examples.TwoIdentityTransport.arrow))
      (g := (Examples.TwoIdentityTransport.arrow, Examples.TwoIdentityTransport.arrow))
      (Multiplicative.ofAdd m, Multiplicative.ofAdd n) =
      (Multiplicative.ofAdd m, Multiplicative.ofAdd n) := rfl

end Examples.TwoFamilyEndpoints
