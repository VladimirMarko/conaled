import SquareKit.InterpretationDiagnostics
import TaskSetup462

import TaskSetup462
namespace AssistedH2
open Tasks462.H2
theorem product_zero : productWeight 0 = 0 := rfl
theorem product_add (a b : Nat) : productWeight (a+b) = productWeight a + productWeight b := by
  apply Prod.ext
  · rfl
  · change 2*(a+b) = 2*a+2*b
    omega
theorem final_zero : finalWeight 0 = 0 := rfl
theorem final_add (a b : Nat × Nat) : finalWeight (a+b) = finalWeight a + finalWeight b := by
  change (a.1+b.1)+3*(a.2+b.2) = (a.1+3*a.2)+(b.1+3*b.2)
  omega
end AssistedH2

namespace Requested
def weight : (Nat) → (Nat × Nat) := Tasks462.H2.productWeight
def initial : Resources.Measured (Int) (Nat) := Tasks462.H2.compiledSeed
def transition : (Int) → (Int) → Resources.Measured (Int) (Nat) := Tasks462.H2.transition
def requirement_0 : Prop := weight 0 = 0
#transport_requirement Requested.requirement_0
def requirement_1 : Prop := ∀ a b : (Nat), weight (a+b) = weight a + weight b
#transport_requirement Requested.requirement_1
def requestPresent : Unit := ()
#check initial
#check transition
#check weight
theorem certificate_0 : requirement_0 := AssistedH2.product_zero
#transport_audit Requested.certificate_0

end Requested
