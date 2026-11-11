import SquareKit.InterpretationDiagnostics
import TaskSetup462

import Examples.PrivateReference462
import TaskSetup462

namespace PrivateApplicability462

theorem extension : Tasks462.H1.changeCodes.Extension Tasks462.H1.source :=
  PrivateReference462.H1.extension

theorem product_zero : Tasks462.H2.productWeight 0 = 0 :=
  PrivateReference462.H2.productCost.map_zero

theorem product_add : ∀ a b : Nat,
    Tasks462.H2.productWeight (a+b) = Tasks462.H2.productWeight a + Tasks462.H2.productWeight b :=
  PrivateReference462.H2.productCost.map_add

theorem final_zero : Tasks462.H2.finalWeight 0 = 0 :=
  PrivateReference462.H2.finalCost.map_zero

theorem final_add : ∀ a b : Nat × Nat,
    Tasks462.H2.finalWeight (a+b) = Tasks462.H2.finalWeight a + Tasks462.H2.finalWeight b :=
  PrivateReference462.H2.finalCost.map_add

theorem shifted_zero_refuted : ¬ Tasks462.H2.shifted 0 = 0 :=
  PrivateReference462.H2.shifted_zero_rejected

end PrivateApplicability462

namespace Requested
def weight : (Nat × Nat) → (Nat) := Tasks462.H2.finalWeight
def initial : Resources.Measured (Int) (Nat × Nat) := Resources.reweight Tasks462.H2.productWeight Tasks462.H2.compiledSeed
def transition : (Int) → (Int) → Resources.Measured (Int) (Nat × Nat) := fun x acc => Resources.reweight Tasks462.H2.productWeight (Tasks462.H2.transition x acc)
def requirement_0 : Prop := weight 0 = 0
#transport_requirement Requested.requirement_0
def requirement_1 : Prop := ∀ a b : (Nat × Nat), weight (a+b) = weight a + weight b
#transport_requirement Requested.requirement_1
def requestPresent : Unit := ()
#check initial
#check transition
#check weight
#transport_audit Requested.requestPresent

end Requested
