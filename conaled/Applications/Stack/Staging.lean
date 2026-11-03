import SquareKit.ArithmeticStaging
import Applications.Stack.Machine

namespace Arithmetic.Staging
open FirstOrderCompiler

/-- Concrete stack execution retains every tail and composes the existing backend proof. -/
theorem stack_correct (p : Program Δ Γ a) (σ : Val Int (context Δ))
    (s : List Ty) (ρ : Val Int (context Γ)) (z : StackMachine.Stack Int s) :
    StackMachine.run Arithmetic.meaning
      ((compile (StackMachine.target Prim (@Arithmetic.meaning Int _)) (specialize p σ)).code s)
      (ρ,z) = (meaning p σ ρ,z) := by
  rw [StackMachine.compile_correct, specialize_correct]

end Arithmetic.Staging
