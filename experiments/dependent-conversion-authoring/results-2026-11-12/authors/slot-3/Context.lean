import Examples.ConversionTrial.Scale
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.Scale
open SquareKit.Internal.DependentFunctions

theorem context_proof : ContextTask := by
  intro k hk
  simp [contextExtraBinders] at hk
  rcases hk with rfl | rfl | rfl
  all_goals exact ⟨(Dep.convertible_iff _ _).mpr rfl, rfl⟩

end Examples.ConversionTrial.Scale
