import Examples.ConversionTrial.Repair
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.Repair
open SquareKit.Internal.DependentFunctions

theorem after_proof : Task := by
  refine ⟨(Dep.convertible_iff _ _).mpr rfl, rfl, ?_⟩
  intro h
  cases h

end Examples.ConversionTrial.Repair
