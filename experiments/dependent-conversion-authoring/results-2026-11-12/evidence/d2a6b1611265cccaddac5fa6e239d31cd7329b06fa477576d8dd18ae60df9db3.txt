import Examples.ConversionTrial.Repair
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.Repair
open SquareKit.Internal.DependentFunctions

theorem after_solved : Task := by
  refine ⟨(Dep.convertible_iff _ _).mpr ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro h
    cases h

end Examples.ConversionTrial.Repair
