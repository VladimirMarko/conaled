import Examples.ConversionTrial.Repair
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.Repair
open SquareKit.Internal.DependentFunctions

theorem before_solved : BeforeTask := by
  refine ⟨(Dep.convertible_iff _ _).mpr ?_, ?_⟩ <;> rfl

end Examples.ConversionTrial.Repair
