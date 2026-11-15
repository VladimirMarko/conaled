import Examples.ConversionTrial.Initial
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.Initial
open SquareKit.Internal.DependentFunctions

theorem solved : Task := by
  refine ⟨(Dep.convertible_iff lhs rhs).mpr ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl

end Examples.ConversionTrial.Initial
