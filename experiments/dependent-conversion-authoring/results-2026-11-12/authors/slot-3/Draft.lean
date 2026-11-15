import Examples.ConversionTrial.Initial
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.Initial
open SquareKit.Internal.DependentFunctions

/-- The released source terms have the same canonical form, and both retain
    the exact expected base index. -/
theorem task_proof : Task := by
  refine ⟨(Dep.convertible_iff lhs rhs).mpr ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl

end Examples.ConversionTrial.Initial
