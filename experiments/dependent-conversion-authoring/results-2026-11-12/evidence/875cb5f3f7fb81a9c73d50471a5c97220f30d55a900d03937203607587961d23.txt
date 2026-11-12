import Examples.ConversionTrial.HeldOut
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.HeldOut
open SquareKit.Internal.DependentFunctions

theorem task_proof : Task := by
  exact ⟨(Dep.convertible_iff _ _).mpr rfl, rfl, rfl⟩

end Examples.ConversionTrial.HeldOut
