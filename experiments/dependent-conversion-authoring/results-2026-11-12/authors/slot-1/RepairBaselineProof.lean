import Examples.ConversionTrial.Repair
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.Repair
open SquareKit.Internal.DependentFunctions

theorem before_proved : BeforeTask :=
  ⟨(Dep.convertible_iff _ _).mpr rfl, rfl⟩

end Examples.ConversionTrial.Repair
