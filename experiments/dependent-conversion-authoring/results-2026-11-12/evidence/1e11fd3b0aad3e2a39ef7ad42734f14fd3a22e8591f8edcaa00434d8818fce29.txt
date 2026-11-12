import Examples.ConversionTrial.Negative
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.Negative
open SquareKit.Internal.DependentFunctions

theorem index_proved : IndexTask := by
  constructor
  · intro h
    cases h
  · intro h
    have hn := (Dep.convertible_iff Initial.lhs bad).mp h
    cases hn

-- Separate optional inequivalence proof: the normal forms retain distinct
-- variable paths even though these functions have the same result index.
theorem head_rejected : HeadTask := by
  constructor
  · rfl
  · intro h
    have hn := (Func.convertible_iff newest older).mp h
    cases hn

end Examples.ConversionTrial.Negative
