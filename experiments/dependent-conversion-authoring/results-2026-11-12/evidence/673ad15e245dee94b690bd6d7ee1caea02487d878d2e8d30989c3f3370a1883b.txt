import Examples.ConversionTrial.Negative
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.Negative
open SquareKit.Internal.DependentFunctions

/-- Equal function indices do not identify the distinct variable heads. -/
theorem head_proof : HeadTask := by
  refine ⟨rfl, ?_⟩
  intro h
  have hn := (Func.convertible_iff newest older).mp h
  cases hn

theorem index_proof : IndexTask := by
  constructor
  · intro h
    cases h
  · intro h
    have hn := (Dep.convertible_iff Initial.lhs bad).mp h
    cases hn

end Examples.ConversionTrial.Negative
