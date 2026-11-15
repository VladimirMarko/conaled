import Examples.ConversionTrial.Negative
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.Negative
open SquareKit.Internal.DependentFunctions

/- The changed-head equality is rejected: newest and older have the same type,
   but their normal forms retain distinct variable paths, top and function top.
   The following optional HeadTask proof checks that inequivalence. -/
theorem head_solved : HeadTask := by
  refine ⟨rfl, ?_⟩
  intro h
  have hn := FuncEq.normal_eq h
  cases hn

theorem index_solved : IndexTask := by
  constructor
  · intro h
    cases h
  · intro h
    have hn := DepEq.normal_eq h
    cases hn

end Examples.ConversionTrial.Negative
