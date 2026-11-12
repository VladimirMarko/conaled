import Examples.ConversionTrial.Repair
namespace Examples.ConversionTrial.Repair
open SquareKit.Internal.DependentFunctions

theorem afterSolved : Task := by
  refine ⟨?_, rfl, ?_⟩
  · apply DepEq.sub (assignment (.var 0)) (assignment_typed (.var 0))
    exact DepEq.app
      (FuncEq.trans (FuncEq.eta (expand 1 parameter)) (FuncEq.eta parameter))
      (.neg (.var 0))
  · intro h
    cases h
end Examples.ConversionTrial.Repair
