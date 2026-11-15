import Examples.ConversionTrial.Repair
namespace Examples.ConversionTrial.Repair
open SquareKit.Internal.DependentFunctions

theorem beforeSolved : BeforeTask := by
  refine ⟨?_, rfl⟩
  apply DepEq.sub (assignment .zero) (assignment_typed .zero)
  exact DepEq.app
    (FuncEq.trans (FuncEq.eta (expand 1 parameter)) (FuncEq.eta parameter))
    (.neg (.var 0))
end Examples.ConversionTrial.Repair
