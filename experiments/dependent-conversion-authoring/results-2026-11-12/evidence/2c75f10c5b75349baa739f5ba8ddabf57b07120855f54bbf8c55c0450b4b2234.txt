import Examples.ConversionTrial.HeldOut
namespace Examples.ConversionTrial.HeldOut
open SquareKit.Internal.DependentFunctions

theorem solved : Task := by
  refine ⟨?_, rfl, rfl⟩
  apply DepEq.sub (liftedNegate 2) (liftedNegate_typed 2)
  apply DepEq.sub (liftedNegate 2) (liftedNegate_typed 2)
  apply DepEq.sub (liftedNegate 2) (liftedNegate_typed 2)
  let f : Func (widen 2) := .var (.base (.base .top))
  exact DepEq.app
    (FuncEq.trans (FuncEq.eta (etaExpand f)) (FuncEq.eta f))
    (.neg (.var 2))
end Examples.ConversionTrial.HeldOut
