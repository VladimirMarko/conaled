import Examples.PrivateReference462
open PrivateReference462.H1 SquareKit.DiagonalConstruction
example : ∀ a, sourceEval true a = diagonal sourceEval sourceStep a := by
  intro a
  rfl
