import Examples.ConversionTrial.Initial
namespace Examples.ConversionTrial.HeldOut
open SquareKit.Internal.DependentFunctions
abbrev lhs := left 2 2 3
abbrev rhs := right 2 3
abbrev index : SquareKit.Internal.DependentStructural.Base 3 :=
  .neg (.neg (.neg (.neg (.var 2))))
def Task : Prop := DepEq lhs rhs ∧ lhs.type = index ∧ rhs.type = index
end Examples.ConversionTrial.HeldOut
