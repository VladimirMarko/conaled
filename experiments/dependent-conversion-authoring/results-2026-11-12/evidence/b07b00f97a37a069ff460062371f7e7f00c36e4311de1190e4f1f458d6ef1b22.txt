import Examples.ConversionTrial.Terms
namespace Examples.ConversionTrial.Initial
open SquareKit.Internal.DependentFunctions
abbrev lhs := left 1 1 2
abbrev rhs := right 1 2
abbrev index : SquareKit.Internal.DependentStructural.Base 2 := .neg (.neg (.neg (.var 1)))
def Task : Prop := DepEq lhs rhs ∧ lhs.type = index ∧ rhs.type = index
end Examples.ConversionTrial.Initial
