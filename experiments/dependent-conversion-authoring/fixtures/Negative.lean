import Examples.ConversionTrial.Initial
namespace Examples.ConversionTrial.Negative
open SquareKit.Internal.DependentFunctions
abbrev two : Ctx 1 := .function Γ (.var 0)
abbrev newest : Func two := .var .top
abbrev older : Func two := .var (.function .top)
def HeadTask : Prop := newest.type = older.type ∧ ¬ FuncEq newest older
abbrev bad : Dep (widen 1) := .app (.var (.base .top)) (.neg (.var 1))
def IndexTask : Prop := Initial.lhs.type ≠ bad.type ∧ ¬ DepEq Initial.lhs bad
end Examples.ConversionTrial.Negative
