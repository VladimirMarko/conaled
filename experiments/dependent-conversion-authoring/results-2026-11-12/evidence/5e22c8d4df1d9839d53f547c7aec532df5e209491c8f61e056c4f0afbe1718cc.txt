import Examples.ConversionTrial.Initial
namespace Examples.ConversionTrial.Repair
open SquareKit.Internal.DependentFunctions
open SquareKit.Internal.DependentStructural (Base)
/-- Unlike weakening the original argument, this assigns the newly free base variable. -/
def assignment (a : Base 2) : Sub (widen 1) Γ where
  base _ := a
  dep
    | .function .top => .point
    | .function (.family (.base v)) => nomatch v
  func
    | .top => .var (.base .top)
    | .function (.family (.base v)) => nomatch v

theorem assignment_typed (a : Base 2) : (assignment a).Typed where
  dep
    | .function .top => rfl
    | .function (.family (.base v)) => nomatch v
  func
    | .top => rfl
    | .function (.family (.base v)) => nomatch v

abbrev before := (assignment .zero).depSub (source 2)
abbrev beforeTarget := (assignment .zero).depSub target
abbrev after := (assignment (.var 0)).depSub (source 2)
abbrev afterTarget := (assignment (.var 0)).depSub target
abbrev oldIndex : Base 2 := .neg .zero
abbrev newIndex : Base 2 := .neg (.var 0)
def BeforeTask : Prop := DepEq before beforeTarget ∧ before.type = oldIndex
def Task : Prop := DepEq after afterTarget ∧ after.type = newIndex ∧ after.type ≠ oldIndex
end Examples.ConversionTrial.Repair
