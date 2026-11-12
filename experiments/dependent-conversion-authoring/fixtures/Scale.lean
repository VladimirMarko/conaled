import Examples.ConversionTrial.Initial
namespace Examples.ConversionTrial.Scale
open SquareKit.Internal.DependentFunctions
/-- Each list is a factorwise task family; dimensions are not combined. -/
def compositionSizes : List Nat := [1,4,8]
def contextExtraBinders : List Nat := [1,3,7]
def substitutionSizes : List Nat := [1,2,4]
def CompositionTask : Prop := ∀ r ∈ compositionSizes,
  DepEq (left 1 r 2) (right 1 2) ∧ (left 1 r 2).type = Initial.index
def ContextTask : Prop := ∀ k ∈ contextExtraBinders,
  DepEq (left k 1 2) (right k 2) ∧ (left k 1 2).type = (right k 2).type
def SubstitutionTask : Prop := ∀ d ∈ substitutionSizes,
  DepEq (left 1 1 d) (right 1 d) ∧ (left 1 1 d).type = (right 1 d).type
end Examples.ConversionTrial.Scale
