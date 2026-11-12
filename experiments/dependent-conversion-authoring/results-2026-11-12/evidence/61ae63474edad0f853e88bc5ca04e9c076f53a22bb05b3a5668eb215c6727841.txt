import Examples.ConversionTrial.Negative
namespace Examples.ConversionTrial.Negative
open SquareKit.Internal.DependentFunctions

theorem headsSameType : newest.type = older.type := rfl

theorem headsDistinctSyntax : newest ≠ older := by
  intro h
  cases h

theorem indexSolved : IndexTask := by
  have hindex : Initial.lhs.type ≠ bad.type := by
    intro h
    cases h
  exact ⟨hindex, fun h => hindex h.type⟩
end Examples.ConversionTrial.Negative
