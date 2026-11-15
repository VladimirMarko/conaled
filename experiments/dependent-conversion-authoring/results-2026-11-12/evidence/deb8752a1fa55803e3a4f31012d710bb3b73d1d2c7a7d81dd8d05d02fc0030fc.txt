import Examples.ConversionTrial.Negative
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ConversionTrial.Negative
open SquareKit.Internal.DependentFunctions

theorem head_types_equal : newest.type = older.type := rfl

theorem heads_syntactically_distinct : newest ≠ older := by
  intro h
  cases h

theorem index_solution : IndexTask := by
  have h : Initial.lhs.type ≠ bad.type := by
    intro h
    cases h
  exact ⟨h, fun he => h he.type⟩

end Examples.ConversionTrial.Negative
