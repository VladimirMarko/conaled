import Examples.ConversionTrial.Negative
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ConversionTrial.Negative
open SquareKit.Internal.DependentFunctions

theorem head_same_type : newest.type = older.type := rfl

theorem distinct_head_syntax : newest ≠ older := by
  intro h
  cases h

theorem bad_index_neq : Initial.lhs.type ≠ bad.type := by
  intro h
  cases h

theorem index_proof : IndexTask := by
  refine ⟨bad_index_neq, ?_⟩
  intro h
  exact bad_index_neq h.type
end Examples.ConversionTrial.Negative
