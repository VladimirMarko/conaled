import Examples.ConversionTrial.HeldOut
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.HeldOut
open SquareKit.Internal.DependentFunctions

theorem source_derivation : DepEq lhs rhs :=
  (Dep.convertible_iff lhs rhs).mpr rfl

theorem left_result_index : lhs.type = index := rfl

theorem right_result_index : rhs.type = index := rfl

theorem task_proved : Task :=
  ⟨source_derivation, left_result_index, right_result_index⟩

end Examples.ConversionTrial.HeldOut
