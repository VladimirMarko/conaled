import Examples.ConversionTrial.Repair
import SquareKit.Internal.DependentFunctionConversion

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ConversionTrial.Repair
open SquareKit.Internal.DependentFunctions

theorem after_derivation : DepEq after afterTarget :=
  (Dep.convertible_iff _ _).mpr rfl

theorem after_index : after.type = newIndex := rfl

theorem old_index_rejected : after.type ≠ oldIndex := by
  intro h
  cases h

theorem repair_proved : Task :=
  ⟨after_derivation, after_index, old_index_rejected⟩

end Examples.ConversionTrial.Repair
