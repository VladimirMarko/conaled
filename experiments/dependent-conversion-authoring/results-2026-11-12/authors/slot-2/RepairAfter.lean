import Examples.ConversionTrial.Repair
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ConversionTrial.Repair
open SquareKit.Internal.DependentFunctions

theorem after_derivation : DepEq after afterTarget :=
  DepEq.sub (assignment (.var 0)) (assignment_typed (.var 0))
    (.app (.trans (.eta (expand 1 parameter)) (.eta parameter)) (.neg (.var 0)))

theorem after_index : after.type = newIndex := rfl

theorem reject_old_index : after.type ≠ oldIndex := by
  intro h
  change newIndex = oldIndex at h
  cases h

theorem after_proof : Task := ⟨after_derivation, after_index, reject_old_index⟩
end Examples.ConversionTrial.Repair
