import Examples.ConversionTrial.Repair
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ConversionTrial.Repair
open SquareKit.Internal.DependentFunctions

theorem before_derivation : DepEq before beforeTarget :=
  DepEq.sub (assignment .zero) (assignment_typed .zero)
    (.app (.trans (.eta (expand 1 parameter)) (.eta parameter)) (.neg (.var 0)))

theorem before_index : before.type = oldIndex := rfl

theorem before_proof : BeforeTask := ⟨before_derivation, before_index⟩
end Examples.ConversionTrial.Repair
