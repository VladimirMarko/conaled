import Examples.ConversionTrial.Repair
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ConversionTrial
open SquareKit.Internal.DependentFunctions

theorem expand_equal {n : Nat} {Δ : Ctx n} (r : Nat) (f : Func Δ) :
    FuncEq (expand r f) f := by
  induction r with
  | zero => exact .refl f
  | succ r ih => exact .trans (.eta (expand r f)) ih

namespace Repair
 theorem after_solution : Task := by
  refine ⟨?_, rfl, ?_⟩
  · exact DepEq.sub (assignment (.var 0)) (assignment_typed (.var 0))
      (DepEq.app (expand_equal 2 parameter) (.neg (.var 0)))
  · intro h
    cases h
end Repair
end Examples.ConversionTrial
