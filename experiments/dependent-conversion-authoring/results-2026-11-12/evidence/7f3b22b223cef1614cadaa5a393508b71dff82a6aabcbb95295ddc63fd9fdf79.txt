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
 theorem before_solution : BeforeTask := by
  refine ⟨?_, rfl⟩
  exact DepEq.sub (assignment .zero) (assignment_typed .zero)
    (DepEq.app (expand_equal 2 parameter) (.neg (.var 0)))
end Repair
end Examples.ConversionTrial
