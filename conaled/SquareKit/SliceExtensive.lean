import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! Extensivity passes to slices through the forgetful functor, which preserves
and reflects the relevant pullbacks and coproducts. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit
open CategoryTheory CategoryTheory.Limits
universe v u
variable {C : Type u} [Category.{v} C] [HasPullbacks C] [FinitaryExtensive C]

instance sliceFinitaryExtensive (X : C) : FinitaryExtensive (Over X) :=
  finitaryExtensive_of_preserves_and_reflects (Over.forget X)
end SquareKit
