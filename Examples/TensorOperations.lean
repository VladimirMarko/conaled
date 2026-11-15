import SquareKit.TensorLaws
import SquareKit.FunctionCategory
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Algebra.Ring.Nat

namespace Examples.TensorOperations
open SquareKit CategoryTheory

/-- Natural-number resources with addition as tensor, and only identity arrows. -/
abbrev Resources := Discrete Nat
local instance : MonoidalCategory Resources := Discrete.addMonoidal Nat

def resourceTensor := TensorOps.ofMonoidal Resources
def resourceComparisons := TensorComparisons.ofMonoidal Resources

theorem resource_combination : (resourceTensor.obj ⟨2⟩ ⟨3⟩).as = 5 := rfl

theorem resource_first :
    resourceTensor.first (b := Discrete.mk 3) (𝟙 (Discrete.mk 2)) =
      𝟙 (Discrete.mk 5) := by rfl

/-- Tensor unit cannot be terminal: a resource cannot be discarded. -/
theorem no_discard : ¬ Nonempty ((Discrete.mk 1 : Resources) ⟶ resourceComparisons.unit) := by
  rintro ⟨f⟩
  have h := Discrete.eq_of_hom f
  change (1 : Nat) = 0 at h
  omega

/-- Copying would change the resource count. -/
theorem no_copy : ¬ Nonempty ((Discrete.mk 1 : Resources) ⟶
    resourceTensor.obj ⟨1⟩ ⟨1⟩) := by
  rintro ⟨f⟩
  have h := Discrete.eq_of_hom f
  change (1 : Nat) = 2 at h
  omega

def functionTensor := TensorOps.ofProducts FunctionCategory.products

theorem function_first (n : Nat) (b : Bool) :
    functionTensor.first (Nat.succ) (n,b) = (n+1,b) := rfl

theorem function_const (b : Bool) :
    (TensorComparisons.ofProducts FunctionCategory.products FunctionCategory.terminal).constLeft
      (fun _ => (7 : Nat)) b = (7,b) := rfl

theorem function_braiding (n : Nat) (b : Bool) :
    ((TensorBraiding.ofProducts FunctionCategory.products).swap Nat Bool).hom (n,b) = (b,n) := rfl

theorem resource_tensor_laws :
    TensorLaws (equality (ofCategory Resources)) resourceTensor :=
  TensorLaws.ofMonoidal Resources

theorem function_tensor_laws :
    TensorLaws (equality FunctionCategory.ops) functionTensor :=
  TensorLaws.ofProducts (equalityCongr _) FunctionCategory.laws
    FunctionCategory.productCongr FunctionCategory.productLaws

/-- An arbitrary operation of conditional's type need not commute with maps. -/
def badConditional (_ : Bool × (Nat × Nat)) : Nat := 0

theorem conditional_naturality_missing :
    (fun p => Nat.succ (badConditional p)) ≠
      (fun p : Bool × (Nat × Nat) => badConditional (p.1, (p.2.1+1, p.2.2+1))) := by
  intro h
  have bad := congrFun h (false, (0,0))
  change (1 : Nat) = 0 at bad
  omega

/-- The intended conditional does satisfy the necessary naturality equation. -/
theorem conditional_natural {A B : Type} (f : A → B) (b : Bool) (x y : A) :
    f (if b then x else y) = (if b then f x else f y) := by cases b <;> rfl

end Examples.TensorOperations
