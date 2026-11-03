import SquareKit.CategoryQuotient
import SquareKit.CodeCategory
import SquareKit.MatrixCategory
import SquareKit.FirstOrderCategory
import Applications.Linear.Compiler

/-! Checked uses of the same interface for syntax and additive first-order matrices. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.CategoryInstances
open SquareKit
open FirstOrderCompiler

variable (R : Type) [CommSemiring R]

def matrixObject (a : Ty) : MatrixCategory.Object R :=
  ⟨⟨MatrixCompiler.Slots a, inferInstance, inferInstance⟩⟩

/-- The existing matrix frontend uses exactly the generic matrix operations. -/
theorem matrix_comp {a b c : Ty} (g : MatrixCompiler.Code R b c) (f : MatrixCompiler.Code R a b) :
    (FirstOrderCategory.ops (MatrixCompiler.target R)).comp g f =
      (MatrixCategory.ops R).comp (a := matrixObject R a) (b := matrixObject R b)
        (c := matrixObject R c) g f := rfl

/-- Product beta for the additive frontend is a specialization of the shared matrix laws. -/
theorem matrix_first_pair {a b c : Ty}
    (f : MatrixCompiler.Code R a b) (g : MatrixCompiler.Code R a c) :
    (FirstOrderCategory.ops (MatrixCompiler.target R)).comp
      (FirstOrderCategory.products (MatrixCompiler.target R)).fst
      ((FirstOrderCategory.products (MatrixCompiler.target R)).pair f g) = f :=
  (MatrixCategory.productLaws R).fst_pair
    (a := matrixObject R a) (b := matrixObject R b) (c := matrixObject R c) f g

theorem matrix_second_pair {a b c : Ty}
    (f : MatrixCompiler.Code R a b) (g : MatrixCompiler.Code R a c) :
    (FirstOrderCategory.ops (MatrixCompiler.target R)).comp
      (FirstOrderCategory.products (MatrixCompiler.target R)).snd
      ((FirstOrderCategory.products (MatrixCompiler.target R)).pair f g) = g :=
  (MatrixCategory.productLaws R).snd_pair
    (a := matrixObject R a) (b := matrixObject R b) (c := matrixObject R c) f g

/-- Composition order: scaling by two then adding the two coordinates doubles their sum. -/
theorem matrix_add_after_pair (x y : R) :
    ((MatrixCategory.ops R).comp (a := matrixObject R (.prod .base .base))
      (b := matrixObject R (.prod .base .base)) (c := matrixObject R .base)
      (MatrixCompiler.primitive R .add)
      (MatrixCompiler.pair R
        ((MatrixCompiler.primitive R (.scale 2)) * MatrixCompiler.first R .base .base)
        ((MatrixCompiler.primitive R (.scale 2)) * MatrixCompiler.second R .base .base))).mulVec (MatrixCompiler.encode (.prod .base .base) (x,y)) =
        fun _ => 2 * x + 2 * y := by
  funext i
  cases i
  simp [MatrixCategory.ops, ofCategory, CategoryTheory.CategoryStruct.comp,
    MatrixCompiler.primitive, MatrixCompiler.pair, MatrixCompiler.first,
    MatrixCompiler.second, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, Fintype.sum_sum_type]
  change (∑ i : Sum Unit Unit, _) = _
  simp [Fintype.sum_sum_type, MatrixCompiler.encode]
end Examples.CategoryInstances
