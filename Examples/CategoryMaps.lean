import SquareKit.CodeCategory
import SquareKit.CartesianMapQuotient

/-! Checked uses of map composition, induced laws and the lawful quotient adapter. -/
namespace Examples.CategoryMaps
open SquareKit CategoricalCompiler
variable {Prim : Ty → Ty → Type} {B : Type}
variable (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)

/-- Code evaluation followed by Mathlib's bundling reuses both local proofs. -/
def bundledEvaluation := (CodeCategory.evaluation meaning).comp FunctionCategory.toTypes

theorem bundledEvaluation_laws : MapLaws (bundledEvaluation meaning) (CodeCategory.equiv meaning)
    (equality (ofCategory (Type))) :=
  RawMap.comp_laws (CodeCategory.evaluation_laws meaning) FunctionCategory.toTypes_laws

/-- Associativity is inherited under semantic equivalence, including distinct raw trees. -/
theorem induced_association {a b c d : Ty}
    (h : Code Prim c d) (g : Code Prim b c) (f : Code Prim a b) :
    ((CodeCategory.evaluation meaning).induced (equality _)).Rel
      (.comp (.comp h g) f) (.comp h (.comp g f)) := by
  let F := CodeCategory.evaluation meaning
  exact (RawMap.transport_laws (F.induced_laws (equality _) rfl (fun _ _ => rfl))
    (F.induced_reflects _) (equality_congr _) FunctionCategory.laws).assoc h g f

/-- The quotient adapter is a Mathlib functor between lawful models. -/
def evaluationOnClasses := RawMap.quotientFunctor (CodeCategory.evaluation meaning)
  (CodeCategory.evaluation_laws meaning) (CodeCategory.congruence meaning) (CodeCategory.laws meaning)
  (equality_congr _) FunctionCategory.laws

theorem evaluationOnClasses_apply {a b : Ty} (f : Code Prim a b) :
    letI := HomQuotient.category (CodeCategory.congruence meaning) (CodeCategory.laws meaning)
    letI := HomQuotient.category (equality_congr FunctionCategory.ops) FunctionCategory.laws
    (evaluationOnClasses meaning).map (HomQuotient.classOf f) =
      HomQuotient.classOf (E := equality FunctionCategory.ops) (run meaning f) := rfl

/-- Composed interpretations preserve every composition, without another syntax induction. -/
theorem bundled_composition {a b c : Ty} (g : Code Prim b c) (f : Code Prim a b) :
    (bundledEvaluation meaning).map (.comp g f) =
      (ofCategory (Type)).comp ((bundledEvaluation meaning).map g)
        ((bundledEvaluation meaning).map f) := (bundledEvaluation_laws meaning).comp g f

/-- Code's semantic quotient evaluation preserves genuine Mathlib binary products. -/
theorem evaluation_preserves_products (a b : Ty) :
    letI := HomQuotient.category (CodeCategory.congruence meaning) (CodeCategory.laws meaning)
    letI := HomQuotient.category (equality_congr FunctionCategory.ops) FunctionCategory.laws
    CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.pair ⟨a⟩ ⟨b⟩)
      (evaluationOnClasses meaning) :=
  HomQuotient.preserves_binary_product
    (CodeCategory.congruence meaning) (CodeCategory.laws meaning)
    (equality_congr _) FunctionCategory.laws (CodeCategory.evaluation_laws meaning)
    (CodeCategory.products_congr meaning) FunctionCategory.productCongr
    (CodeCategory.products_laws meaning) FunctionCategory.productLaws
    (CodeCategory.productComparison_laws meaning) (CodeCategory.evaluation_preserves_products meaning) ⟨a⟩ ⟨b⟩

/-- The same quotient functor preserves the empty-diagram limit. -/
theorem evaluation_preserves_terminal :
    letI := HomQuotient.category (CodeCategory.congruence meaning) (CodeCategory.laws meaning)
    letI := HomQuotient.category (equality_congr FunctionCategory.ops) FunctionCategory.laws
    CategoryTheory.Limits.PreservesLimit
      (CategoryTheory.Functor.empty.{0} (HomQuotient (CodeCategory.ops Prim) (CodeCategory.equiv meaning)))
      (evaluationOnClasses meaning) :=
  HomQuotient.preserves_terminal
    (CodeCategory.congruence meaning) (CodeCategory.laws meaning)
    (equality_congr _) FunctionCategory.laws (CodeCategory.evaluation_laws meaning)
    (CodeCategory.terminalComparison_laws meaning)
    (CodeCategory.terminal_laws meaning) FunctionCategory.terminalLaws

end Examples.CategoryMaps
