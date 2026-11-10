import SquareKit.MorphismRestriction
import SquareKit.FunctionCategory

namespace Examples.MorphismRestriction
open SquareKit

def admissible {A B : Type} (_ : A → B) := Bool

def closure : SquareKit.MorphismRestriction.CategoryClosure FunctionCategory.ops admissible where
  ident := false
  comp a b := Bool.xor a b

def chosen (w : Bool) : SquareKit.MorphismRestriction.Hom FunctionCategory.ops admissible Nat Nat :=
  ⟨Nat.succ, w⟩

theorem choices_distinct : chosen false ≠ chosen true := by
  intro h
  exact Bool.false_ne_true (congrArg SquareKit.MorphismRestriction.Hom.sat h)

theorem choices_related :
    (SquareKit.MorphismRestriction.equiv closure (equality FunctionCategory.ops)).Rel
      (chosen false) (chosen true) := rfl

theorem inherited_category :
    CategoryLaws (SquareKit.MorphismRestriction.ops closure)
      (SquareKit.MorphismRestriction.equiv closure (equality FunctionCategory.ops)) :=
  SquareKit.MorphismRestriction.laws closure (equalityCongr _) FunctionCategory.laws

theorem forgotten_composition (m n : Bool) (x : Nat) :
    (SquareKit.MorphismRestriction.forget closure).map
      ((SquareKit.MorphismRestriction.ops closure).comp (chosen m) (chosen n)) x = x+2 := rfl

def productClosure : SquareKit.MorphismRestriction.ProductClosure
    (M := admissible) FunctionCategory.products where
  fst := false
  snd := false
  pair a b := a && b

def restrictedProducts := SquareKit.MorphismRestriction.products closure FunctionCategory.products productClosure

theorem restricted_product_laws : ProductLaws
    (SquareKit.MorphismRestriction.equiv closure (equality FunctionCategory.ops)) restrictedProducts :=
  SquareKit.MorphismRestriction.productLaws closure FunctionCategory.products productClosure FunctionCategory.productLaws

theorem product_witness_not_lawful_raw :
    ((SquareKit.MorphismRestriction.ops closure).comp restrictedProducts.snd
      (restrictedProducts.pair (chosen false) (chosen true))).sat ≠ (chosen true).sat := by change false ≠ true; decide

theorem product_semantic_recovery :
    (SquareKit.MorphismRestriction.equiv closure (equality FunctionCategory.ops)).Rel
      ((SquareKit.MorphismRestriction.ops closure).comp restrictedProducts.snd
        (restrictedProducts.pair (chosen false) (chosen true))) (chosen true) :=
  restricted_product_laws.snd_pair _ _
end Examples.MorphismRestriction
