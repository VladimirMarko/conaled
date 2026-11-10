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

end Examples.MorphismRestriction
