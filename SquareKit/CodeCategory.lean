import SquareKit.Category
import Compiler

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SquareKit.CodeCategory
open CategoricalCompiler
variable (Prim : Ty → Ty → Type)

def ops : CategoryOps Ty where
  Hom := Code Prim
  ident := .ident
  comp := .comp

def terminal : TerminalOps (ops Prim) where
  unit := .unit
  terminal := .terminal

def products : ProductOps (ops Prim) where
  prod := .prod
  fst := .fst
  snd := .snd
  pair := .pair

variable {Prim} {B : Type}
variable (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)

def equiv : HomEquiv (ops Prim) where
  homSetoid _ _ := {
    r := Equivalent meaning
    iseqv := ⟨fun _ _ => rfl, fun h x => (h x).symm, fun h k x => (h x).trans (k x)⟩ }

theorem congruence : CategoryCongr (ops Prim) (equiv meaning) where
  comp := by
    intro a b c g g' f f' hg hf x
    exact (congrArg (run meaning g) (hf x)).trans (hg (run meaning f' x))

theorem laws : CategoryLaws (ops Prim) (equiv meaning) where
  id_comp _ _ := rfl
  comp_id _ _ := rfl
  assoc := category_assoc meaning

theorem terminalLaws : TerminalLaws (equiv meaning) (terminal Prim) where
  unique f x := by
    change run meaning f x = ()
    exact @Subsingleton.elim Unit inferInstance _ _

theorem productCongr : ProductCongr (equiv meaning) (products Prim) where
  pair hf hg x := Prod.ext (hf x) (hg x)

theorem productLaws : ProductLaws (equiv meaning) (products Prim) where
  fst_pair := product_beta meaning
  snd_pair _ _ _ := rfl
  pair_eta := product_eta meaning

/-- The raw trees differ even though their equivalence classes agree. -/
theorem association_not_equal :
    (Code.comp (Code.comp .ident .ident) .ident : Code Prim .base .base) ≠
      Code.comp .ident (Code.comp .ident .ident) := by
  intro h
  cases h

theorem association_classes {a b c d : Ty}
    (h : Code Prim c d) (g : Code Prim b c) (f : Code Prim a b) :
    HomQuotient.classOf (E := equiv meaning) (.comp (.comp h g) f) =
      HomQuotient.classOf (Code.comp h (.comp g f)) :=
  (HomQuotient.mk_eq_iff _ _).mpr ((laws meaning).assoc h g f)

/-- Products of equivalence classes satisfy eta for every raw program. -/
theorem product_classes {a b c : Ty} (f : Code Prim a (.prod b c)) :
    HomQuotient.classOf (E := equiv meaning) (.pair (.comp .fst f) (.comp .snd f)) =
      HomQuotient.classOf f :=
  (HomQuotient.mk_eq_iff _ _).mpr ((productLaws meaning).pair_eta f)
end SquareKit.CodeCategory
