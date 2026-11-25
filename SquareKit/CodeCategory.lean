import SquareKit.FunctionCategory
import SquareKit.CartesianMap
import Compiler
import SquareKit.ClosedMap
import SquareKit.FunctionOptional
import SquareKit.DistributionMap
import SquareKit.FunctionOptionalLaws

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

def coproducts : CoproductOps (ops Prim) where
  sum := .sum
  inl := .inl
  inr := .inr
  copair := .copair

def distribution : DistributionOps (ops Prim) (products Prim) (coproducts Prim) where
  distribute := .dist

def closed : ClosedOps (ops Prim) (products Prim) where
  exp := .arr
  evaluation := .apply
  curry := .curry

variable {Prim} {B : Type}
variable (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)

def equiv : HomEquiv (ops Prim) where
  homSetoid _ _ := {
    r := Equivalent meaning
    iseqv := ⟨fun _ _ => rfl, fun h x => (h x).symm, fun h k x => (h x).trans (k x)⟩ }

/-- Evaluation supplies local preservation; all category algebra is shared. -/
def evaluation : RawMap (ops Prim) FunctionCategory.ops where
  obj := Val B
  map := run meaning

theorem evaluation_laws : MapLaws (evaluation meaning) (equiv meaning)
    (equality FunctionCategory.ops) where
  congr h := funext h
  ident := rfl
  comp _ _ := rfl

theorem evaluation_reflects : (evaluation meaning).Reflects (equiv meaning)
    (equality FunctionCategory.ops) := fun h x => congrFun h x

theorem congruence : CategoryCongr (ops Prim) (equiv meaning) :=
  RawMap.transportCongr (evaluation_laws meaning) (evaluation_reflects meaning)
    (equalityCongr _)

theorem laws : CategoryLaws (ops Prim) (equiv meaning) :=
  RawMap.transportLaws (evaluation_laws meaning) (evaluation_reflects meaning)
    (equalityCongr _) FunctionCategory.laws

def terminalComparison : TerminalMap (evaluation meaning) (terminal Prim) FunctionCategory.terminal where
  hom := fun _ => PUnit.unit
  inv := fun _ => ()

theorem terminalComparison_laws : ComparisonLaws (equality _) (terminalComparison meaning) where
  hom_inv := rfl
  inv_hom := rfl

theorem evaluation_preserves_terminal : TerminalMapLaws (equality _) (terminalComparison meaning) where
  terminal := rfl

/-- Evaluation preserves product objects strictly. -/
def productComparison : ProductMap (evaluation meaning) (products Prim) FunctionCategory.products :=
  fun _ _ => ⟨id, id⟩

theorem productComparison_laws (a b : Ty) :
    ComparisonLaws (equality _) (productComparison meaning a b) := ⟨rfl, rfl⟩

theorem evaluation_preserves_products : ProductMapLaws (equality _) (productComparison meaning) where
  fst := rfl
  snd := rfl
  pair _ _ := rfl

theorem terminal_laws : TerminalLaws (equiv meaning) (terminal Prim) :=
  TerminalMap.transportLaws (evaluation_reflects meaning) (equalityCongr _) FunctionCategory.laws
    (terminalComparison_laws meaning) (evaluation_preserves_terminal meaning) FunctionCategory.terminalLaws

theorem products_congr : ProductCongr (equiv meaning) (products Prim) :=
  ProductMap.transportCongr (evaluation_laws meaning) (evaluation_reflects meaning)
    (equalityCongr _) (evaluation_preserves_products meaning) FunctionCategory.productCongr

theorem products_laws : ProductLaws (equiv meaning) (products Prim) :=
  ProductMap.transportLaws (evaluation_laws meaning) (evaluation_reflects meaning)
    (equalityCongr _) FunctionCategory.laws (productComparison_laws meaning)
    (evaluation_preserves_products meaning) FunctionCategory.productCongr FunctionCategory.productLaws

/-- Evaluation compares sum values without identifying raw syntax trees. -/
def coproductComparison : CoproductMap (evaluation meaning) (coproducts Prim)
    FunctionCategory.coproducts := fun _ _ => ⟨id, id⟩

theorem coproductComparison_laws (a b : Ty) :
    ComparisonLaws (equality _) (coproductComparison meaning a b) := ⟨rfl, rfl⟩

theorem evaluation_preserves_coproducts : CoproductMapLaws (equality _) (coproductComparison meaning) where
  inl := rfl
  inr := rfl
  copair _ _ := rfl

theorem coproducts_congr : CoproductCongr (ops Prim) (equiv meaning) (coproducts Prim) :=
  CoproductMap.transportCongr (evaluation_laws meaning) (evaluation_reflects meaning)
    (equalityCongr _) (evaluation_preserves_coproducts meaning) FunctionCategory.coproductCongr

theorem coproducts_laws : CoproductLaws (ops Prim) (equiv meaning) (coproducts Prim) :=
  CoproductMap.transportLaws (evaluation_laws meaning) (evaluation_reflects meaning)
    (equalityCongr _) FunctionCategory.laws (coproductComparison_laws meaning)
    (evaluation_preserves_coproducts meaning) FunctionCategory.coproductCongr FunctionCategory.coproductLaws

theorem evaluation_preserves_distribution : DistributionMapLaws (equality _)
    (productComparison meaning) (coproductComparison meaning)
    (distribution Prim) FunctionCategory.distribution where
  distribute := by
    intro a b c
    funext x
    rcases x with ⟨x, y | y⟩ <;> rfl

theorem distribution_laws : DistributionLaws (ops Prim) (equiv meaning)
    (products Prim) (coproducts Prim) (distribution Prim) :=
  DistributionMap.transportLaws (equalityCongr _) FunctionCategory.laws
    FunctionCategory.productCongr FunctionCategory.productLaws
    FunctionCategory.coproductCongr FunctionCategory.coproductLaws
    (evaluation_laws meaning) (evaluation_reflects meaning)
    (evaluation_preserves_products meaning) (evaluation_preserves_coproducts meaning)
    (productComparison_laws meaning) (coproductComparison_laws meaning)
    (evaluation_preserves_distribution meaning) FunctionCategory.distributionLaws

/-- Raw closures are interpreted as functions; comparison arrows are explicit. -/
def closedComparison : ClosedMap (evaluation meaning) (closed Prim) FunctionCategory.closed :=
  fun _ _ => ⟨id, id⟩

theorem closedComparison_laws (a b : Ty) :
    ComparisonLaws (equality _) (closedComparison meaning a b) := ⟨rfl, rfl⟩

theorem evaluation_preserves_closed : ClosedMapLaws (equality _) (productComparison meaning)
    (closedComparison meaning) where
  curry _ := rfl
  evaluation := rfl

theorem closed_congr : ClosedCongr (equiv meaning) (products Prim) (closed Prim) :=
  ClosedMap.transportCongr (evaluation_laws meaning) (evaluation_reflects meaning)
    (equalityCongr _) FunctionCategory.closedCongr (evaluation_preserves_closed meaning)

/-- Beta, eta and naturality use shared transport, with no induction on raw code. -/
theorem closed_laws : ClosedLaws (equiv meaning) (products Prim) (closed Prim) :=
  ClosedMap.transportLaws (evaluation_laws meaning) (evaluation_reflects meaning)
    (equalityCongr _) FunctionCategory.laws FunctionCategory.productCongr
    FunctionCategory.productLaws FunctionCategory.closedCongr FunctionCategory.closedLaws
    (productComparison_laws meaning) (closedComparison_laws meaning)
    (evaluation_preserves_products meaning) (evaluation_preserves_closed meaning)

/-- Recovery of `CategoricalCompiler.closed_eta` through the public transport interface. -/
theorem closed_eta {a b c : Ty} (f : Code Prim a (.arr b c)) :
    Equivalent meaning (.curry (.comp .apply (.pair (.comp f .fst) .snd))) f :=
  (closed_laws meaning).eta f

/-- Semantic eta does not identify the closure constructor with the original tree. -/
theorem closed_eta_not_equal :
    (Code.curry (.comp .apply (.pair (.comp .ident .fst) .snd)) :
      Code Prim (.arr .base .base) (.arr .base .base)) ≠ .ident := by
  intro h
  cases h

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
  (HomQuotient.mk_eq_iff _ _).mpr ((products_laws meaning).pair_eta f)
end SquareKit.CodeCategory
