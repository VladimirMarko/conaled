import SquareKit.RightDistribution
import Examples.OptionalTransport

/-! Both branches, independent raw choices and two composed interpretations. -/
namespace Examples.RightDistribution
open SquareKit
open Examples.OptionalTransport
open Examples.ClosedTransport (Box)

abbrev functions := FunctionCategory.distribution.right

theorem function_laws : RightDistributionLaws (E := equality _) FunctionCategory.products
    FunctionCategory.coproducts functions :=
  DistributionOps.right_laws (equality_congr _) FunctionCategory.laws
    FunctionCategory.productCongr FunctionCategory.productLaws
    FunctionCategory.coproductCongr FunctionCategory.coproductLaws FunctionCategory.distributionLaws

/-- A directly selected right inverse, independent of the swap construction. -/
def selected : RightDistributionOps FunctionCategory.products FunctionCategory.coproducts where
  distribute x := match x.1 with
    | .inl b => .inl (b, x.2)
    | .inr c => .inr (c, x.2)

theorem selected_laws : RightDistributionLaws (E := equality _) FunctionCategory.products
    FunctionCategory.coproducts selected where
  collect_distribute a b c := by funext x; rcases x with ⟨x | x, y⟩ <;> rfl
  distribute_collect a b c := by funext x; rcases x with ⟨x,y⟩ | ⟨x,y⟩ <;> rfl

/-- Recover the independently chosen map through inverse uniqueness. -/
theorem selected_agrees (a b c : Type) :
    selected.distribute (a := a) (b := b) (c := c) = functions.distribute :=
  DistributionOps.right_unique (equality_congr _) FunctionCategory.laws
    FunctionCategory.productCongr FunctionCategory.productLaws
    FunctionCategory.coproductCongr FunctionCategory.coproductLaws
    FunctionCategory.distributionLaws selected_laws.distribute_collect a b c

example : functions.distribute (a := Nat) (b := Bool) (c := Nat) (.inl true, 3) =
    Sum.inl (true, 3) := rfl
example : functions.distribute (a := Nat) (b := Bool) (c := Nat) (.inr 7, 3) =
    Sum.inr (7, 3) := rfl
example (x : (Sum Bool Nat) × Nat) :
    collectRight FunctionCategory.products FunctionCategory.coproducts (functions.distribute x) = x :=
  congrFun (function_laws.collect_distribute _ _ _) x
example : selected.distribute (a := PEmpty) (b := Bool) (c := Nat) = functions.distribute :=
  selected_agrees _ _ _

abbrev wrapped := Wrapped.distribution.right

theorem wrapped_laws : RightDistributionLaws (E := equality _) Wrapped.products
    Wrapped.coproducts wrapped :=
  DistributionOps.right_laws (equality_congr _) FunctionCategory.laws
    Wrapped.products_congr Wrapped.products_laws Wrapped.coproducts_congr Wrapped.coproducts_laws
    Wrapped.distribution_laws

theorem wrap_preserves : DistributionMapLaws (equality _)
    Wrapped.wrapProducts.reverse Wrapped.wrapCoproducts functions wrapped :=
  RightDistributionMap.of_laws (equality_congr _) FunctionCategory.laws
    Wrapped.products_congr Wrapped.products_laws Wrapped.coproducts_congr Wrapped.coproducts_laws
    (RawMap.id_laws _) Wrapped.wrapProducts_preserves_products Wrapped.wrapCoproducts_preserves_coproducts
    Wrapped.wrapProducts_laws Wrapped.wrapCoproducts_laws function_laws wrapped_laws

example : wrapped.distribute (a := Nat) (b := Bool) (c := Nat) ⟨(⟨.inl true⟩, 3)⟩ =
    (⟨.inl ⟨(true, 3)⟩⟩ : Box (Sum (Box (Bool × Nat)) (Box (Nat × Nat)))) := rfl
example : wrapped.distribute (a := Nat) (b := Bool) (c := Nat) ⟨(⟨.inr 7⟩, 3)⟩ =
    (⟨.inr ⟨(7, 3)⟩⟩ : Box (Sum (Box (Bool × Nat)) (Box (Nat × Nat)))) := rfl

open CategoricalCompiler
variable {Prim : Ty → Ty → Type} {B : Type}
variable (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)

abbrev codeRight := (CodeCategory.distribution Prim).right

theorem code_laws : RightDistributionLaws (E := CodeCategory.equiv meaning)
    (CodeCategory.products Prim) (CodeCategory.coproducts Prim) (codeRight (Prim := Prim)) :=
  DistributionOps.right_laws (CodeCategory.congruence meaning) (CodeCategory.laws meaning)
    (CodeCategory.products_congr meaning) (CodeCategory.products_laws meaning)
    (CodeCategory.coproducts_congr meaning) (CodeCategory.coproducts_laws meaning)
    (CodeCategory.distribution_laws meaning)

theorem evaluation_preserves : DistributionMapLaws (equality _)
    (CodeCategory.productComparison meaning).reverse (CodeCategory.coproductComparison meaning)
    (codeRight (Prim := Prim)) functions :=
  RightDistributionMap.of_laws (equality_congr _) FunctionCategory.laws
    FunctionCategory.productCongr FunctionCategory.productLaws
    FunctionCategory.coproductCongr FunctionCategory.coproductLaws
    (CodeCategory.evaluation_laws meaning) (CodeCategory.evaluation_preserves_products meaning)
    (CodeCategory.evaluation_preserves_coproducts meaning) (CodeCategory.productComparison_laws meaning)
    (CodeCategory.coproductComparison_laws meaning) (code_laws meaning) function_laws

/-- Compose existing contracts through the changed product/sum presentation. -/
theorem composed_preserves : DistributionMapLaws (equality _)
    ((CodeCategory.productComparison meaning).reverse.comp Wrapped.wrapProducts.reverse)
    (composedCoproductComparison meaning) (codeRight (Prim := Prim)) wrapped :=
  DistributionMap.comp_laws (RawMap.id_laws _) (equality_congr _) FunctionCategory.laws
    (ProductOps.reverse_congr Wrapped.products_congr) (ProductOps.reverse_laws Wrapped.products_laws)
    Wrapped.coproducts_congr Wrapped.coproducts_laws
    (ProductMap.reverse_laws Wrapped.wrapProducts_preserves_products) Wrapped.wrapCoproducts_preserves_coproducts
    (fun a b => (Wrapped.wrapProducts_laws b a).hom_inv)
    (fun a b => (Wrapped.wrapCoproducts_laws a b).hom_inv)
    (evaluation_preserves meaning) wrap_preserves

/-- A separately selected raw inverse includes an extra identity instruction. -/
def padded : RightDistributionOps (CodeCategory.products Prim) (CodeCategory.coproducts Prim) where
  distribute := .comp .ident codeRight.distribute

theorem padded_laws : RightDistributionLaws (E := CodeCategory.equiv meaning)
    (CodeCategory.products Prim) (CodeCategory.coproducts Prim) (padded (Prim := Prim)) where
  collect_distribute a b c :=
    (CodeCategory.equiv meaning).trans ((CodeCategory.congruence meaning).comp
      ((CodeCategory.equiv meaning).refl _) ((CodeCategory.laws meaning).id_comp _))
      ((code_laws meaning).collect_distribute a b c)
  distribute_collect a b c :=
    (CodeCategory.equiv meaning).trans ((CodeCategory.congruence meaning).comp
      ((CodeCategory.laws meaning).id_comp _) ((CodeCategory.equiv meaning).refl _))
      ((code_laws meaning).distribute_collect a b c)

theorem padded_agrees (a b c : Ty) :
    (CodeCategory.equiv meaning).Rel (padded.distribute (a := a) (b := b) (c := c))
      codeRight.distribute :=
  DistributionOps.right_unique (CodeCategory.congruence meaning) (CodeCategory.laws meaning)
    (CodeCategory.products_congr meaning) (CodeCategory.products_laws meaning)
    (CodeCategory.coproducts_congr meaning) (CodeCategory.coproducts_laws meaning)
    (CodeCategory.distribution_laws meaning) (padded_laws meaning).distribute_collect a b c

/-- Uniqueness never identifies the different constructor trees. -/
theorem padded_not_equal :
    (padded (Prim := Prim)).distribute (a := .unit) (b := .base) (c := .base) ≠
      codeRight.distribute := by
  intro h
  change Code.comp .ident _ = Code.comp (.copair _ _) _ at h
  cases h

example : ¬ RightDistributionLaws (E := equality _) (CodeCategory.products Prim)
    (CodeCategory.coproducts Prim) (codeRight (Prim := Prim)) := by
  intro h
  have bad := h.distribute_collect .unit .base .base
  cases bad

end Examples.RightDistribution
