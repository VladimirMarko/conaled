import Examples.ClosedTransport

/-! Optional laws through evaluation and a change of product/sum presentation. -/
namespace Examples.OptionalTransport
open SquareKit
open Examples.ClosedTransport (Box)
universe u
namespace Wrapped
open FunctionCategory
abbrev products := Examples.ClosedTransport.Wrapped.products
abbrev productComparison := Examples.ClosedTransport.Wrapped.productComparison
abbrev productComparison_laws := Examples.ClosedTransport.Wrapped.productComparison_laws
abbrev interpretation_preserves_products := Examples.ClosedTransport.Wrapped.interpretation_preserves_products
abbrev interpretation := Examples.ClosedTransport.Wrapped.interpretation
abbrev products_congr := Examples.ClosedTransport.Wrapped.products_congr
abbrev products_laws := Examples.ClosedTransport.Wrapped.products_laws
abbrev wrapProducts := Examples.ClosedTransport.Wrapped.wrapProducts
abbrev wrapProducts_laws := Examples.ClosedTransport.Wrapped.wrapProducts_laws
abbrev wrapProducts_preserves_products := Examples.ClosedTransport.Wrapped.wrapProducts_preserves_products

def coproducts : CoproductOps ops.{u} where
  sum a b := Box (Sum a b)
  inl a := ⟨.inl a⟩
  inr b := ⟨.inr b⟩
  copair f g x := Sum.elim f g x.value

def distribution : DistributionOps ops.{u} products coproducts where
  distribute x := match x.value.2.value with
    | .inl b => ⟨.inl ⟨(x.value.1, b)⟩⟩
    | .inr c => ⟨.inr ⟨(x.value.1, c)⟩⟩

def coproductComparison : CoproductMap interpretation coproducts FunctionCategory.coproducts :=
  fun _ _ => ⟨Box.value, Box.mk⟩
theorem coproductComparison_laws (a b : Type u) :
    ComparisonLaws (equality _) (coproductComparison a b) := ⟨rfl, rfl⟩
theorem interpretation_preserves_coproducts : CoproductMapLaws (equality _) coproductComparison where
  inl := rfl
  inr := rfl
  copair _ _ := rfl

theorem coproducts_congr : CoproductCongr ops.{u} (equality _) coproducts :=
  CoproductMap.transportCongr (RawMap.id_laws _) (fun h => h) (equalityCongr _)
    interpretation_preserves_coproducts FunctionCategory.coproductCongr

theorem coproducts_laws : CoproductLaws ops.{u} (equality _) coproducts :=
  CoproductMap.transportLaws (RawMap.id_laws _) (fun h => h) (equalityCongr _)
    FunctionCategory.laws coproductComparison_laws interpretation_preserves_coproducts
    FunctionCategory.coproductCongr FunctionCategory.coproductLaws

theorem interpretation_preserves_distribution : DistributionMapLaws (equality ops.{u}) productComparison
    coproductComparison distribution FunctionCategory.distribution where
  distribute := by
    intro a b c
    funext x
    rcases x with ⟨x, ⟨y | y⟩⟩ <;> rfl

theorem distribution_laws : DistributionLaws ops.{u} (equality _) products coproducts distribution :=
  DistributionMap.transportLaws (equalityCongr _) FunctionCategory.laws
    FunctionCategory.productCongr FunctionCategory.productLaws
    FunctionCategory.coproductCongr FunctionCategory.coproductLaws
    (RawMap.id_laws _) (fun h => h) interpretation_preserves_products interpretation_preserves_coproducts
    productComparison_laws coproductComparison_laws interpretation_preserves_distribution FunctionCategory.distributionLaws

def wrapCoproducts : CoproductMap interpretation FunctionCategory.coproducts coproducts :=
  fun _ _ => ⟨Box.mk, Box.value⟩
theorem wrapCoproducts_laws (a b : Type u) :
    ComparisonLaws (equality _) (wrapCoproducts a b) := ⟨rfl, rfl⟩
theorem wrapCoproducts_preserves_coproducts : CoproductMapLaws (equality _) wrapCoproducts where
  inl := rfl
  inr := rfl
  copair _ _ := rfl

theorem wrap_preserves_distribution : DistributionMapLaws (equality ops.{u}) wrapProducts
    wrapCoproducts FunctionCategory.distribution distribution where
  distribute := by
    intro a b c
    funext x
    rcases x with ⟨x, y | y⟩ <;> rfl

/-- A selected right branch survives both changes of carrier. -/
example (x z : Nat) : distribution.distribute (a := Nat) (b := Bool) (c := Nat)
    ⟨(x, ⟨.inr z⟩)⟩ = ⟨.inr ⟨(x, z)⟩⟩ := rfl

example (x : Box (Nat × Box (Sum Bool Nat))) :
    collect ops products coproducts (distribution.distribute x) = x :=
  congrFun (distribution_laws.collect_distribute _ _ _) x

example {a b c : Type u} (f : Box (Sum a b) → c) :
    coproducts.copair (fun x => f ⟨.inl x⟩) (fun y => f ⟨.inr y⟩) = f :=
  coproducts_laws.eta f
end Wrapped
open CategoricalCompiler
variable {Prim : Ty → Ty → Type} {B : Type}
variable (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)

def composedInterpretation := (CodeCategory.evaluation meaning).comp Wrapped.interpretation
def composedProductComparison := (CodeCategory.productComparison meaning).comp Wrapped.wrapProducts
def composedCoproductComparison := (CodeCategory.coproductComparison meaning).comp Wrapped.wrapCoproducts

theorem composedInterpretation_laws : MapLaws (composedInterpretation meaning) (CodeCategory.equiv meaning) (equality _) :=
  RawMap.comp_laws (CodeCategory.evaluation_laws meaning) (RawMap.id_laws _)

theorem composedProductComparison_laws (a b : Ty) :
    ComparisonLaws (equality _) (composedProductComparison meaning a b) :=
  Comparison.comp_laws (equalityCongr _) FunctionCategory.laws
    (Comparison.map_laws (RawMap.id_laws _) (CodeCategory.productComparison_laws meaning a b))
    (Wrapped.wrapProducts_laws _ _)

theorem composedCoproductComparison_laws (a b : Ty) :
    ComparisonLaws (equality _) (composedCoproductComparison meaning a b) :=
  CoproductMap.comp_inverse (RawMap.id_laws _) (equalityCongr _) FunctionCategory.laws
    (CodeCategory.coproductComparison_laws meaning) Wrapped.wrapCoproducts_laws a b

theorem composedInterpretation_preserves_products : ProductMapLaws (equality _) (composedProductComparison meaning) :=
  ProductMap.comp_laws (RawMap.id_laws _) (equalityCongr _) FunctionCategory.laws
    (CodeCategory.evaluation_preserves_products meaning) Wrapped.wrapProducts_preserves_products

theorem composedInterpretation_preserves_coproducts : CoproductMapLaws (equality _) (composedCoproductComparison meaning) :=
  CoproductMap.comp_laws (RawMap.id_laws _) (equalityCongr _) FunctionCategory.laws
    (CodeCategory.evaluation_preserves_coproducts meaning) Wrapped.wrapCoproducts_preserves_coproducts

/-- Compose the two operation-preservation contracts before transporting source laws. -/
theorem composedInterpretation_preserves_distribution : DistributionMapLaws (equality _)
    (composedProductComparison meaning) (composedCoproductComparison meaning)
    (CodeCategory.distribution Prim) Wrapped.distribution :=
  DistributionMap.comp_laws (RawMap.id_laws _) (equalityCongr _) FunctionCategory.laws
    Wrapped.products_congr Wrapped.products_laws Wrapped.coproducts_congr Wrapped.coproducts_laws
    Wrapped.wrapProducts_preserves_products Wrapped.wrapCoproducts_preserves_coproducts
    (fun a b => (Wrapped.wrapProducts_laws a b).hom_inv)
    (fun a b => (Wrapped.wrapCoproducts_laws a b).hom_inv)
    (CodeCategory.evaluation_preserves_distribution meaning) Wrapped.wrap_preserves_distribution

/-- Forward preservation remains available with raw constructor equality as the
source relation, although the source distribution inverse laws fail there. -/
theorem raw_preservation_without_inverse_laws :
    MapLaws (composedInterpretation meaning) (equality _) (equality _) ∧
    DistributionMapLaws (equality _) (composedProductComparison meaning) (composedCoproductComparison meaning)
      (CodeCategory.distribution Prim) Wrapped.distribution ∧
    ¬ DistributionLaws (CodeCategory.ops Prim) (equality _)
      (CodeCategory.products Prim) (CodeCategory.coproducts Prim)
      (CodeCategory.distribution Prim) := by
  refine ⟨?_, composedInterpretation_preserves_distribution meaning, ?_⟩
  · exact RawMap.comp_laws
      (show MapLaws (CodeCategory.evaluation meaning) (equality _) (equality _) from
        { congr := fun h => congrArg _ h, ident := rfl, comp := fun _ _ => rfl })
      (RawMap.id_laws _)
  · intro h
    have bad := h.distribute_collect .base .base .base
    cases bad

/-- The separately chosen source relation is retained after two interpretations. -/
theorem composedInterpretation_distribution_laws : DistributionLaws (CodeCategory.ops Prim)
    (CodeCategory.equiv meaning) (CodeCategory.products Prim) (CodeCategory.coproducts Prim)
    (CodeCategory.distribution Prim) :=
  DistributionMap.transportLaws (equalityCongr _) FunctionCategory.laws
    Wrapped.products_congr Wrapped.products_laws Wrapped.coproducts_congr Wrapped.coproducts_laws
    (composedInterpretation_laws meaning) (CodeCategory.evaluation_reflects meaning)
    (composedInterpretation_preserves_products meaning) (composedInterpretation_preserves_coproducts meaning)
    (composedProductComparison_laws meaning) (composedCoproductComparison_laws meaning)
    (composedInterpretation_preserves_distribution meaning) Wrapped.distribution_laws

example : CoproductMapLaws (equality FunctionCategory.ops)
    (CoproductMap.id Wrapped.coproducts) := CoproductMap.id_laws FunctionCategory.laws _

example : DistributionMapLaws (equality FunctionCategory.ops)
    (ProductMap.id Wrapped.products) (CoproductMap.id Wrapped.coproducts)
    Wrapped.distribution Wrapped.distribution :=
  DistributionMap.id_laws (equalityCongr _) FunctionCategory.laws
    Wrapped.products_congr Wrapped.products_laws Wrapped.coproducts_congr Wrapped.coproducts_laws _

/-- Arbitrary code arrows recover coproduct eta through shared law transport. -/
example {a b c : Ty} (f : Code Prim (.sum a b) c) :
    Equivalent meaning (.copair (.comp f .inl) (.comp f .inr)) f :=
  (CodeCategory.coproducts_laws meaning).eta f

/-- Evaluation induces laws without being injective on raw code. -/
example : CoproductLaws (CodeCategory.ops Prim)
    ((CodeCategory.evaluation meaning).induced (equality _)) (CodeCategory.coproducts Prim) :=
  CoproductMap.transportLaws
    ((CodeCategory.evaluation meaning).inducedLaws (equality _) rfl (fun _ _ => rfl))
    ((CodeCategory.evaluation meaning).induced_reflects _)
    (equalityCongr _) FunctionCategory.laws (CodeCategory.coproductComparison_laws meaning)
    (CodeCategory.evaluation_preserves_coproducts meaning) FunctionCategory.coproductCongr
    FunctionCategory.coproductLaws

/-- Evaluation cannot reflect the stronger relation of raw constructor equality. -/
example : ¬ (CodeCategory.evaluation meaning).Reflects (equality _) (equality _) := by
  intro h
  have bad := h (f := (Code.comp .ident .ident : Code Prim .base .base))
    (g := .ident) (by rfl)
  cases bad

end Examples.OptionalTransport
