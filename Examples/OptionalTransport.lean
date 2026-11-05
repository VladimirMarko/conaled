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
abbrev productInverse := Examples.ClosedTransport.Wrapped.productInverse
abbrev preservesProducts := Examples.ClosedTransport.Wrapped.preservesProducts
abbrev interpretation := Examples.ClosedTransport.Wrapped.interpretation
abbrev productCongr := Examples.ClosedTransport.Wrapped.productCongr
abbrev productLaws := Examples.ClosedTransport.Wrapped.productLaws
abbrev wrapProducts := Examples.ClosedTransport.Wrapped.wrapProducts
abbrev wrapProductInverse := Examples.ClosedTransport.Wrapped.wrapProductInverse
abbrev wrapPreservesProducts := Examples.ClosedTransport.Wrapped.wrapPreservesProducts

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
theorem coproductInverse (a b : Type u) :
    ComparisonLaws (equality _) (coproductComparison a b) := ⟨rfl, rfl⟩
theorem preservesCoproducts : CoproductMapLaws (equality _) coproductComparison where
  inl := rfl
  inr := rfl
  copair _ _ := rfl

theorem coproductCongr : CoproductCongr ops.{u} (equality _) coproducts :=
  CoproductMap.transportCongr (RawMap.id_laws _) (fun h => h) (equalityCongr _)
    preservesCoproducts FunctionCategory.coproductCongr

theorem coproductLaws : CoproductLaws ops.{u} (equality _) coproducts :=
  CoproductMap.transportLaws (RawMap.id_laws _) (fun h => h) (equalityCongr _)
    FunctionCategory.laws coproductInverse preservesCoproducts
    FunctionCategory.coproductCongr FunctionCategory.coproductLaws

theorem preservesDistribution : DistributionMapLaws (equality ops.{u}) productComparison
    coproductComparison distribution FunctionCategory.distribution where
  distribute := by
    intro a b c
    funext x
    rcases x with ⟨x, ⟨y | y⟩⟩ <;> rfl

theorem distributionLaws : DistributionLaws ops.{u} (equality _) products coproducts distribution :=
  DistributionMap.transportLaws (equalityCongr _) FunctionCategory.laws
    FunctionCategory.productCongr FunctionCategory.productLaws
    FunctionCategory.coproductCongr FunctionCategory.coproductLaws
    (RawMap.id_laws _) (fun h => h) preservesProducts preservesCoproducts
    productInverse coproductInverse preservesDistribution FunctionCategory.distributionLaws

def wrapCoproducts : CoproductMap interpretation FunctionCategory.coproducts coproducts :=
  fun _ _ => ⟨Box.mk, Box.value⟩
theorem wrapCoproductInverse (a b : Type u) :
    ComparisonLaws (equality _) (wrapCoproducts a b) := ⟨rfl, rfl⟩
theorem wrapPreservesCoproducts : CoproductMapLaws (equality _) wrapCoproducts where
  inl := rfl
  inr := rfl
  copair _ _ := rfl

/-- A selected right branch survives both changes of carrier. -/
example (x z : Nat) : distribution.distribute (a := Nat) (b := Bool) (c := Nat)
    ⟨(x, ⟨.inr z⟩)⟩ = ⟨.inr ⟨(x, z)⟩⟩ := rfl

example (x : Box (Nat × Box (Sum Bool Nat))) :
    collect ops products coproducts (distribution.distribute x) = x :=
  congrFun (distributionLaws.collect_distribute _ _ _) x

example {a b c : Type u} (f : Box (Sum a b) → c) :
    coproducts.copair (fun x => f ⟨.inl x⟩) (fun y => f ⟨.inr y⟩) = f :=
  coproductLaws.eta f
end Wrapped
open CategoricalCompiler
variable {Prim : Ty → Ty → Type} {B : Type}
variable (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)

def composed := (CodeCategory.evaluation meaning).comp Wrapped.interpretation
def composedProducts := (CodeCategory.productComparison meaning).comp Wrapped.wrapProducts
def composedCoproducts := (CodeCategory.coproductComparison meaning).comp Wrapped.wrapCoproducts

theorem composedMapLaws : MapLaws (composed meaning) (CodeCategory.equiv meaning) (equality _) :=
  RawMap.comp_laws (CodeCategory.evaluationLaws meaning) (RawMap.id_laws _)

theorem composedProductInverse (a b : Ty) :
    ComparisonLaws (equality _) (composedProducts meaning a b) :=
  Comparison.comp_laws (equalityCongr _) FunctionCategory.laws
    (Comparison.map_laws (RawMap.id_laws _) (CodeCategory.productComparisonLaws meaning a b))
    (Wrapped.wrapProductInverse _ _)

theorem composedCoproductInverse (a b : Ty) :
    ComparisonLaws (equality _) (composedCoproducts meaning a b) :=
  CoproductMap.comp_inverse (RawMap.id_laws _) (equalityCongr _) FunctionCategory.laws
    (CodeCategory.coproductComparisonLaws meaning) Wrapped.wrapCoproductInverse a b

theorem composedPreservesProducts : ProductMapLaws (equality _) (composedProducts meaning) :=
  ProductMap.comp_laws (RawMap.id_laws _) (equalityCongr _) FunctionCategory.laws
    (CodeCategory.evaluationProducts meaning) Wrapped.wrapPreservesProducts

theorem composedPreservesCoproducts : CoproductMapLaws (equality _) (composedCoproducts meaning) :=
  CoproductMap.comp_laws (RawMap.id_laws _) (equalityCongr _) FunctionCategory.laws
    (CodeCategory.evaluationCoproducts meaning) Wrapped.wrapPreservesCoproducts

/-- Composition needs no new distribution equation once both chosen inverses
are lawful: uniqueness derives it from the composed structural preservation. -/
theorem composedPreservesDistribution : DistributionMapLaws (equality _)
    (composedProducts meaning) (composedCoproducts meaning)
    (CodeCategory.distribution Prim) Wrapped.distribution :=
  DistributionMap.of_laws (equalityCongr _) FunctionCategory.laws
    Wrapped.productCongr Wrapped.productLaws Wrapped.coproductCongr Wrapped.coproductLaws
    (composedMapLaws meaning) (composedPreservesProducts meaning) (composedPreservesCoproducts meaning)
    (composedProductInverse meaning) (composedCoproductInverse meaning)
    (CodeCategory.distributionLaws meaning).distribute_collect Wrapped.distributionLaws.collect_distribute

/-- The separately chosen source relation is retained after two interpretations. -/
theorem composedDistributionLaws : DistributionLaws (CodeCategory.ops Prim)
    (CodeCategory.equiv meaning) (CodeCategory.products Prim) (CodeCategory.coproducts Prim)
    (CodeCategory.distribution Prim) :=
  DistributionMap.transportLaws (equalityCongr _) FunctionCategory.laws
    Wrapped.productCongr Wrapped.productLaws Wrapped.coproductCongr Wrapped.coproductLaws
    (composedMapLaws meaning) (CodeCategory.evaluationReflects meaning)
    (composedPreservesProducts meaning) (composedPreservesCoproducts meaning)
    (composedProductInverse meaning) (composedCoproductInverse meaning)
    (composedPreservesDistribution meaning) Wrapped.distributionLaws

example : CoproductMapLaws (equality FunctionCategory.ops)
    (CoproductMap.id Wrapped.coproducts) := CoproductMap.id_laws FunctionCategory.laws _

example : DistributionMapLaws (equality FunctionCategory.ops)
    (ProductMap.id Wrapped.products) (CoproductMap.id Wrapped.coproducts)
    Wrapped.distribution Wrapped.distribution :=
  DistributionMap.id_laws (equalityCongr _) FunctionCategory.laws
    Wrapped.productCongr Wrapped.productLaws Wrapped.coproductCongr Wrapped.coproductLaws _

/-- Arbitrary code arrows recover coproduct eta through shared law transport. -/
example {a b c : Ty} (f : Code Prim (.sum a b) c) :
    Equivalent meaning (.copair (.comp f .inl) (.comp f .inr)) f :=
  (CodeCategory.coproductLaws meaning).eta f

/-- Evaluation induces laws without being injective on raw code. -/
example : CoproductLaws (CodeCategory.ops Prim)
    ((CodeCategory.evaluation meaning).induced (equality _)) (CodeCategory.coproducts Prim) :=
  CoproductMap.transportLaws
    ((CodeCategory.evaluation meaning).inducedLaws (equality _) rfl (fun _ _ => rfl))
    ((CodeCategory.evaluation meaning).induced_reflects _)
    (equalityCongr _) FunctionCategory.laws (CodeCategory.coproductComparisonLaws meaning)
    (CodeCategory.evaluationCoproducts meaning) FunctionCategory.coproductCongr
    FunctionCategory.coproductLaws

/-- Evaluation cannot reflect the stronger relation of raw constructor equality. -/
example : ¬ (CodeCategory.evaluation meaning).Reflects (equality _) (equality _) := by
  intro h
  have bad := h (f := (Code.comp .ident .ident : Code Prim .base .base))
    (g := .ident) (by rfl)
  cases bad

end Examples.OptionalTransport
