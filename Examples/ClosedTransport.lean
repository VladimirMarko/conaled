import SquareKit.CodeCategory

/-! Closed transport for raw code and genuinely different product/exponential
presentations. The composed interpretation checks reuse of preservation proofs. -/
namespace Examples.ClosedTransport
open SquareKit
universe u

structure Box (α : Type u) where
  value : α

namespace Wrapped
open FunctionCategory

def products : ProductOps ops.{u} where
  prod a b := Box (a × b)
  fst p := p.value.1
  snd p := p.value.2
  pair f g x := ⟨(f x, g x)⟩

def closed : ClosedOps ops.{u} products where
  exp a b := Box (a → b)
  evaluation p := p.value.1.value p.value.2
  curry f x := ⟨fun a => f ⟨(x, a)⟩⟩

/-- Objects stay fixed, while chosen products and exponentials change carrier. -/
abbrev interpretation : RawMap ops.{u} ops.{u} := RawMap.id ops

def productComparison : ProductMap interpretation products FunctionCategory.products :=
  fun _ _ => ⟨Box.value, Box.mk⟩
def closedComparison : ClosedMap interpretation closed FunctionCategory.closed :=
  fun _ _ => ⟨Box.value, Box.mk⟩

theorem productComparison_laws (a b : Type u) :
    ComparisonLaws (equality _) (productComparison a b) := ⟨rfl, rfl⟩
theorem closedComparison_laws (a b : Type u) :
    ComparisonLaws (equality _) (closedComparison a b) := ⟨rfl, rfl⟩
theorem interpretation_preserves_products : ProductMapLaws (equality _) productComparison where
  fst := rfl
  snd := rfl
  pair _ _ := rfl
theorem interpretation_preserves_closed : ClosedMapLaws (equality _) productComparison closedComparison where
  curry _ := rfl
  evaluation := rfl

theorem interpretation_reflects : interpretation.{u}.Reflects (equality _) (equality _) := fun h => h

theorem products_congr : ProductCongr (equality ops.{u}) products :=
  ProductMap.transport_congr (RawMap.id_laws _) interpretation_reflects (equality_congr _)
    interpretation_preserves_products FunctionCategory.productCongr

theorem products_laws : ProductLaws (equality ops.{u}) products :=
  ProductMap.transport_laws (RawMap.id_laws _) interpretation_reflects (equality_congr _) FunctionCategory.laws
    productComparison_laws interpretation_preserves_products FunctionCategory.productCongr FunctionCategory.productLaws

theorem closed_congr : ClosedCongr (equality ops.{u}) products closed :=
  ClosedMap.transport_congr (RawMap.id_laws _) interpretation_reflects (equality_congr _)
    FunctionCategory.closedCongr interpretation_preserves_closed

theorem closed_laws : ClosedLaws (equality ops.{u}) products closed :=
  ClosedMap.transport_laws (RawMap.id_laws _) interpretation_reflects (equality_congr _) FunctionCategory.laws
    FunctionCategory.productCongr FunctionCategory.productLaws
    FunctionCategory.closedCongr FunctionCategory.closedLaws
    productComparison_laws closedComparison_laws interpretation_preserves_products interpretation_preserves_closed

/-- The reverse interpretation will follow raw-code evaluation in the composition. -/
def wrapProducts : ProductMap interpretation FunctionCategory.products products :=
  fun _ _ => ⟨Box.mk, Box.value⟩
def wrapClosed : ClosedMap interpretation FunctionCategory.closed closed :=
  fun _ _ => ⟨Box.mk, Box.value⟩
theorem wrapProducts_laws (a b : Type u) :
    ComparisonLaws (equality _) (wrapProducts a b) := ⟨rfl, rfl⟩
theorem wrapClosed_laws (a b : Type u) :
    ComparisonLaws (equality _) (wrapClosed a b) := ⟨rfl, rfl⟩
theorem wrapProducts_preserves_products : ProductMapLaws (equality _) wrapProducts where
  fst := rfl
  snd := rfl
  pair _ _ := rfl
theorem wrapClosed_preserves_closed : ClosedMapLaws (equality _) wrapProducts wrapClosed where
  curry _ := rfl
  evaluation := rfl

/-- A captured offset exercises both Box comparisons and the generic beta theorem. -/
theorem captured_offset (x a : Nat) :
    closed.uncurry (closed.curry (fun p : Box (Nat × Nat) => p.value.1 + p.value.2))
      ⟨(x, a)⟩ = x + a :=
  congrFun (closed_laws.beta (fun p : Box (Nat × Nat) => p.value.1 + p.value.2)) ⟨(x, a)⟩

/-- Identity preservation is checked for the wrapped operations as well. -/
example : ClosedMapLaws (equality ops.{u}) (ProductMap.id products) (ClosedMap.id closed) :=
  ClosedMap.id_laws (equality_congr _) FunctionCategory.laws products_congr products_laws closed_congr
end Wrapped

open CategoricalCompiler
variable {Prim : Ty → Ty → Type} {B : Type}
variable (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)

def composedInterpretation := (CodeCategory.evaluation meaning).comp Wrapped.interpretation

def composedProductComparison := (CodeCategory.productComparison meaning).comp Wrapped.wrapProducts
def composedClosedComparison := (CodeCategory.closedComparison meaning).comp Wrapped.wrapClosed

theorem composedInterpretation_laws : MapLaws (composedInterpretation meaning)
    ((composedInterpretation meaning).induced (equality _)) (equality _) :=
  RawMap.comp_laws
    ((CodeCategory.evaluation meaning).induced_laws (equality _) rfl (fun _ _ => rfl))
    (RawMap.id_laws _)

theorem composedProductComparison_laws (a b : Ty) :
    ComparisonLaws (equality _) (composedProductComparison meaning a b) :=
  Comparison.comp_laws (equality_congr _) FunctionCategory.laws
    (Comparison.map_laws (RawMap.id_laws _) (CodeCategory.productComparison_laws meaning a b))
    (Wrapped.wrapProducts_laws _ _)

theorem composedClosedComparison_laws (a b : Ty) :
    ComparisonLaws (equality _) (composedClosedComparison meaning a b) :=
  ClosedMap.comp_inverse (RawMap.id_laws _) (equality_congr _) FunctionCategory.laws
    (CodeCategory.closedComparison_laws meaning) Wrapped.wrapClosed_laws a b

theorem composedInterpretation_preserves_products : ProductMapLaws (equality _) (composedProductComparison meaning) :=
  ProductMap.comp_laws (RawMap.id_laws _) (equality_congr _) FunctionCategory.laws
    (CodeCategory.evaluation_preserves_products meaning) Wrapped.wrapProducts_preserves_products

theorem composedInterpretation_preserves_closed : ClosedMapLaws (equality _)
    (composedProductComparison meaning) (composedClosedComparison meaning) :=
  ClosedMap.comp_laws (RawMap.id_laws _) (equality_congr _) FunctionCategory.laws
    Wrapped.products_congr Wrapped.products_laws Wrapped.closed_congr
    Wrapped.wrapProducts_laws Wrapped.wrapProducts_preserves_products
    (CodeCategory.evaluation_preserves_closed meaning) Wrapped.wrapClosed_preserves_closed

/-- All source laws follow after composition, under the induced relation. -/
theorem composedInterpretation_closed_laws : ClosedLaws ((composedInterpretation meaning).induced (equality _))
    (CodeCategory.products Prim) (CodeCategory.closed Prim) :=
  ClosedMap.transport_laws (composedInterpretation_laws meaning) ((composedInterpretation meaning).induced_reflects _)
    (equality_congr _) FunctionCategory.laws Wrapped.products_congr Wrapped.products_laws
    Wrapped.closed_congr Wrapped.closed_laws (composedProductComparison_laws meaning)
    (composedClosedComparison_laws meaning) (composedInterpretation_preserves_products meaning) (composedInterpretation_preserves_closed meaning)

/-- Distinct syntax trees satisfy eta after the composed interpretation. -/
theorem raw_eta {a b c : Ty} (f : Code Prim a (.arr b c)) :
    ((composedInterpretation meaning).induced (equality _)).Rel
      (.curry (.comp .apply (.pair (.comp f .fst) .snd))) f :=
  (composedInterpretation_closed_laws meaning).eta f

theorem raw_beta {x a b : Ty} (f : Code Prim (.prod x a) b) :
    Equivalent meaning (.comp .apply (.pair (.comp (.curry f) .fst) .snd)) f :=
  (CodeCategory.closed_laws meaning).beta f

theorem raw_natural {x y a b : Ty} (f : Code Prim (.prod x a) b) (g : Code Prim y x) :
    Equivalent meaning (.curry (.comp f (.pair (.comp g .fst) .snd))) (.comp (.curry f) g) :=
  (CodeCategory.closed_laws meaning).natural f g
end Examples.ClosedTransport
