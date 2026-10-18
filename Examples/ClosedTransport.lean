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

theorem productInverse (a b : Type u) :
    ComparisonLaws (equality _) (productComparison a b) := ⟨rfl, rfl⟩
theorem closedInverse (a b : Type u) :
    ComparisonLaws (equality _) (closedComparison a b) := ⟨rfl, rfl⟩
theorem preservesProducts : ProductMapLaws (equality _) productComparison where
  fst := rfl
  snd := rfl
  pair _ _ := rfl
theorem preservesClosed : ClosedMapLaws (equality _) productComparison closedComparison where
  curry _ := rfl
  evaluation := rfl

theorem reflects : interpretation.{u}.Reflects (equality _) (equality _) := fun h => h

theorem productCongr : ProductCongr (equality ops.{u}) products :=
  ProductMap.transportCongr (RawMap.id_laws _) reflects (equalityCongr _)
    preservesProducts FunctionCategory.productCongr

theorem productLaws : ProductLaws (equality ops.{u}) products :=
  ProductMap.transportLaws (RawMap.id_laws _) reflects (equalityCongr _) FunctionCategory.laws
    productInverse preservesProducts FunctionCategory.productCongr FunctionCategory.productLaws

theorem closedCongr : ClosedCongr (equality ops.{u}) products closed :=
  ClosedMap.transportCongr (RawMap.id_laws _) reflects (equalityCongr _)
    FunctionCategory.closedCongr preservesClosed

theorem closedLaws : ClosedLaws (equality ops.{u}) products closed :=
  ClosedMap.transportLaws (RawMap.id_laws _) reflects (equalityCongr _) FunctionCategory.laws
    FunctionCategory.productCongr FunctionCategory.productLaws
    FunctionCategory.closedCongr FunctionCategory.closedLaws
    productInverse closedInverse preservesProducts preservesClosed

/-- The reverse interpretation will follow raw-code evaluation in the composition. -/
def wrapProducts : ProductMap interpretation FunctionCategory.products products :=
  fun _ _ => ⟨Box.mk, Box.value⟩
def wrapClosed : ClosedMap interpretation FunctionCategory.closed closed :=
  fun _ _ => ⟨Box.mk, Box.value⟩
theorem wrapProductInverse (a b : Type u) :
    ComparisonLaws (equality _) (wrapProducts a b) := ⟨rfl, rfl⟩
theorem wrapClosedInverse (a b : Type u) :
    ComparisonLaws (equality _) (wrapClosed a b) := ⟨rfl, rfl⟩
theorem wrapPreservesProducts : ProductMapLaws (equality _) wrapProducts where
  fst := rfl
  snd := rfl
  pair _ _ := rfl
theorem wrapPreservesClosed : ClosedMapLaws (equality _) wrapProducts wrapClosed where
  curry _ := rfl
  evaluation := rfl

/-- A captured offset exercises both Box comparisons and the generic beta theorem. -/
theorem captured_offset (x a : Nat) :
    closed.uncurry (closed.curry (fun p : Box (Nat × Nat) => p.value.1 + p.value.2))
      ⟨(x, a)⟩ = x + a :=
  congrFun (closedLaws.beta (fun p : Box (Nat × Nat) => p.value.1 + p.value.2)) ⟨(x, a)⟩

/-- Identity preservation is checked for the wrapped operations as well. -/
example : ClosedMapLaws (equality ops.{u}) (ProductMap.id products) (ClosedMap.id closed) :=
  ClosedMap.id_laws (equalityCongr _) FunctionCategory.laws productCongr productLaws closedCongr
end Wrapped

open CategoricalCompiler
variable {Prim : Ty → Ty → Type} {B : Type}
variable (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)

def composed := (CodeCategory.evaluation meaning).comp Wrapped.interpretation

def composedProducts := (CodeCategory.productComparison meaning).comp Wrapped.wrapProducts
def composedClosed := (CodeCategory.closedComparison meaning).comp Wrapped.wrapClosed

theorem composedMapLaws : MapLaws (composed meaning)
    ((composed meaning).induced (equality _)) (equality _) :=
  RawMap.comp_laws
    ((CodeCategory.evaluation meaning).inducedLaws (equality _) rfl (fun _ _ => rfl))
    (RawMap.id_laws _)

theorem composedProductInverse (a b : Ty) :
    ComparisonLaws (equality _) (composedProducts meaning a b) :=
  Comparison.comp_laws (equalityCongr _) FunctionCategory.laws
    (Comparison.map_laws (RawMap.id_laws _) (CodeCategory.productComparisonLaws meaning a b))
    (Wrapped.wrapProductInverse _ _)

theorem composedClosedInverse (a b : Ty) :
    ComparisonLaws (equality _) (composedClosed meaning a b) :=
  ClosedMap.comp_inverse (RawMap.id_laws _) (equalityCongr _) FunctionCategory.laws
    (CodeCategory.closedComparisonLaws meaning) Wrapped.wrapClosedInverse a b

theorem composedPreservesProducts : ProductMapLaws (equality _) (composedProducts meaning) :=
  ProductMap.comp_laws (RawMap.id_laws _) (equalityCongr _) FunctionCategory.laws
    (CodeCategory.evaluationProducts meaning) Wrapped.wrapPreservesProducts

theorem composedPreservesClosed : ClosedMapLaws (equality _)
    (composedProducts meaning) (composedClosed meaning) :=
  ClosedMap.comp_laws (RawMap.id_laws _) (equalityCongr _) FunctionCategory.laws
    Wrapped.productCongr Wrapped.productLaws Wrapped.closedCongr
    Wrapped.wrapProductInverse Wrapped.wrapPreservesProducts
    (CodeCategory.evaluationClosed meaning) Wrapped.wrapPreservesClosed

/-- All source laws follow after composition, under the induced relation. -/
theorem composedClosedLaws : ClosedLaws ((composed meaning).induced (equality _))
    (CodeCategory.products Prim) (CodeCategory.closed Prim) :=
  ClosedMap.transportLaws (composedMapLaws meaning) ((composed meaning).induced_reflects _)
    (equalityCongr _) FunctionCategory.laws Wrapped.productCongr Wrapped.productLaws
    Wrapped.closedCongr Wrapped.closedLaws (composedProductInverse meaning)
    (composedClosedInverse meaning) (composedPreservesProducts meaning) (composedPreservesClosed meaning)

/-- Distinct syntax trees satisfy eta after the composed interpretation. -/
theorem raw_eta {a b c : Ty} (f : Code Prim a (.arr b c)) :
    ((composed meaning).induced (equality _)).Rel
      (.curry (.comp .apply (.pair (.comp f .fst) .snd))) f :=
  (composedClosedLaws meaning).eta f

theorem raw_beta {x a b : Ty} (f : Code Prim (.prod x a) b) :
    Equivalent meaning (.comp .apply (.pair (.comp (.curry f) .fst) .snd)) f :=
  (CodeCategory.closedLaws meaning).beta f

theorem raw_natural {x y a b : Ty} (f : Code Prim (.prod x a) b) (g : Code Prim y x) :
    Equivalent meaning (.curry (.comp f (.pair (.comp g .fst) .snd))) (.comp (.curry f) g) :=
  (CodeCategory.closedLaws meaning).natural f g
end Examples.ClosedTransport
