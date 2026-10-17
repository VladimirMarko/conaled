import SquareKit.CartesianMap
import SquareKit.FunctionCategory
import SquareKit.FirstOrderCategory
import Applications.Linear.Compiler

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace MatrixCompiler.Maps
open SquareKit FirstOrderCompiler MatrixCompiler
variable (R : Type) [CommSemiring R]

def matrices : CategoryOps Ty := FirstOrderCategory.ops (target R)
def matrixTerminal : TerminalOps (matrices R) := FirstOrderCategory.terminal (target R)
def matrixProducts : ProductOps (matrices R) := FirstOrderCategory.products (target R)

def coordinates : CategoryOps Ty where
  Hom a b := (Slots a → R) → (Slots b → R)
  ident := id
  comp g f := g ∘ f

def coordinateTerminal : TerminalOps (coordinates R) where
  unit := .unit
  terminal := fun _ e => nomatch e

def coordinateProducts : ProductOps (coordinates R) where
  prod := .prod
  fst x i := x (.inl i)
  snd x j := x (.inr j)
  pair f g x := Sum.elim (f x) (g x)

def evaluate : RawMap (matrices R) (coordinates R) where
  obj := id
  map := Matrix.mulVec

def coordinateFunctions : RawMap (coordinates R) FunctionCategory.ops where
  obj a := Slots a → R
  map f := f

def values : RawMap (coordinates R) FunctionCategory.ops where
  obj := Val R
  map {a b} f x := decode b (f (encode a x))

omit [CommSemiring R] in
theorem coordinateFunctions_laws :
    MapLaws (coordinateFunctions R) (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := rfl
  comp _ _ := rfl

theorem evaluate_laws : MapLaws (evaluate R) (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := by intro a; change (fun x => (1 : Code R a a).mulVec x) = id; funext x; exact Matrix.one_mulVec x
  comp g f := by
    dsimp [matrices, FirstOrderCategory.ops, target] at g f
    change (fun x => (g * f).mulVec x) = fun x => g.mulVec (f.mulVec x)
    funext x; exact (Matrix.mulVec_mulVec _ _ _).symm

omit [CommSemiring R] in
theorem values_laws : MapLaws (values R) (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := by intro a; funext x; exact decode_encode _ x
  comp g f := by
    change (fun x => decode _ (g (f (encode _ x)))) =
      fun x => decode _ (g (encode _ (decode _ (f (encode _ x)))))
    funext x; rw [encode_decode]

def coordinateFunctionTerminal : TerminalMap (coordinateFunctions R)
    (coordinateTerminal R) FunctionCategory.terminal where
  hom _ := PUnit.unit
  inv _ e := nomatch e

def coordinateFunctionProducts : ProductMap (coordinateFunctions R)
    (coordinateProducts R) FunctionCategory.products := fun _ _ => {
  hom := fun x => (fun i => x (.inl i), fun j => x (.inr j))
  inv := fun x => Sum.elim x.1 x.2 }

omit [CommSemiring R] in
theorem coordinateFunctionTerminal_inverse :
    ComparisonLaws (equality _) (coordinateFunctionTerminal R) where
  hom_inv := by funext x; cases x; rfl
  inv_hom := by funext x e; exact nomatch e

omit [CommSemiring R] in
theorem coordinateFunctionProducts_inverse (a b : Ty) :
    ComparisonLaws (equality _) (coordinateFunctionProducts R a b) where
  hom_inv := rfl
  inv_hom := by funext x i; cases i <;> rfl

omit [CommSemiring R] in
theorem coordinateFunctionTerminal_laws :
    TerminalMapLaws (equality _) (coordinateFunctionTerminal R) where
  terminal := by intro a; funext x e; exact nomatch e

omit [CommSemiring R] in
theorem coordinateFunctionProducts_laws :
    ProductMapLaws (equality _) (coordinateFunctionProducts R) where
  fst := rfl
  snd := rfl
  pair _ _ := rfl

omit [CommSemiring R] in
theorem coordinateLaws : CategoryLaws (coordinates R) (equality _) :=
  RawMap.transportLaws (coordinateFunctions_laws R) (fun h => h)
    (equalityCongr _) FunctionCategory.laws

omit [CommSemiring R] in
theorem coordinateTerminalLaws : TerminalLaws (equality _) (coordinateTerminal R) :=
  TerminalMap.transportLaws (fun h => h) (equalityCongr _) FunctionCategory.laws
    (coordinateFunctionTerminal_inverse R) (coordinateFunctionTerminal_laws R)
    FunctionCategory.terminalLaws

omit [CommSemiring R] in
theorem coordinateProductCongr : ProductCongr (equality _) (coordinateProducts R) :=
  ProductMap.transportCongr (coordinateFunctions_laws R) (fun h => h) (equalityCongr _)
    (coordinateFunctionProducts_laws R) FunctionCategory.productCongr

omit [CommSemiring R] in
theorem coordinateProductLaws : ProductLaws (equality _) (coordinateProducts R) :=
  ProductMap.transportLaws (coordinateFunctions_laws R) (fun h => h) (equalityCongr _)
    FunctionCategory.laws (coordinateFunctionProducts_inverse R)
    (coordinateFunctionProducts_laws R) FunctionCategory.productCongr FunctionCategory.productLaws

def evaluateTerminal : TerminalMap (evaluate R) (matrixTerminal R) (coordinateTerminal R) :=
  Comparison.id _ _

def evaluateProducts : ProductMap (evaluate R) (matrixProducts R) (coordinateProducts R) :=
  fun _ _ => Comparison.id _ _

theorem evaluateTerminal_laws : TerminalMapLaws (equality _) (evaluateTerminal R) where
  terminal := by intro a; funext x e; exact nomatch e

theorem evaluateProducts_laws : ProductMapLaws (equality _) (evaluateProducts R) where
  fst := by intro a b; funext x; exact first_mulVec R _ _ x
  snd := by intro a b; funext x; exact second_mulVec R _ _ x
  pair f g := by funext x i; cases i <;> rfl

def valueTerminal : TerminalMap (values R) (coordinateTerminal R) FunctionCategory.terminal where
  hom _ := PUnit.unit
  inv _ := ()

def valueProducts : ProductMap (values R) (coordinateProducts R) FunctionCategory.products :=
  fun _ _ => Comparison.id _ _

omit [CommSemiring R] in
theorem valueTerminal_inverse : ComparisonLaws (equality _) (valueTerminal R) where
  hom_inv := by funext x; cases x; rfl
  inv_hom := by funext x; cases x; rfl

omit [CommSemiring R] in
theorem valueProducts_inverse (a b : Ty) : ComparisonLaws (equality _) (valueProducts R a b) :=
  Comparison.id_laws FunctionCategory.laws _

omit [CommSemiring R] in
theorem valueTerminal_laws : TerminalMapLaws (equality _) (valueTerminal R) where
  terminal := rfl

omit [CommSemiring R] in
theorem valueProducts_laws : ProductMapLaws (equality _) (valueProducts R) where
  fst := by intro a b; funext x; exact decode_encode _ x.1
  snd := by intro a b; funext x; exact decode_encode _ x.2
  pair _ _ := rfl

/-- Matrix action with the sum-coordinate/product-function comparison. -/
def matrixFunctions : RawMap (matrices R) FunctionCategory.ops :=
  (evaluate R).comp (coordinateFunctions R)

def matrixFunctionProducts : ProductMap (matrixFunctions R) (matrixProducts R) FunctionCategory.products :=
  ProductMap.comp (evaluateProducts R) (coordinateFunctionProducts R)

theorem matrixFunctions_laws : MapLaws (matrixFunctions R) (equality _) (equality _) :=
  RawMap.comp_laws (evaluate_laws R) (coordinateFunctions_laws R)

theorem matrixFunctionProducts_laws : ProductMapLaws (equality _) (matrixFunctionProducts R) :=
  ProductMap.comp_laws (coordinateFunctions_laws R) (equalityCongr _) FunctionCategory.laws
    (evaluateProducts_laws R) (coordinateFunctionProducts_laws R)

theorem matrixFunctionProducts_inverse (a b : Ty) :
    ComparisonLaws (equality _) (matrixFunctionProducts R a b) :=
  Comparison.comp_laws (equalityCongr _) FunctionCategory.laws
    (Comparison.map_laws (coordinateFunctions_laws R) (Comparison.id_laws (coordinateLaws R) _))
    (coordinateFunctionProducts_inverse R a b)

/-- The nested-value interpretation factors through the same coordinate action. -/
def matrixValues : RawMap (matrices R) FunctionCategory.ops := (evaluate R).comp (values R)

theorem matrixValues_laws : MapLaws (matrixValues R) (equality _) (equality _) :=
  RawMap.comp_laws (evaluate_laws R) (values_laws R)

def matrixValueProducts : ProductMap (matrixValues R) (matrixProducts R) FunctionCategory.products :=
  ProductMap.comp (evaluateProducts R) (valueProducts R)

theorem matrixValueProducts_laws : ProductMapLaws (equality _) (matrixValueProducts R) :=
  ProductMap.comp_laws (values_laws R) (equalityCongr _) FunctionCategory.laws
    (evaluateProducts_laws R) (valueProducts_laws R)

theorem matrixValues_denote {a b : Ty} (M : Code R a b) (x : Val R a) :
    (matrixValues R).map M x = denote R M x := rfl

theorem interpretation_commutes {a b : Ty} (M : Code R a b) (x : Slots a → R) :
    decode b ((matrixFunctions R).map M x) = (matrixValues R).map M (decode a x) := by
  change decode b (M.mulVec x) = decode b (M.mulVec (encode a (decode a x)))
  rw [encode_decode]

/-- The generic transport recovers product laws for arbitrary matrices modulo action. -/
theorem matrixProductLaws :
    ProductLaws ((matrixFunctions R).induced (equality _)) (matrixProducts R) := by
  let L : MapLaws (matrixFunctions R) ((matrixFunctions R).induced (equality _)) (equality _) := {
    congr := fun h => h
    ident := (matrixFunctions_laws R).ident
    comp := (matrixFunctions_laws R).comp }
  exact ProductMap.transportLaws L ((matrixFunctions R).induced_reflects _) (equalityCongr _)
    FunctionCategory.laws (matrixFunctionProducts_inverse R)
    (matrixFunctionProducts_laws R) FunctionCategory.productCongr FunctionCategory.productLaws

def matrixFunctionTerminal : TerminalMap (matrixFunctions R) (matrixTerminal R) FunctionCategory.terminal :=
  TerminalMap.comp (evaluateTerminal R) (coordinateFunctionTerminal R)

theorem matrixFunctionTerminal_laws : TerminalMapLaws (equality _) (matrixFunctionTerminal R) :=
  TerminalMap.comp_laws (coordinateFunctions_laws R) (equalityCongr _) FunctionCategory.laws
    (evaluateTerminal_laws R) (coordinateFunctionTerminal_laws R)

theorem matrixFunctionTerminal_inverse : ComparisonLaws (equality _) (matrixFunctionTerminal R) :=
  Comparison.comp_laws (equalityCongr _) FunctionCategory.laws
    (Comparison.map_laws (coordinateFunctions_laws R) (Comparison.id_laws (coordinateLaws R) _))
    (coordinateFunctionTerminal_inverse R)

theorem matrixTerminalLaws :
    TerminalLaws ((matrixFunctions R).induced (equality _)) (matrixTerminal R) :=
  TerminalMap.transportLaws ((matrixFunctions R).induced_reflects _) (equalityCongr _)
    FunctionCategory.laws (matrixFunctionTerminal_inverse R)
    (matrixFunctionTerminal_laws R) FunctionCategory.terminalLaws

theorem matrixValueProducts_inverse (a b : Ty) :
    ComparisonLaws (equality _) (matrixValueProducts R a b) :=
  Comparison.comp_laws (equalityCongr _) FunctionCategory.laws
    (Comparison.map_laws (values_laws R) (Comparison.id_laws (coordinateLaws R) _))
    (valueProducts_inverse R a b)

/-- This comparison changes a sum-indexed coordinate vector into two vectors. -/
theorem matrix_product_comparison {a b : Ty} (x : Slots (.prod a b) → R) :
    (matrixFunctionProducts R a b).hom x =
      ((fun i => x (.inl i)), (fun j => x (.inr j))) := rfl

/-- Composition runs the right matrix first in both interpretations. -/
theorem composed_matrix_action {a b c : Ty} (M : Code R b c) (N : Code R a b)
    (x : Slots a → R) :
    (matrixFunctions R).map (M * N) x =
      (matrixFunctions R).map M ((matrixFunctions R).map N x) :=
  congrFun ((matrixFunctions_laws R).comp M N) x

end MatrixCompiler.Maps
