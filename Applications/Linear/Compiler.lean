import Applications.Linear.Maps
import SquareKit.FirstOrderNaturality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace MatrixCompiler
open SquareKit FirstOrderCompiler
variable (R : Type) [CommSemiring R]

/-- Structural soundness is inherited from the composed coordinate interpretation. -/
def sound : Sound R (target R) (meaning R) where
  denote := (Maps.matrixValues R).map
  ident x := congrFun (Maps.matrixValues_laws R).ident x
  comp g f x := congrFun ((Maps.matrixValues_laws R).comp g f) x
  terminal _ := rfl
  fst x := by
    have h := congrFun (Maps.matrixValueProducts_laws R).fst x
    simpa [Maps.matrixValueProducts, ProductMap.comp, Comparison.comp,
      Maps.evaluateProducts, Maps.valueProducts, Comparison.id, Maps.values,
      FunctionCategory.ops, FunctionCategory.products, Comparison.map, Maps.coordinates,
      Maps.evaluate, Maps.matrixProducts, FirstOrderCategory.products, Maps.coordinateProducts,
      decode_encode] using h
  snd x := by
    have h := congrFun (Maps.matrixValueProducts_laws R).snd x
    simpa [Maps.matrixValueProducts, ProductMap.comp, Comparison.comp,
      Maps.evaluateProducts, Maps.valueProducts, Comparison.id, Maps.values,
      FunctionCategory.ops, FunctionCategory.products, Comparison.map, Maps.coordinates,
      Maps.evaluate, Maps.matrixProducts, FirstOrderCategory.products, Maps.coordinateProducts,
      decode_encode] using h
  pair f g x := by
    have h := congrFun ((Maps.matrixValueProducts_laws R).pair f g) x
    simpa [Maps.matrixValueProducts, ProductMap.comp, Comparison.comp,
      Maps.evaluateProducts, Maps.valueProducts, Comparison.id, Maps.values,
      FunctionCategory.ops, FunctionCategory.products, Comparison.map, Maps.coordinates,
      Maps.evaluate, Maps.matrixProducts, FirstOrderCategory.products, Maps.coordinateProducts,
      decode_encode] using h
  primitive := denote_primitive R

theorem denote_id (a : Ty) (x : Val R a) : denote R (1 : Code R a a) x = x :=
  (sound R).ident x

theorem denote_comp {a b c : Ty} (M : Code R b c) (N : Code R a b) (x : Val R a) :
    denote R (M * N) x = denote R M (denote R N x) :=
  (sound R).comp M N x

theorem denote_first (a b : Ty) (x : Val R (.prod a b)) : denote R (first R a b) x = x.1 :=
  (sound R).fst x

theorem denote_second (a b : Ty) (x : Val R (.prod a b)) : denote R (second R a b) x = x.2 :=
  (sound R).snd x

theorem denote_pair {a b c : Ty} (M : Code R a b) (N : Code R a c) (x : Val R a) :
    denote R (pair R M N) x = (denote R M x, denote R N x) :=
  (sound R).pair M N x

theorem compile_correct (t : Term (Prim R) Γ a) (ρ : Val R (context Γ)) :
    denote R (compile (target R) t) ρ = eval (meaning R) t ρ :=
  FirstOrderNaturality.compile_sound (target R) (sound R) t ρ

def valueRep (a : Ty) : Squares.Rep := ⟨Slots a → R, Val R a, decode a⟩

def compileSquare (t : Term (Prim R) Γ a) :
    Squares.Square (valueRep R (context Γ)) (valueRep R a) where
  impl := (compile (target R) t).mulVec
  spec := eval (meaning R) t
  commutes x := (Maps.interpretation_commutes R _ x).trans
    (compile_correct R t (decode _ x))

def linearCombination : Term (Prim R) [.prod .base .base] .base :=
  .prim .add (.pair (.prim (.scale 2) (.fst (.var .here)))
    (.prim (.scale 3) (.snd (.var .here))))

theorem two_x_three_y (x y : R) :
    denote R (compile (target R) (linearCombination R)) ((), (x, y)) = 2*x + 3*y :=
  compile_correct R (linearCombination R) ((), (x, y))

end MatrixCompiler
