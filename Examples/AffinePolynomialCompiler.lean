import Applications.AlgebraicGeometry.AffineCompiler
import Mathlib.Data.ZMod.Basic

/-! Polynomial composition, shared source expressions, all-algebra points and
finite-field information loss through the public affine compiler. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.AffinePolynomial
open FirstOrderCompiler MvPolynomial PolynomialMap
open MatrixCompiler (Slots encode decode)
open AffinePolynomialCompiler CategoryTheory AlgebraicGeometry
variable (R : Type) [CommRing R]

abbrev plane := Ty.prod .base .base

def f : Code R plane plane := Sum.elim
  (fun _ => X (.inl ()) + X (.inr ()))
  (fun _ => X (.inl ()) * X (.inr ()))
def g : Code R plane plane := Sum.elim
  (fun _ => X (.inl ()) * X (.inl ()) + X (.inr ()))
  (fun _ => X (.inl ()) + X (.inr ()))
def composite : Code R plane plane := Sum.elim
  (fun _ => (X (.inl ()) + X (.inr ())) * (X (.inl ()) + X (.inr ())) + X (.inl ()) * X (.inr ()))
  (fun _ => (X (.inl ()) + X (.inr ())) + X (.inl ()) * X (.inr ()))

theorem composition_coordinates : PolynomialMap.comp (g R) (f R) = composite R := by
  funext i; cases i <;> simp [PolynomialMap.comp, coordHom, f, g, composite]

theorem composition_schemes :
    geometricComp R (realize R (g R)) (realize R (f R)) = realize R (composite R) := by
  rw [← realize_comp, composition_coordinates]

variable (A : Type) [CommRing A] [Algebra R A]

theorem composition_values (x y : A) :
    denote R A (PolynomialMap.comp (g R) (f R)) (x,y) =
      ((x+y)*(x+y)+x*y, (x+y)+x*y) := by
  rw [composition_coordinates]
  simp [denote, PolynomialMap.evaluate, composite, encode, decode]

theorem composition_points (x y : A) :
    mapPoint R A (geometricComp R (realize R (g R)) (realize R (f R)))
      (pointEquiv R A plane (Sum.elim (fun _ => x) (fun _ => y))) =
    pointEquiv R A plane (Sum.elim (fun _ => (x+y)*(x+y)+x*y) (fun _ => (x+y)+x*y)) := by
  rw [composition_schemes, realize_point]
  congr 1
  funext i; cases i <;> simp [PolynomialMap.evaluate, composite]

/-- Discard the empty-context coordinate and retain the supplied input. -/
def input (a : Ty) : Code R a (.prod .unit a) :=
  Sum.elim Empty.elim PolynomialMap.identity

def sourceF {Γ : Ctx} : Term (Prim R) (plane :: Γ) plane :=
  .pair (.prim .add (.var .here)) (.prim .mul (.var .here))
def sourceG {Γ : Ctx} : Term (Prim R) (plane :: Γ) plane :=
  .pair (.prim .add (.pair
    (.prim .mul (.pair (.fst (.var .here)) (.fst (.var .here)))) (.snd (.var .here))))
    (.prim .add (.var .here))
def sourceComposite : Term (Prim R) [plane] plane :=
  .letE (sourceF R) (sourceG R)

theorem source_composite_coordinates :
    PolynomialMap.comp (compile (target R) (sourceComposite R)) (input R plane) = composite R := by
  funext i; cases i <;> simp [sourceComposite, sourceF, sourceG, input,
    compile, compileVar, target, PolynomialMap.comp, coordHom, PolynomialMap.identity,
    primitive, pair, first, second, composite]

theorem source_composite_scheme :
    geometricComp R (compile (geometricTarget R) (sourceComposite R)) (realize R (input R plane)) =
      geometricComp R (realize R (g R)) (realize R (f R)) := by
  rw [← compile_realize, ← realize_comp, source_composite_coordinates, composition_schemes]

/-- The source expressions are independent of their coordinate implementation. -/
def shifted : Term (Prim R) [.base] .base :=
  .prim .add (.pair (.var .here) (.prim (.constant 2) .unit))
def duplicated : Term (Prim R) [.base] .base :=
  .prim .mul (.pair (shifted R) (shifted R))
def shared : Term (Prim R) [.base] .base :=
  .letE (shifted R) (.prim .mul (.pair (.var .here) (.var .here)))

theorem same_code : compile (target R) (duplicated R) = compile (target R) (shared R) := by
  funext i; cases i
  simp [compile, compileVar, target, duplicated, shared, shifted,
    PolynomialMap.comp, PolynomialMap.identity, coordHom, primitive, pair, second]

theorem same_scheme :
    compile (geometricTarget R) (duplicated R) = compile (geometricTarget R) (shared R) := by
  rw [← compile_realize, ← compile_realize, same_code]

theorem shared_points (x : A) :
    mapPoint R A (compile (geometricTarget R) (shared R))
      (pointEquiv R A _ (encode _ ((),x))) =
    pointEquiv R A .base (fun _ => (x+2)*(x+2)) := by
  rw [compile_points]
  congr 1
  funext i
  change (x + (algebraMap R A) (2 : R)) * (x + (algebraMap R A) (2 : R)) =
    (x + 2) * (x + 2)
  rw [map_ofNat]

/-- No coordinate is introduced by an empty context. -/
theorem closed_constant :
    compile (target R) (.prim (.constant (2 : R)) .unit : Term (Prim R) [] .base) =
      (fun _ => C 2) := by
  funext i; simp [compile, target, PolynomialMap.comp, coordHom, primitive]

theorem empty_unit :
    compile (geometricTarget R) (.unit : Term (Prim R) [] .unit) = geometricIdentity R .unit := by
  rw [← compile_realize, ← realize_identity]
  apply congrArg (realize R)
  funext i; exact nomatch i

example : IsIso (baseMap R .unit) := inferInstance
example : IsPullback (realize R (first R .base .base)).val
    (realize R (second R .base .base)).val (baseMap R .base) (baseMap R .base) :=
  product_isPullback R _ _

/-- Ordinary points over F₂ forget the difference between these polynomials. -/
def squareCode : Code (ZMod 2) .base .base := fun _ => X () ^ 2
def identityCode : Code (ZMod 2) .base .base := PolynomialMap.identity

theorem same_finite_field_values (x : ZMod 2) :
    denote (ZMod 2) (ZMod 2) squareCode x = denote (ZMod 2) (ZMod 2) identityCode x := by
  simp only [denote, PolynomialMap.evaluate, squareCode, identityCode,
    PolynomialMap.identity, encode, decode, map_pow, aeval_X]
  fin_cases x <;> decide

theorem different_polynomials : squareCode ≠ identityCode := by
  intro h
  have hh := congrArg (fun k : Code (ZMod 2) .base .base =>
    (k ()).coeff (Finsupp.single () 2)) h
  norm_num [squareCode, identityCode, PolynomialMap.identity, coeff_X_pow, coeff_X] at hh

theorem different_schemes : realize (ZMod 2) squareCode ≠ realize (ZMod 2) identityCode :=
  fun h => different_polynomials (realize_injective (ZMod 2) h)

/-- A generic polynomial-ring point still distinguishes the two maps. -/
theorem different_generic_points :
    PolynomialMap.evaluate squareCode (X : Unit → MvPolynomial Unit (ZMod 2)) ≠
      PolynomialMap.evaluate identityCode X := by
  simpa only [PolynomialMap.evaluate_generic] using different_polynomials

end Examples.AffinePolynomial
