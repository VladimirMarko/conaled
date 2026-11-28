import Applications.AlgebraicGeometry.BaseChange
import Examples.AffinePolynomialCompiler
import SquareKit.ClosedComparison

/-! Nonidentity scalar extension, compiled let, and failure of reflection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.AffineBaseChange
open FirstOrderCompiler MvPolynomial PolynomialMap
open AffinePolynomialCompiler CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AffinePolynomial
open scoped TensorProduct

def modTwo : ℤ →+* ZMod 2 := Int.castRingHom _
def adjoin : ZMod 2 →+* MvPolynomial Unit (ZMod 2) := C

def shiftedSquare : Code ℤ .base .base := fun _ => (X () + C 2) ^ 2

theorem specialized_square : changeCoefficients modTwo shiftedSquare = squareCode := by
  have h : modTwo 2 = 0 := by decide
  funext i
  simp only [changeCoefficients, shiftedSquare, squareCode, map_pow, map_add,
    map_X, map_C, h, map_zero, add_zero]

theorem direct_scheme_specialization :
    (realize (ZMod 2) squareCode).val ≫ scalarMap modTwo .base =
      scalarMap modTwo .base ≫ (realize ℤ shiftedSquare).val := by
  rw [← specialized_square]
  exact realize_changeCoefficients modTwo shiftedSquare

theorem compiled_let_coordinates :
    compile (coefficientTarget modTwo) (shared ℤ) =
      (fun _ => (X (Sum.inr ())) ^ 2) := by
  rw [← compile_changeCoefficients]
  funext i
  have h : (2 : MvPolynomial (MatrixCompiler.Slots (context [.base])) (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C : ZMod 2 →+* MvPolynomial (MatrixCompiler.Slots (context [.base])) (ZMod 2))
        (show (2 : ZMod 2) = 0 by decide)
  simp [changeCoefficients, modTwo, compile, compileVar, target, shared, shifted,
    PolynomialMap.comp, PolynomialMap.identity, coordHom, primitive,
    AffinePolynomialCompiler.pair, second, pow_two, map_ofNat, h]

theorem compiled_let_pullback :
    (compile (coefficientGeometricTarget modTwo) (shared ℤ)).val ≫
        (baseChangeIso modTwo .base).hom =
      (baseChangeIso modTwo (context [.base])).hom ≫
        pullbackHom modTwo (compile (geometricTarget ℤ) (shared ℤ)) :=
  compile_pullback modTwo (shared ℤ)

theorem two_step_coordinates :
    changeCoefficients adjoin (changeCoefficients modTwo shiftedSquare) =
      changeCoefficients (adjoin.comp modTwo) shiftedSquare :=
  changeCoefficients_comp adjoin modTwo shiftedSquare

theorem two_step_schemes :
    baseChangedHom adjoin (baseChangedHom modTwo (realize ℤ shiftedSquare)) =
      baseChangedHom (adjoin.comp modTwo) (realize ℤ shiftedSquare) :=
  baseChangedHom_comp adjoin modTwo _

theorem two_step_scalar_square :
    scalarMap adjoin .base ≫ scalarMap modTwo .base = scalarMap (adjoin.comp modTwo) .base :=
  scalarMap_comp adjoin modTwo .base

def two : Code ℤ .unit .base := fun _ => C 2
def zero : Code ℤ .unit .base := fun _ => C 0

theorem distinct_before : realize ℤ two ≠ realize ℤ zero := by
  intro h
  have hc := congrArg (fun f : Code ℤ .unit .base => constantCoeff (f ()))
    (realize_injective ℤ h)
  norm_num only [two, zero, constantCoeff_C] at hc

theorem equal_after : baseChangedHom modTwo (realize ℤ two) =
    baseChangedHom modTwo (realize ℤ zero) := by
  simp only [baseChangedHom_realize]
  congr 1
  have h : modTwo 2 = 0 := by decide
  funext i; simp only [changeCoefficients, two, zero, map_C, h, map_zero]

theorem base_change_not_injective :
    ¬ Function.Injective (baseChangedHom modTwo (a := .unit) (b := .base)) :=
  fun h => distinct_before (h equal_after)

example : IsPullback (scalarMap modTwo .base) (baseMap (ZMod 2) .base)
    (baseMap ℤ .base) (Spec.map (CommRingCat.ofHom modTwo)) :=
  scalarMap_isPullback modTwo .base

example (s : ZMod 2) (p : CoordinateRing ℤ .base) :
    tensorComparison .base (s ⊗ₜ[ℤ] p) = s • MvPolynomial.map (algebraMap ℤ (ZMod 2)) p :=
  tensorComparison_tmul .base s p

example (a : Ty) :
    (iteratedBaseChangeIso adjoin modTwo a).hom ≫ (successivePullbackIso adjoin modTwo a).hom =
      (baseChangeIso (adjoin.comp modTwo) a).hom :=
  baseChangeIso_comp adjoin modTwo a

example : IsIso (unitExponentialComparison modTwo .base).val := inferInstance

example (f : Code ℤ (.prod .unit .base) .base) :
    geometricComp (ZMod 2) (unitExponentialComparison modTwo .base)
      (realize (ZMod 2) (changeCoefficients modTwo (unitCurryEquiv ℤ .base .base f))) =
      realize (ZMod 2) (unitCurryEquiv (ZMod 2) .base .base (changeCoefficients modTwo f)) :=
  unitExponentialComparison_curry modTwo f

example (e : Ty)
    (curry : GeometricHom (ZMod 2) (.prod .unit .base) .base → GeometricHom (ZMod 2) .unit e)
    (uncurry : GeometricHom (ZMod 2) .unit e → GeometricHom (ZMod 2) (.prod .unit .base) .base)
    (h : ∀ f, uncurry (curry f) = f) : False :=
  no_geometric_ground_exponential e curry uncurry h

end Examples.AffineBaseChange

/-! Conditional ambient comparison for #739. These hypotheses are not instances
for the category of affine schemes or for arbitrary geometric base change. -/
namespace Examples.AffineBaseChange.Ambient
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
universe u u' v
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v} D]
variable [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
variable [MonoidalClosed C] [MonoidalClosed D]
variable (F : C ⥤ D) [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) F]

/-- The canonical comparison is obtained by currying transported evaluation. -/
def comparison (A B : C) : F.obj ((ihom A).obj B) ⟶ (ihom (F.obj A)).obj (F.obj B) :=
  (expComparison F A).app B

theorem comparison_curry {A X B : C} (f : A ⊗ X ⟶ B) :
    F.map (curry f) ≫ comparison F A B =
      curry (inv (prodComparison F A X) ≫ F.map f) :=
  SquareKit.ClosedComparison.curry_compare F f

/-- Invertibility follows from Frobenius, which is an additional obligation. -/
theorem comparison_isIso {L : D ⥤ C} (h : L ⊣ F) (A B : C)
    [IsIso (frobeniusMorphism F h A)] : IsIso (comparison F A B) := by
  let : IsIso (expComparison F A) := expComparison_iso_of_frobeniusMorphism_iso F h A
  change IsIso ((expComparison F A).app B)
  infer_instance

/-- A sufficient source of Frobenius is a full faithful right adjoint whose left adjoint
preserves binary products. Finite-limit preservation of F alone is not this condition. -/
example {L : D ⥤ C} (h : L ⊣ F) [F.Full] [F.Faithful]
    [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) L] (A B : C) :
    IsIso (comparison F A B) :=
  comparison_isIso F h A B

end Examples.AffineBaseChange.Ambient
