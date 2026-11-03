import SquareKit.Internal.SyntheticScalarSheaf

/-! Experimental optional source-to-model consequence for ordinary sheaf maps.
The public product theorem consumes a source derivation through all-rule
soundness. Ordinary scalar/model modules do not import this adapter.
-/
noncomputable section
namespace SquareKit.SyntheticProductRule
open CategoryTheory
open AlgebraicStage AlgebraicKL AlgebraicDerivative SheafRelation
open Internal.SyntheticScalar

/-- Ordinary natural-map product rule, obtained from the source proof. -/
theorem product (f g : scalar ⟶ scalar) :
    derivative (lift f g ≫ AlgebraicStage.mul) =
      lift (lift (derivative f) g ≫ AlgebraicStage.mul)
        (lift f (derivative g) ≫ AlgebraicStage.mul) ≫ AlgebraicStage.add := by
  have h := SheafSem.slope_sound (fun i : Fin 2 => if i = 0 then f else g)
    (product_rule (.param 0) (.param 1))
  simpa only [SheafSem.map, productSlope, ite_eq_left (show (0 : Fin 2) = 0 from rfl),
    ite_eq_right (show (1 : Fin 2) ≠ 0 by decide), ite_true] using h

theorem component (f g : scalar ⟶ scalar) (A : Stage) (x : Carrier A) :
    (derivative (lift f g ≫ AlgebraicStage.mul)).hom.app (atStage A) x =
      (derivative f).hom.app (atStage A) x * g.hom.app (atStage A) x +
      f.hom.app (atStage A) x * (derivative g).hom.app (atStage A) x :=
  congrArg (fun k : scalar ⟶ scalar => k.hom.app (atStage A) x) (product f g)

/-- Product differentiation remains valid under any natural parameter substitution. -/
theorem parameters {X : Sheaf topology Type} (p : X ⟶ scalar) (f g : scalar ⟶ scalar) :
    p ≫ derivative (lift f g ≫ AlgebraicStage.mul) =
      p ≫ (lift (lift (derivative f) g ≫ AlgebraicStage.mul)
        (lift f (derivative g) ≫ AlgebraicStage.mul) ≫ AlgebraicStage.add) :=
  congrArg (fun k => p ≫ k) (product f g)

end SquareKit.SyntheticProductRule
