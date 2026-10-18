import SquareKit.SyntheticProductRule
import Examples.AlgebraicKL

/-! Experimental source-to-model-to-analytic product-rule consumer.
Fourth-power coefficients come from the interpreted source product proof.
The existing ordinary KL clients are used directly in the same module.
-/
noncomputable section
namespace Examples.SyntheticProduct
open CategoryTheory
open SquareKit.AlgebraicStage SquareKit.AlgebraicKL SquareKit.AlgebraicDerivative
open SquareKit.SheafRelation
open SquareKit.Internal.SyntheticScalar

abbrev square := AlgebraicKL.square

def fourth : scalar ⟶ scalar := lift square square ≫ SquareKit.AlgebraicStage.mul

/-- This calculation invokes source soundness, then the old ordinary square client. -/
theorem derivative_fourth_apply (A : Stage) (x : Carrier A) :
    (derivative fourth).hom.app (atStage A) x = 4*x^3 := by
  have h := SquareKit.SyntheticProductRule.component square square A x
  rw [AlgebraicKL.derivative_square_apply] at h
  change (derivative fourth).hom.app (atStage A) x = (2*x)*(x*x)+(x*x)*(2*x) at h
  rw [h]
  ring

/-- An ordinary direct-map observation and a source-derived derivative coexist. -/
theorem mixed_styles (A : Stage) (x : Carrier A) :
    square.hom.app (atStage A) x = x*x ∧
      (derivative fourth).hom.app (atStage A) x = 4*x^3 :=
  ⟨rfl, derivative_fourth_apply A x⟩

/-- Taylor with a source-derived coefficient at the nonzero dual epsilon. -/
theorem fourth_at_epsilon (x : Carrier AlgebraicKL.dualIntegers) :
    fourth.hom.app (atStage AlgebraicKL.dualIntegers) (x+(eps .integers).val) =
      x^4 + (4*x^3)*(eps .integers).val := by
  have h := taylor fourth AlgebraicKL.dualIntegers x (eps .integers)
  rw [derivative_fourth_apply] at h
  change _ = (x*x)*(x*x)+(4*x^3)*(eps .integers).val at h
  rw [h]
  ring

/-- Concrete restriction comparison for the coefficient obtained from source soundness. -/
theorem fourth_flip (x : Carrier AlgebraicKL.dualIntegers) :
    (derivative fourth).hom.app (atStage AlgebraicKL.dualIntegers) (ringMap AlgebraicKL.flip x) =
      ringMap AlgebraicKL.flip (4*x^3) := by
  have h := congrArg
    (fun k : scalar.obj.obj (atStage AlgebraicKL.dualIntegers) ⟶
      scalar.obj.obj (atStage AlgebraicKL.dualIntegers) => k x)
    ((derivative fourth).hom.naturality (stageMap AlgebraicKL.flip))
  change (derivative fourth).hom.app (atStage AlgebraicKL.dualIntegers) (ringMap AlgebraicKL.flip x) =
    ringMap AlgebraicKL.flip ((derivative fourth).hom.app (atStage AlgebraicKL.dualIntegers) x) at h
  exact h.trans (congrArg (ringMap AlgebraicKL.flip)
    (derivative_fourth_apply AlgebraicKL.dualIntegers x))

def polynomial : Polynomial ℤ := Polynomial.X ^ 4

theorem fourth_polynomial (A : Stage) (x : Carrier A) :
    fourth.hom.app (atStage A) x = polynomial.eval₂ (Int.castRingHom (Carrier A)) x := by
  change (x*x)*(x*x) = _
  simp only [polynomial, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  ring

/-- The coefficient is observed from the source-derived model derivative. -/
def modelCoefficient : Polynomial ℤ :=
  (derivative fourth).hom.app (atStage (.polynomial .integers)) Polynomial.X

theorem modelCoefficient_eq : modelCoefficient = polynomial.derivative := by
  have h : (4 : Polynomial ℤ) * (Polynomial.X : Polynomial ℤ)^3 = polynomial.derivative := by
    simp [polynomial]
  exact (derivative_fourth_apply (.polynomial .integers)
    (show Carrier (.polynomial .integers) from (Polynomial.X : Polynomial ℤ))).trans h

/-- External ℝ evaluation consumes the coefficient obtained via the source proof. -/
theorem analytic_fourth (x : ℝ) :
    HasDerivAt (fun y : ℝ => (polynomial.map (Int.castRingHom ℝ)).eval y)
      ((modelCoefficient.map (Int.castRingHom ℝ)).eval x) x := by
  rw [modelCoefficient_eq]
  simpa only [Polynomial.derivative_map] using
    (polynomial.map (Int.castRingHom ℝ)).hasDerivAt x

abbrev boundaryLeft : Expr 0 := (0+1*epsilon)*(0+1*epsilon)
abbrev boundaryRight : Expr 0 := 0*0+(1*0+0*1)*epsilon

/-- The truncated expansion has a source proof using the nilsquare rule. -/
theorem boundary_source : Derives boundaryLeft boundaryRight :=
  .trans (product_cross 0 0 1 1) (remove_cross 0 0 1 1)

/-- Without nilsquare, a plain ring certificate cannot discard the cross term.
Evaluation at epsilon=1 is a counterexample to the truncated ring identity. -/
theorem boundary_no_ring_certificate :
    Expr.polynomial boundaryLeft ≠ Expr.polynomial boundaryRight := by
  intro h
  have he : Expr.eval (fun _ : Atom 0 => (1 : ℤ)) boundaryLeft =
      Expr.eval (fun _ : Atom 0 => (1 : ℤ)) boundaryRight := by
    rw [Expr.eval_polynomial, Expr.eval_polynomial, h]
  norm_num [Expr.eval, boundaryLeft, boundaryRight] at he

/-- The existing nontriviality and nonidentity witnesses apply to these consumers. -/
theorem nontrivial_checks : (eps .integers).val ≠ 0 ∧ AlgebraicKL.flip ≠ 𝟙 AlgebraicKL.dualIntegers :=
  ⟨AlgebraicScalar.epsilon_nonzero, AlgebraicKL.flip_not_identity⟩

end Examples.SyntheticProduct
