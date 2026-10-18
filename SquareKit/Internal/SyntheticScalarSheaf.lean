import SquareKit.Internal.SyntheticScalar
import SquareKit.AlgebraicDerivative

/-! Experimental interpretation of every synthetic scalar rule in the
constructed algebraic KL model. This source adapter is opt-in.
-/
noncomputable section
namespace SquareKit.Internal.SyntheticScalar.SheafSem
open CategoryTheory
open AlgebraicStage AlgebraicKL AlgebraicDerivative SheafRelation

abbrev Assignment (n : ℕ) := Fin n → (scalar ⟶ scalar)

def map {n} (ρ : Assignment n) : MapExpr n → (scalar ⟶ scalar)
  | .param i => ρ i
  | .add f g => lift (map ρ f) (map ρ g) ≫ AlgebraicStage.add
  | .mul f g => lift (map ρ f) (map ρ g) ≫ AlgebraicStage.mul
  | .derivative f => derivative (map ρ f)

def atom {n} (ρ : Assignment n) (A : Stage) (x : Carrier A)
    (d : infinitesimal.obj.obj (atStage A)) : Atom n → Carrier A
  | .base f => (map ρ f).hom.app (atStage A) x
  | .shifted f => (map ρ f).hom.app (atStage A) (x+d.val)
  | .epsilon => d.val

/-- Soundness covers every source constructor, including polynomial certificates.
No source product rule or desired equality is required from the assignment. -/
theorem sound {n} (ρ : Assignment n) (A : Stage) (x : Carrier A)
    (d : infinitesimal.obj.obj (atStage A)) {a b : Expr n} (h : Derives a b) :
    Expr.eval (atom ρ A x d) a = Expr.eval (atom ρ A x d) b := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij
  | add _ _ ih ij => exact congrArg₂ (·+·) ih ij
  | mul _ _ ih ij => exact congrArg₂ (·*·) ih ij
  | neg _ ih => exact congrArg Neg.neg ih
  | ring hc => rw [Expr.eval_polynomial, Expr.eval_polynomial, hc]
  | nilsquare => simpa [Expr.eval, atom] using d.property
  | taylor f => exact AlgebraicDerivative.taylor (map ρ f) A x d
  | base_add f g => rfl
  | base_mul f g => rfl
  | shifted_mul f g => rfl

/-- Unique slopes are interpreted with the inverse of the proved KL map.
This quantifies all stages and all infinitesimals, never cancelling one d. -/
theorem slope_sound {n} (ρ : Assignment n) {f g : MapExpr n} (h : Slope f g) :
    derivative (map ρ f) = map ρ g := by
  cases h with
  | unique he =>
    apply derivative_unique
    intro A x d
    exact sound ρ A x d he

/-- The same derivation is sound after any sheaf-valued parameter assignment. -/
theorem sound_parameters {n} (ρ : Assignment n) {X : Sheaf topology Type}
    (p : X ⟶ scalar) (A : Stage) (x : X.obj.obj (atStage A))
    (d : infinitesimal.obj.obj (atStage A)) {a b : Expr n} (h : Derives a b) :
    Expr.eval (atom ρ A (p.hom.app (atStage A) x) d) a =
      Expr.eval (atom ρ A (p.hom.app (atStage A) x) d) b :=
  sound ρ A _ d h

end SquareKit.Internal.SyntheticScalar.SheafSem
