import SquareKit.Internal.SyntheticScalarSoundness
import SquareKit.SmoothGeometricDerivative

/-! Experimental interpretation of every synthetic scalar rule in the
constructed geometric KL model. This source adapter is opt-in.
-/
noncomputable section
namespace SquareKit.Internal.SyntheticScalar.GeometricSem
open CategoryTheory
open SmoothPresentationSite SmoothGeometricKL SmoothGeometricDerivative SheafRelation

abbrev Assignment (n : ℕ) := Fin n → (scalar ⟶ scalar)

def map {n} (ρ : Assignment n) : MapExpr n → (scalar ⟶ scalar)
  | .param i => ρ i
  | .add f g => lift (map ρ f) (map ρ g) ≫ SmoothPresentationSite.add
  | .mul f g => lift (map ρ f) (map ρ g) ≫ SmoothPresentationSite.mul
  | .derivative f => derivative (map ρ f)

def atom {n} (ρ : Assignment n) (A : Code) (x : Carrier A)
    (d : infinitesimal.obj.obj (atStage A)) : Atom n → Carrier A
  | .base f => (map ρ f).hom.app (atStage A) x
  | .shifted f => (map ρ f).hom.app (atStage A) (x+d.val)
  | .epsilon => d.val

/-- Soundness covers every source constructor, including polynomial certificates.
No source product rule or desired equality is required from the assignment. -/
theorem sound {n} (ρ : Assignment n) (A : Code) (x : Carrier A)
    (d : infinitesimal.obj.obj (atStage A)) {a b : Expr n} (h : Derives a b) :
    Expr.eval (atom ρ A x d) a = Expr.eval (atom ρ A x d) b := by
  exact sound_eval (atom ρ A x d) d.property
    (fun f => SmoothGeometricDerivative.taylor (map ρ f) A x d)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) h

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
    (p : X ⟶ scalar) (A : Code) (x : X.obj.obj (atStage A))
    (d : infinitesimal.obj.obj (atStage A)) {a b : Expr n} (h : Derives a b) :
    Expr.eval (atom ρ A (p.hom.app (atStage A) x) d) a =
      Expr.eval (atom ρ A (p.hom.app (atStage A) x) d) b :=
  sound ρ A _ d h

end SquareKit.Internal.SyntheticScalar.GeometricSem
