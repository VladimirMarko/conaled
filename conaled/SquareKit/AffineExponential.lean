import SquareKit.SheafFunction

/-! Experimental shared conversion from natural coefficient reconstruction to
an isomorphism with the actual sheaf exponential. Used by both KL models. -/
noncomputable section
namespace SquareKit.AffineExponential
open CategoryTheory SheafRelation SheafFunction
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D R P : Sheaf J (Type (max u v))}
variable (coeff : {X : Sheaf J (Type (max u v))} → (product D X ⟶ R) → (X ⟶ P))
variable (natural : ∀ {X Y} (h : product D X ⟶ R) (p : Y ⟶ X),
  coeff (parameterMap D p ≫ h) = p ≫ coeff h)

include natural in
theorem extract_curry {X} (h : product D X ⟶ R) :
    curry h ≫ coeff (evaluation D R) = coeff h := by
  rw [← natural, ← uncurry_evaluation, beta]

/-- Naturality and two reconstruction laws suffice; no scalar or KL axiom is assumed. -/
def iso (body : product D P ⟶ R)
    (reconstruct : ∀ {X} (h : product D X ⟶ R), parameterMap D (coeff h) ≫ body = h)
    (recover : ∀ {X} (p : X ⟶ P), coeff (parameterMap D p ≫ body) = p) :
    P ≅ exponential D R where
  hom := curry body
  inv := coeff (evaluation D R)
  hom_inv_id := by
    rw [extract_curry coeff natural]
    convert recover (𝟙 P) using 1
    rfl
  inv_hom_id := by
    rw [← curry_parameter, reconstruct]
    exact eta (𝟙 _)

end SquareKit.AffineExponential
