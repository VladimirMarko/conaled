import SquareKit.Internal.Cubical.FunctionComposition

/-! Dependent products inherit actual uniform filling from domain filling and
codomain composition, through the general composition-to-filling construction. -/
namespace SquareKit.Cubical.Presheaf
universe u

def piComposition {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Composition B) : Composition (pi A B) where
  comp := FunctionComposition.comp F hF G

theorem piComposition_lawful {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Composition B) (hG : G.Lawful) :
    (piComposition F hF G).Lawful where
  boundary := FunctionComposition.comp_boundary F hF G hG
  uniform p φ b σ := FunctionComposition.comp_uniform F hF G hG p φ b σ

noncomputable def piFilling {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) : Filling (pi A B) :=
  (piComposition F hF G.toComposition).toFilling

theorem piFilling_lawful {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) :
    (piFilling F hF G).Lawful :=
  Composition.toFilling_lawful (piComposition_lawful F hF G.toComposition
    (Filling.toComposition_lawful hG))

end SquareKit.Cubical.Presheaf
