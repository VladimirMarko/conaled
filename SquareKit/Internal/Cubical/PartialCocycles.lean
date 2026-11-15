import SquareKit.Internal.Cubical.CochainSieveExtension

/-! Relative cocycles and prisms keep the terminal vertex's sieve membership. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]

abbrev PartialCochain2 (S : SieveObjects C) :=
  ∀ {X Y Z : C}, (X ⟶ Y) → (Y ⟶ Z) → S.contains Z → ℤ

structure PartialCocycle2 (S : SieveObjects C) where
  cochain : PartialCochain2 S
  closed : ∀ {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (p : S.contains Z),
    cochain g h p - cochain (f ≫ g) h p + cochain f (g ≫ h) p -
      cochain f g (S.downward h p) = 0

def partialPrism {S : SieveObjects C} (z : PartialCocycle2 S)
    {F G : C ⥤ C} (η : F ⟶ G) (hG : ∀ X, S.contains X → S.contains (G.obj X)) :
    PartialCochain1 S := fun {X Y} f p =>
  z.cochain (η.app X) (G.map f) (hG Y p) - z.cochain (F.map f) (η.app Y) (hG Y p)

theorem partialPrism_boundary {S : SieveObjects C} (z : PartialCocycle2 S)
    {F G : C ⥤ C} (η : F ⟶ G) (hG : ∀ X, S.contains X → S.contains (G.obj X))
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (p : S.contains Z) :
    partialPrism z η hG g p - partialPrism z η hG (f ≫ g) p +
      partialPrism z η hG f (S.downward g p) =
      z.cochain (G.map f) (G.map g) (hG Z p) -
      z.cochain (F.map f) (F.map g) (S.downward (η.app Z) (hG Z p)) := by
  have h₁ := z.closed (F.map f) (F.map g) (η.app Z) (hG Z p)
  have h₂ := z.closed (F.map f) (η.app Y) (G.map g) (hG Z p)
  have h₃ := z.closed (η.app X) (G.map f) (G.map g) (hG Z p)
  rw [η.naturality g] at h₁
  rw [η.naturality f] at h₂
  simp only [partialPrism,Functor.map_comp]
  omega

end SquareKit.Cubical.CategoryCocycles
