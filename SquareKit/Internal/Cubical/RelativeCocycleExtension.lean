import SquareKit.Internal.Cubical.PartialCocycles

/-! A relative primitive extends a partial cocycle without changing its cap. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]

def addCoboundary (z : Cocycle2 C) (b : Cochain1 C) : Cocycle2 C where
  cochain f g := z.cochain f g + δ1 b f g
  closed f g h := by
    have hz := z.closed f g h
    have hb := δ2_δ1 b f g h
    simp only [δ2] at *
    omega

def partialDifference {S : SieveObjects C} (t : PartialCocycle2 S) (z : Cocycle2 C) :
    PartialCocycle2 S where
  cochain f g p := t.cochain f g p - z.cochain f g
  closed f g h p := by
    have ht := t.closed f g h p
    have hz := z.closed f g h
    simp only [δ2] at hz
    omega

/-- Extension changes the base cocycle by a genuine coboundary. -/
noncomputable def relativeExtension {S : SieveObjects C} (z : Cocycle2 C)
    (b : PartialCochain1 S) : Cocycle2 C := addCoboundary z (extendZero b)

theorem relativeExtension_inside {S : SieveObjects C} (z : Cocycle2 C)
    (t : PartialCocycle2 S) (b : PartialCochain1 S)
    (hb : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (p : S.contains Z),
      b g p - b (f ≫ g) p + b f (S.downward g p) = t.cochain f g p - z.cochain f g)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (p : S.contains Z) :
    (relativeExtension z b).cochain f g = t.cochain f g p := by
  change z.cochain f g + δ1 (extendZero b) f g = _
  rw [δ1_extendZero_inside b f g p,hb f g p]
  omega

theorem relativeExtension_zero {S : SieveObjects C} (z : Cocycle2 C)
    (b : PartialCochain1 S) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : extendZero b f = 0) (hg : extendZero b g = 0) (hfg : extendZero b (f ≫ g) = 0) :
    (relativeExtension z b).cochain f g = z.cochain f g := by
  change z.cochain f g + δ1 (extendZero b) f g = _
  simp [δ1,hf,hg,hfg]

end SquareKit.Cubical.CategoryCocycles
