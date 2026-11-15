import SquareKit.Internal.Cubical.CocyclePresheaf

/-! Additive pasting of cocycles along a shared face. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory
universe u v u' v'
variable {C : Type u} [Category.{v} C]

def pasteCocycle (a b c : Cocycle2 C) : Cocycle2 C where
  cochain f g := a.cochain f g + b.cochain f g - c.cochain f g
  closed f g h := by
    have ha := a.closed f g h
    have hb := b.closed f g h
    have hc := c.closed f g h
    simp only [δ2] at *
    omega

theorem pasteCocycle_left (a b : Cocycle2 C) : pasteCocycle a b b = a := by
  apply Cocycle2.ext
  funext X Y Z f g
  simp only [pasteCocycle]
  omega

theorem pasteCocycle_right (a b : Cocycle2 C) : pasteCocycle a b a = b := by
  apply Cocycle2.ext
  funext X Y Z f g
  simp only [pasteCocycle]
  omega

theorem pasteCocycle_pullback {D : Type u'} [Category.{v'} D]
    (a b c : Cocycle2 C) (F : D ⥤ C) :
    (pasteCocycle a b c).pullback F = pasteCocycle (a.pullback F) (b.pullback F) (c.pullback F) := rfl

end SquareKit.Cubical.CategoryCocycles
