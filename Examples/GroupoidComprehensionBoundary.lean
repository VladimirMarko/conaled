import SquareKit.Internal.PathTransport.SplitFamily
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.ZMod.Basic

/-! A commuting square of actual groupoid display maps need not preserve the
chosen horizontal lifts. This prevents silently identifying all display squares
with strict morphisms of split families. -/
namespace Examples.GroupoidComprehensionBoundary
open CategoryTheory
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev G := SingleObj (Multiplicative (ZMod 2))
def A : G ⥤ Grpd := constant G

/-- The shear (g,h) ↦ (g,g+h) is a functor over the base. -/
def shear : Extend A ⥤ Extend A where
  obj := id
  map f := {
    base := f.base
    fiber := by
      change Multiplicative (ZMod 2)
      exact (show Multiplicative (ZMod 2) from f.base) * (show Multiplicative (ZMod 2) from f.fiber)
  }
  map_id x := by
    apply Grothendieck.ext _ _ rfl
    simp [A, constant, Grpd.forgetToCat]
  map_comp f g := by
    fapply Grothendieck.ext
    · rfl
    · simp only [eqToHom_refl, Category.id_comp]
      dsimp [A, constant, Grothendieck.comp, Grpd.forgetToCat]
      simp only [Category.id_comp]
      let fb : Multiplicative (ZMod 2) := f.base
      let gb : Multiplicative (ZMod 2) := g.base
      let ff : Multiplicative (ZMod 2) := f.fiber
      let gf : Multiplicative (ZMod 2) := g.fiber
      change (gb * fb) * (gf * ff) = (gb * gf) * (fb * ff)
      simp [mul_comm, mul_left_comm]

theorem shear_over_base : shear ⋙ weaken A = weaken A := rfl

def point : Extend A := ⟨SingleObj.star (Multiplicative (ZMod 2)), SingleObj.star (Multiplicative (ZMod 2))⟩

def horizontal (g : Multiplicative (ZMod 2)) : point ⟶ point := ⟨g, (show Multiplicative (ZMod 2) from 1)⟩

/-- The chosen lift of the nonzero base loop acquires a nonzero fiber loop. -/
theorem shear_not_horizontal :
    shear.map (horizontal (Multiplicative.ofAdd (1 : ZMod 2))) ≠
      horizontal (Multiplicative.ofAdd (1 : ZMod 2)) := by
  intro h
  have hh := congrArg Grothendieck.Hom.fiber h
  change (Multiplicative.ofAdd (1 : ZMod 2)) * 1 = (1 : Multiplicative (ZMod 2)) at hh
  have hn : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd (by simp at hh)
  exact (by decide : (1 : ZMod 2) ≠ 0) hn

end Examples.GroupoidComprehensionBoundary
