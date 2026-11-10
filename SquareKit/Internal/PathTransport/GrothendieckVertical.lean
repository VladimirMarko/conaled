import SquareKit.Internal.PathTransport.GrothendieckProjectionLifts

/-! Arrows with identity base are precisely arrows in the included fiber. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GrothendieckVertical
open CategoryTheory
universe u v w z
variable {C : Type u} [Category.{v} C] (F : C ⥤ Cat.{w,z})
variable {c : C} {x y : F.obj c}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def arrow (f : (Grothendieck.ι F c).obj x ⟶ (Grothendieck.ι F c).obj y)
    (h : f.base = 𝟙 c) : x ⟶ y := by
  rcases f with ⟨b,f⟩
  change b = 𝟙 c at h
  subst b
  exact eqToHom (by simp) ≫ f

theorem inclusion_arrow (f : (Grothendieck.ι F c).obj x ⟶ (Grothendieck.ι F c).obj y)
    (h : f.base = 𝟙 c) : (Grothendieck.ι F c).map (arrow F f h) = f := by
  rcases f with ⟨b,f⟩
  change b = 𝟙 c at h
  subst b
  dsimp only [arrow, Grothendieck.ι]
  apply Grothendieck.ext _ _ (by rfl)
  simp

end SquareKit.Internal.PathTransport.GrothendieckVertical
