import SquareKit.Internal.PathTransport.GrothendieckPreComparison

/-! Reindexing is fully faithful on arrows over a prescribed base arrow. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GrothendieckPreFiber
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (F : D ⥤ Cat.{u,u}) (S : C ⥤ D)
variable {x y : Grothendieck (S ⋙ F)}

def lift (b : x.base ⟶ y.base)
    (f : (Grothendieck.pre F S).obj x ⟶ (Grothendieck.pre F S).obj y)
    (h : f.base = S.map b) : x ⟶ y := by
  rcases f with ⟨a,f⟩
  change a = S.map b at h
  subst a
  exact ⟨b,f⟩

@[simp] theorem lift_base (b : x.base ⟶ y.base)
    (f : (Grothendieck.pre F S).obj x ⟶ (Grothendieck.pre F S).obj y)
    (h : f.base = S.map b) : (lift F S b f h).base = b := by
  rcases f with ⟨a,f⟩
  change a = S.map b at h
  subst a
  rfl

@[simp] theorem map_lift (b : x.base ⟶ y.base)
    (f : (Grothendieck.pre F S).obj x ⟶ (Grothendieck.pre F S).obj y)
    (h : f.base = S.map b) : (Grothendieck.pre F S).map (lift F S b f h) = f := by
  rcases f with ⟨a,f⟩
  change a = S.map b at h
  subst a
  rfl

theorem map_injective_of_base (f g : x ⟶ y) (hb : f.base = g.base)
    (hh : (Grothendieck.pre F S).map f = (Grothendieck.pre F S).map g) : f = g := by
  rcases f with ⟨fb,ff⟩
  rcases g with ⟨gb,gf⟩
  change fb = gb at hb
  subst gb
  change (⟨S.map fb, ff⟩ : Grothendieck.Hom ((Grothendieck.pre F S).obj x)
    ((Grothendieck.pre F S).obj y)) = ⟨S.map fb, gf⟩ at hh
  have hf : ff = gf := by injection hh
  cases hf
  rfl

end SquareKit.Internal.PathTransport.GrothendieckPreFiber
