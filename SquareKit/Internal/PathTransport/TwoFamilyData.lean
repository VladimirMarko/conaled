import SquareKit.Internal.PathTransport.TwoFamilyHigherReindex

/-! Shared extensionality for actual higher total objects, arrows and cells.
The dependent boundaries are explicit; no genuine cell is discarded. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
/-- Equality of both observations determines a total arrow across equal endpoints. -/
theorem total_hom_hext {C : Type*} [Bicategory C] [Strict C] (H : Family C)
    {x x' y y' : Total H} (hx : x = x') (hy : y = y')
    (p : Hom H x y) (q : Hom H x' y') (hb : HEq p.base q.base)
    (hf : HEq p.fiber q.fiber) : HEq p q := by
  subst x'
  subst y'
  apply heq_of_eq
  exact Pseudofunctor.CoGrothendieck.ext (eq_of_heq hb) hf
/-- Equality of both observations determines a total cell across equal boundaries. -/
theorem total_cell_hext {C : Type*} [Bicategory C] [Strict C] (H : Family C)
    {x x' y y' : Total H} (hx : x = x') (hy : y = y')
    {p q : Hom H x y} {p' q' : Hom H x' y'} (hp : HEq p p') (hq : HEq q q')
    (α : p ⟶ q) (β : p' ⟶ q') (hb : HEq α.base β.base)
    (hf : HEq α.fiber β.fiber) : HEq α β := by
  subst x'
  subst y'
  cases eq_of_heq hp
  cases eq_of_heq hq
  apply heq_of_eq
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (eq_of_heq hb)
  exact eq_of_heq (HEq.trans hf (comp_eqToHom_heq _ _).symm)

/-- Equality of base and fiber observations determines a total object. -/
theorem total_obj_hext {C : Type*} [Bicategory C] [Strict C] (H : Family C)
    {x y : Total H} (hb : x.base = y.base) (hf : HEq x.fiber y.fiber) : x = y := by
  rcases x with ⟨x,a⟩
  rcases y with ⟨y,b⟩
  dsimp only at hb hf
  subst y
  cases eq_of_heq hf
  rfl

end SquareKit.Internal.PathTransport.TwoFamily
