import SquareKit.Internal.PathTransport.CechMatching
import Mathlib.CategoryTheory.Whiskering

/-! A coherent natural local evaluation gives a functor to independent matching. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {D : Diagram.{u,v}} {C : Type w} [Category.{u} C]
variable (L : C ⥤ D.localCategory) (η : L ⋙ D.first ≅ L ⋙ D.second)

/-- A matching cone keeps an actual natural overlap isomorphism. Its equations
are natural-isomorphism equalities, so their components include all arrows. -/
structure ConeLaws : Prop where
  diagonal : isoWhiskerRight η D.diagonal =
    isoWhiskerLeft L D.diagonalFirst ≪≫ (isoWhiskerLeft L D.diagonalSecond).symm
  cocycle : isoWhiskerRight η D.firstSecond ≪≫ isoWhiskerLeft L D.tripleMiddle ≪≫
      isoWhiskerRight η D.secondThird =
    isoWhiskerLeft L D.tripleFirst ≪≫ isoWhiskerRight η D.firstThird ≪≫
      isoWhiskerLeft L D.tripleLast

/-- Each input object receives its supplied local object and selected overlap;
input arrows retain the local functor's full action. -/
def coneFunctor (h : ConeLaws L η) : C ⥤ Datum D where
  obj c := {
    localObject := L.obj c
    overlap := η.app c
    diagonal := congrArg (fun e => e.hom.app c) h.diagonal
    cocycle := congrArg (fun e => e.hom.app c) h.cocycle }
  map f := ⟨L.map f, η.hom.naturality f⟩
  map_id c := Datum.Hom.ext _ _ (L.map_id c)
  map_comp f g := Datum.Hom.ext _ _ (L.map_comp f g)

@[simp] theorem coneFunctor_local (h : ConeLaws L η) :
    coneFunctor L η h ⋙ Datum.localFunctor = L := rfl

end SquareKit.Internal.PathTransport.CechMatching
