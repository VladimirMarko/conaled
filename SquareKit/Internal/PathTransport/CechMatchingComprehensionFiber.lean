import SquareKit.Internal.PathTransport.CechMatchingComprehensionDiagram

/-! Relative matching data expose the local fiber object, the actual selected
overlap and its equations over a supplied base datum. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D : StrictDiagram.{u,u}} (A : FamilyData D) (h : A.Coherence)

abbrev liftLocal (d : Datum D.toDiagram) (x : A.localFamily.obj d.localObject) : A.localTotal :=
  ⟨d.localObject, x⟩

structure Fiber (d : Datum D.toDiagram) where
  localFiber : A.localFamily.obj d.localObject
  overlap : A.firstMap.obj (liftLocal A d localFiber) ≅ A.secondMap.obj (liftLocal A d localFiber)
  diagonal : A.diagonalMap.map overlap.hom =
    (eqToHom h.diagonalFirst).app (liftLocal A d localFiber) ≫
      (eqToHom h.diagonalSecond.symm).app (liftLocal A d localFiber)
  cocycle : A.firstSecondMap.map overlap.hom ≫
      (eqToHom h.tripleMiddle).app (liftLocal A d localFiber) ≫
        A.secondThirdMap.map overlap.hom =
    (eqToHom h.tripleFirst).app (liftLocal A d localFiber) ≫
      A.firstThirdMap.map overlap.hom ≫
        (eqToHom h.tripleLast).app (liftLocal A d localFiber)
  base_overlap : overlap.hom.base = d.overlap.hom

namespace Fiber
variable {A h} {d : Datum D.toDiagram}

def datum (x : Fiber A h d) : Datum (A.total h).toDiagram where
  localObject := liftLocal A d x.localFiber
  overlap := x.overlap
  diagonal := x.diagonal
  cocycle := x.cocycle

theorem projection_datum (x : Fiber A h d) : (A.projection h).mapDatum x.datum = d := by
  apply Datum.ext (d := (A.projection h).mapDatum x.datum) (e := d)
    (show ((A.projection h).mapDatum x.datum).localObject = d.localObject from rfl)
  apply heq_of_eq
  apply Iso.ext
  simp only [StrictMap.mapDatum, StrictMap.overlap, FamilyData.projection,
    Iso.symm_hom, eqToIso.hom, eqToIso.inv, Iso.trans_hom, Functor.mapIso_hom,
    eqToHom_refl, Category.id_comp, Category.comp_id, Grothendieck.forget_map]
  exact x.base_overlap

/-- The local total arrow is vertical and satisfies the actual overlap square. -/
structure Hom (x y : Fiber A h d) where
  matchingArrow : x.datum ⟶ y.datum
  vertical : matchingArrow.localArrow.base = 𝟙 d.localObject

@[ext] theorem Hom.ext {x y : Fiber A h d} (f g : Hom x y)
    (hh : f.matchingArrow = g.matchingArrow) : f = g := by
  cases f; cases g; cases hh; rfl

instance : Category (Fiber A h d) where
  Hom := Hom
  id x := ⟨𝟙 x.datum, rfl⟩
  comp f g := ⟨f.matchingArrow ≫ g.matchingArrow, by
    change f.matchingArrow.localArrow.base ≫ g.matchingArrow.localArrow.base = _
    rw [f.vertical, g.vertical]
    exact Category.id_comp (𝟙 d.localObject)⟩
  id_comp f := Hom.ext _ _ (Category.id_comp _)
  comp_id f := Hom.ext _ _ (Category.comp_id _)
  assoc f g k := Hom.ext _ _ (Category.assoc _ _ _)

def Hom.inverse {x y : Fiber A h d} (f : x ⟶ y) : y ⟶ x where
  matchingArrow := inv f.matchingArrow
  vertical := by
    change (Datum.localFunctor ⋙ Grothendieck.forget
      (A.localFamily ⋙ Grpd.forgetToCat)).map (inv f.matchingArrow) = 𝟙 d.localObject
    rw [Functor.map_inv]
    change inv f.matchingArrow.localArrow.base = 𝟙 d.localObject
    rw [f.vertical]
    exact IsIso.inv_id

instance : Groupoid (Fiber A h d) where
  inv := Hom.inverse
  inv_comp f := Hom.ext _ _ (IsIso.inv_hom_id f.matchingArrow)
  comp_inv f := Hom.ext _ _ (IsIso.hom_inv_id f.matchingArrow)

/-- Recover the exposed relative data from a total datum with exactly this base. -/
def ofDatum (e : Datum (A.total h).toDiagram)
    (hd : (A.projection h).mapDatum e = d) : Fiber A h d := by
  subst d
  exact {
    localFiber := e.localObject.fiber
    overlap := e.overlap
    diagonal := e.diagonal
    cocycle := e.cocycle
    base_overlap := by
      simp only [StrictMap.mapDatum, StrictMap.overlap, FamilyData.projection,
        Iso.symm_hom, eqToIso.hom, eqToIso.inv, Iso.trans_hom, Functor.mapIso_hom,
        eqToHom_refl, Category.id_comp, Category.comp_id, Grothendieck.forget_map] }

@[simp] theorem datum_ofDatum (e : Datum (A.total h).toDiagram)
    (hd : (A.projection h).mapDatum e = d) : (ofDatum e hd).datum = e := by
  subst d
  apply Datum.ext rfl
  exact HEq.rfl


@[simp] theorem localFiber_ofDatum (e : Datum (A.total h).toDiagram)
    (hd : (A.projection h).mapDatum e = d) :
    HEq (ofDatum e hd).localFiber e.localObject.fiber := by
  subst d
  rfl

theorem datum_injective : Function.Injective (datum (A := A) (h := h) (d := d)) := by
  intro x y he
  cases x with
  | mk xx xo xd xc xb =>
    cases y with
    | mk yy yo yd yc yb =>
      have hl := congrArg Datum.localObject he
      have hf : xx = yy := by
        injection hl
      subst yy
      have hi : xo = yo := by
        have depcongr : ∀ {a b : Datum (A.total h).toDiagram}, a = b → HEq a.overlap b.overlap := by
          intro a b hab
          cases hab
          rfl
        exact eq_of_heq (depcongr he)
      subst yo
      rfl


@[simp] theorem ofDatum_datum (x : Fiber A h d) :
    ofDatum x.datum (projection_datum x) = x :=
  datum_injective (datum_ofDatum _ _)

def forget : Fiber A h d ⥤ Datum (A.total h).toDiagram where
  obj := datum
  map f := f.matchingArrow
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (forget (A := A) (h := h) (d := d)).Faithful where
  map_injective := Hom.ext _ _

end Fiber
end SquareKit.Internal.PathTransport.CechMatching.Comprehension
