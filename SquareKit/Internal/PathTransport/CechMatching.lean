import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
import Mathlib.CategoryTheory.Groupoid

/-! Matching data on a truncated Čech diagram of groupoids. The diagram records
restriction functors and their endpoint comparisons. Objects and arrows are
specified locally; effectiveness is not part of the input. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- The part of a parameter diagram needed to state overlap matching. -/
structure Diagram where
  localCategory : Grpd.{u,u}
  doubleCategory : Grpd.{u,u}
  tripleCategory : Grpd.{u,u}
  first : localCategory ⥤ doubleCategory
  second : localCategory ⥤ doubleCategory
  diagonal : doubleCategory ⥤ localCategory
  firstSecond : doubleCategory ⥤ tripleCategory
  firstThird : doubleCategory ⥤ tripleCategory
  secondThird : doubleCategory ⥤ tripleCategory
  diagonalFirst : first ⋙ diagonal ≅ 𝟭 localCategory
  diagonalSecond : second ⋙ diagonal ≅ 𝟭 localCategory
  tripleFirst : first ⋙ firstSecond ≅ first ⋙ firstThird
  tripleMiddle : second ⋙ firstSecond ≅ first ⋙ secondThird
  tripleLast : second ⋙ firstThird ≅ second ⋙ secondThird

/-- A diagram whose endpoint comparisons come from strict restriction laws. -/
structure StrictDiagram where
  localCategory : Grpd.{u,u}
  doubleCategory : Grpd.{u,u}
  tripleCategory : Grpd.{u,u}
  first : localCategory ⥤ doubleCategory
  second : localCategory ⥤ doubleCategory
  diagonal : doubleCategory ⥤ localCategory
  firstSecond : doubleCategory ⥤ tripleCategory
  firstThird : doubleCategory ⥤ tripleCategory
  secondThird : doubleCategory ⥤ tripleCategory
  diagonalFirst : first ⋙ diagonal = 𝟭 localCategory
  diagonalSecond : second ⋙ diagonal = 𝟭 localCategory
  tripleFirst : first ⋙ firstSecond = first ⋙ firstThird
  tripleMiddle : second ⋙ firstSecond = first ⋙ secondThird
  tripleLast : second ⋙ firstThird = second ⋙ secondThird

def StrictDiagram.toDiagram (D : StrictDiagram.{u}) : Diagram.{u} where
  localCategory := D.localCategory
  doubleCategory := D.doubleCategory
  tripleCategory := D.tripleCategory
  first := D.first
  second := D.second
  diagonal := D.diagonal
  firstSecond := D.firstSecond
  firstThird := D.firstThird
  secondThird := D.secondThird
  diagonalFirst := eqToIso D.diagonalFirst
  diagonalSecond := eqToIso D.diagonalSecond
  tripleFirst := eqToIso D.tripleFirst
  tripleMiddle := eqToIso D.tripleMiddle
  tripleLast := eqToIso D.tripleLast

variable (D : Diagram.{u})

/-- A supplied local object with an actual overlap isomorphism and its laws. -/
structure Datum where
  localObject : D.localCategory
  overlap : D.first.obj localObject ≅ D.second.obj localObject
  diagonal : D.diagonal.map overlap.hom =
    D.diagonalFirst.hom.app localObject ≫ D.diagonalSecond.inv.app localObject
  cocycle : D.firstSecond.map overlap.hom ≫ D.tripleMiddle.hom.app localObject ≫
      D.secondThird.map overlap.hom =
    D.tripleFirst.hom.app localObject ≫ D.firstThird.map overlap.hom ≫
      D.tripleLast.hom.app localObject

/-- Equality of restrictions supplies the canonical overlap. Its coherence
uses only equality transport; no effectivity or faithfulness is assumed. -/
def StrictDiagram.equalDatum (D : StrictDiagram.{u}) (x : D.localCategory)
    (h : D.first.obj x = D.second.obj x) : Datum D.toDiagram where
  localObject := x
  overlap := eqToIso h
  diagonal := by
    simp only [StrictDiagram.toDiagram, eqToIso.hom, eqToIso.inv, eqToHom_app,
      eqToHom_map, eqToHom_trans]
  cocycle := by
    simp only [StrictDiagram.toDiagram, eqToIso.hom, eqToHom_app,
      eqToHom_map, eqToHom_trans]

namespace Datum
variable {D}

@[ext] theorem ext {d e : Datum D} (h : d.localObject = e.localObject)
    (hh : HEq d.overlap e.overlap) : d = e := by
  cases d; cases e
  cases h
  cases eq_of_heq hh
  rfl

/-- An arrow is its complete local action, with the overlap square. -/
structure Hom (d e : Datum D) where
  localArrow : d.localObject ⟶ e.localObject
  commutes : D.first.map localArrow ≫ e.overlap.hom =
    d.overlap.hom ≫ D.second.map localArrow

@[ext] theorem Hom.ext {d e : Datum D} (f g : Hom d e)
    (h : f.localArrow = g.localArrow) : f = g := by
  cases f; cases g; cases h; rfl

def Hom.id (d : Datum D) : Hom d d where
  localArrow := 𝟙 _
  commutes := by simp

def Hom.comp {d e f : Datum D} (g : Hom d e) (h : Hom e f) : Hom d f where
  localArrow := g.localArrow ≫ h.localArrow
  commutes := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, h.commutes,
      ← Category.assoc, g.commutes, Category.assoc]

instance : Category (Datum D) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext _ _ (Category.id_comp _)
  comp_id _ := Hom.ext _ _ (Category.comp_id _)
  assoc _ _ _ := Hom.ext _ _ (Category.assoc _ _ _)

def Hom.inverse {d e : Datum D} (f : d ⟶ e) : e ⟶ d where
  localArrow := inv f.localArrow
  commutes := by
    apply (cancel_mono (D.second.map f.localArrow)).1
    simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id]
    rw [← f.commutes, ← Category.assoc, ← Functor.map_comp]
    simp

instance : Groupoid (Datum D) where
  inv := Hom.inverse
  inv_comp _f := Hom.ext _ _ (IsIso.inv_hom_id _)
  comp_inv _f := Hom.ext _ _ (IsIso.hom_inv_id _)

@[simp] theorem comp_localArrow {d e f : Datum D} (h : d ⟶ e) (k : e ⟶ f) :
    (h ≫ k).localArrow = h.localArrow ≫ k.localArrow := rfl

@[simp] theorem id_localArrow (d : Datum D) : (𝟙 d : d ⟶ d).localArrow = 𝟙 d.localObject := rfl

@[simp] theorem eqToHom_localArrow {d e : Datum D} (h : d = e) :
    (eqToHom h).localArrow = eqToHom (congrArg Datum.localObject h) := by
  cases h; rfl

/-- The forgetful functor keeps every selected local arrow. -/
def localFunctor : Datum D ⥤ D.localCategory where
  obj d := d.localObject
  map f := f.localArrow
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (localFunctor (D := D)).Faithful where
  map_injective := fun h => Hom.ext _ _ h

/-- Equality of local arrows is both preserved and reflected. -/
theorem localArrow_eq_iff {d e : Datum D} (f g : d ⟶ e) :
    f.localArrow = g.localArrow ↔ f = g := ⟨Hom.ext _ _, congrArg Hom.localArrow⟩

end Datum

/-- A functor with equal overlap restrictions has a canonical matching lift. -/
def StrictDiagram.equalFunctor (D : StrictDiagram.{u}) {C : Type u} [Category.{u} C]
    (F : C ⥤ D.localCategory) (h : F ⋙ D.first = F ⋙ D.second) :
    C ⥤ Datum D.toDiagram where
  obj x := D.equalDatum (F.obj x) (Functor.congr_obj h x)
  map f := ⟨F.map f, by
    have hh := (eqToHom h).naturality f
    simpa only [eqToHom_app, StrictDiagram.equalDatum, StrictDiagram.toDiagram,
      eqToIso.hom, Functor.comp_map, Functor.comp_obj] using hh⟩
  map_id x := Datum.Hom.ext _ _ (F.map_id x)
  map_comp f g := Datum.Hom.ext _ _ (F.map_comp f g)

end SquareKit.Internal.PathTransport.CechMatching
