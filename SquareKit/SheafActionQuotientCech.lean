import SquareKit.SplitSheafCech
import SquareKit.SheafActionQuotient

/-! Independent quotient Čech data: a local object, overlap isomorphism and
its equations. No descended object or gluing interpretation is an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SheafActionQuotient.Cech
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M X : Sheaf J (Type (max u v))}
variable {a : Action G M}
open SplitSheaf.Cech

/-- Ordinary groupoid Čech data on a fixed split display. -/
structure Datum (A : SplitSheaf.Ty X) where
  localObject : Object a (SplitSheaf.Ext A)
  overlap : reindex localObject (first A) ≅ reindex localObject (second A)
  diagonal : overlap.hom.reindex (SplitSheaf.Cech.diagonal A) = Arrow.ident localObject
  cocycle : (overlap.hom.reindex (firstSecond A)).comp
      (overlap.hom.reindex (secondThird A)) = overlap.hom.reindex (firstThird A)

variable {A : SplitSheaf.Ty X}

/-- Local arrows with their actual commuting overlap square. -/
structure Map (d e : Datum (a := a) A) where
  localArrow : Arrow d.localObject e.localObject
  commutes : (localArrow.reindex (first A)).comp e.overlap.hom =
    d.overlap.hom.comp (localArrow.reindex (second A))

@[ext] theorem Map.ext {d e : Datum (a := a) A} (h k : Map d e)
    (he : h.localArrow = k.localArrow) : h = k := by
  cases h
  cases k
  cases he
  rfl

def Map.ident (d : Datum (a := a) A) : Map d d where
  localArrow := Arrow.ident d.localObject
  commutes := rfl

def Map.comp {d e r : Datum (a := a) A} (h : Map d e) (k : Map e r) : Map d r where
  localArrow := h.localArrow.comp k.localArrow
  commutes := by
    change (h.localArrow.reindex (first A)).comp
      ((k.localArrow.reindex (first A)).comp r.overlap.hom) = _
    rw [k.commutes]
    change ((h.localArrow.reindex (first A)).comp e.overlap.hom).comp
      (k.localArrow.reindex (second A)) = _
    rw [h.commutes]
    rfl

instance : Category (Datum (a := a) A) where
  Hom := Map
  id := Map.ident
  comp := Map.comp
  id_comp _ := Map.ext _ _ rfl
  comp_id _ := Map.ext _ _ rfl
  assoc _ _ _ := Map.ext _ _ rfl

/-- Inverting a local arrow preserves its overlap square. -/
def Map.inverse {d e : Datum (a := a) A} (h : Map d e) : Map e d where
  localArrow := h.localArrow.inverse
  commutes := by
    let f := h.localArrow.reindex (first A)
    let g := h.localArrow.reindex (second A)
    have hf : h.localArrow.inverse.reindex (first A) = f.toIso.inv := by
      apply SheafActionQuotient.Arrow.ext
      apply SheafTorsor.Arrow.ext
      rfl
    have hg : h.localArrow.inverse.reindex (second A) = g.toIso.inv := by
      apply SheafActionQuotient.Arrow.ext
      apply SheafTorsor.Arrow.ext
      rfl
    rw [hf, hg]
    change f.toIso.inv ≫ d.overlap.hom = e.overlap.hom ≫ g.toIso.inv
    apply (cancel_mono (C := Object a (double A)) g).1
    have hh : f ≫ e.overlap.hom = d.overlap.hom ≫ g := h.commutes
    rw [Category.assoc, ← hh]
    change f.toIso.inv ≫ f.toIso.hom ≫ e.overlap.hom =
      (e.overlap.hom ≫ g.toIso.inv) ≫ g.toIso.hom
    rw [f.toIso.inv_hom_id_assoc, Category.assoc, g.toIso.inv_hom_id,
      Category.comp_id]

instance : Groupoid (Datum (a := a) A) where
  inv := Map.inverse
  inv_comp h := by
    apply Map.ext
    exact h.localArrow.toIso.inv_hom_id
  comp_inv h := by
    apply Map.ext
    exact h.localArrow.toIso.hom_inv_id

/-- The forgetful functor retains the entire local quotient arrow. -/
def localFunctor : Datum (a := a) A ⥤ Object a (SplitSheaf.Ext A) where
  obj d := d.localObject
  map h := h.localArrow
  map_id _ := rfl
  map_comp _ _ := rfl

end SquareKit.SheafActionQuotient.Cech
