import SquareKit.SheafActionQuotientCech
import SquareKit.SheafActionQuotientDescentOverlap

/-! Recover pointwise torsor cocycles from independent overlap isomorphisms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SheafActionQuotient.Cech
open CategoryTheory SplitSheaf.Cech
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M X : Sheaf J (Type (max u v))}
variable {a : Action G M} {A : SplitSheaf.Ty X}

/-- Evaluate the actual overlap arrow at a pair of lifts. -/
def Datum.transport (d : Datum (a := a) A) (x : X.obj.Elements) (b c : A.family.obj x) :
    d.localObject.torsor.family.family.obj (SheafTorsor.Descent.point A x b) →
      d.localObject.torsor.family.family.obj (SheafTorsor.Descent.point A x c) :=
  d.overlap.hom.torsorArrow.iso.hom.app
    ((double A).obj.elementsMk x.obj ⟨⟨x.val,b⟩,c⟩)

/-- Diagonal and triple-overlap laws supply the pointwise identity and cocycle;
the local overlap arrow supplies naturality, equivariance and map preservation. -/
def Datum.toDescent (d : Datum (a := a) A) : Descent.Datum (a := a) A where
  localObject := d.localObject
  torsorDatum := {
    transport := d.transport
    identity x b p := congrArg (fun k => k.torsorArrow.iso.hom.app
      (SheafTorsor.Descent.point A x b) p) d.diagonal
    cocycle x b c e p := congrArg (fun k => k.torsorArrow.iso.hom.app
      ((triple A).obj.elementsMk x.obj ⟨⟨⟨x.val,b⟩,c⟩,e⟩) p) d.cocycle
    natural {x y} f b c p := by
      let k := SplitFunctionDiagram.pairArrow (SplitSheaf.tySub A (SplitSheaf.p A)).family
        (SplitFunctionDiagram.pairArrow A.family f b) c
      exact (NatTrans.naturality_apply d.overlap.hom.torsorArrow.iso.hom k p).symm
    equivariant x b c := d.overlap.hom.torsorArrow.equivariant
      ((double A).obj.elementsMk x.obj ⟨⟨x.val,b⟩,c⟩) }
  value_compatible x b c := d.overlap.hom.preserves
    ((double A).obj.elementsMk x.obj ⟨⟨x.val,b⟩,c⟩)

/-- The overlap square recovers compatibility of local equivariant maps
with every pointwise torsor transport. -/
def Map.toDescent {d e : Datum (a := a) A} (h : Map d e) :
    Descent.Map d.toDescent e.toDescent where
  torsorMap := {
    hom := h.localArrow.torsorArrow.iso.hom
    equivariant := h.localArrow.torsorArrow.equivariant
    transport x b c p := (congrArg (fun k => k.torsorArrow.iso.hom.app
      ((double A).obj.elementsMk x.obj ⟨⟨x.val,b⟩,c⟩) p) h.commutes).symm }
  preserves := h.localArrow.preserves

/-- The reverse identification is defined on every local object and arrow,
without a covering or effectiveness assumption. -/
def toDescent : Datum (a := a) A ⥤ Descent.Datum (a := a) A where
  obj := Datum.toDescent
  map := Map.toDescent
  map_id _ := Descent.Map.ext_hom _ _ rfl
  map_comp _ _ := Descent.Map.ext_hom _ _ rfl

end SquareKit.SheafActionQuotient.Cech
