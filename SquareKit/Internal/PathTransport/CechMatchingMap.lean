import SquareKit.Internal.PathTransport.CechMatching

/-! Change of a strict parameter diagram acts on independently supplied
matching data, including the chosen overlap and local arrows. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- A map of the truncated strict diagrams. The equations concern restriction
functors, rather than assumptions about their categories of matching data. -/
structure StrictMap (D E : StrictDiagram.{u}) where
  localMap : D.localCategory ⥤ E.localCategory
  doubleMap : D.doubleCategory ⥤ E.doubleCategory
  tripleMap : D.tripleCategory ⥤ E.tripleCategory
  first : localMap ⋙ E.first = D.first ⋙ doubleMap
  second : localMap ⋙ E.second = D.second ⋙ doubleMap
  diagonal : doubleMap ⋙ E.diagonal = D.diagonal ⋙ localMap
  firstSecond : doubleMap ⋙ E.firstSecond = D.firstSecond ⋙ tripleMap
  firstThird : doubleMap ⋙ E.firstThird = D.firstThird ⋙ tripleMap
  secondThird : doubleMap ⋙ E.secondThird = D.secondThird ⋙ tripleMap

namespace StrictMap
variable {D E : StrictDiagram.{u}} (F : StrictMap D E)

def overlap (d : Datum D.toDiagram) :
    E.first.obj (F.localMap.obj d.localObject) ≅
      E.second.obj (F.localMap.obj d.localObject) :=
  eqToIso (Functor.congr_obj F.first d.localObject) ≪≫ F.doubleMap.mapIso d.overlap ≪≫
    (eqToIso (Functor.congr_obj F.second d.localObject)).symm

private theorem diagonal_law (d : Datum D.toDiagram) :
    E.diagonal.map (F.overlap d).hom =
      (eqToHom E.diagonalFirst).app (F.localMap.obj d.localObject) ≫
        (eqToHom E.diagonalSecond.symm).app (F.localMap.obj d.localObject) := by
  dsimp only [overlap, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    Functor.mapIso_hom]
  simp only [Functor.map_comp, eqToHom_map, eqToHom_app]
  have h := Functor.congr_hom F.diagonal d.overlap.hom
  dsimp only [Functor.comp_map] at h
  rw [h]
  have hd := congrArg F.localMap.map d.diagonal
  simp only [StrictDiagram.toDiagram, eqToIso.hom, eqToIso.inv, eqToHom_app,
    eqToHom_map, eqToHom_trans] at hd
  rw [hd]
  simp only [eqToHom_trans]

private theorem cocycle_law (d : Datum D.toDiagram) :
    E.firstSecond.map (F.overlap d).hom ≫
      (eqToHom E.tripleMiddle).app (F.localMap.obj d.localObject) ≫
        E.secondThird.map (F.overlap d).hom =
      (eqToHom E.tripleFirst).app (F.localMap.obj d.localObject) ≫
        E.firstThird.map (F.overlap d).hom ≫
          (eqToHom E.tripleLast).app (F.localMap.obj d.localObject) := by
  dsimp only [overlap, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    Functor.mapIso_hom]
  simp only [Functor.map_comp, eqToHom_map, eqToHom_app]
  have h01 := Functor.congr_hom F.firstSecond d.overlap.hom
  have h02 := Functor.congr_hom F.firstThird d.overlap.hom
  have h12 := Functor.congr_hom F.secondThird d.overlap.hom
  dsimp only [Functor.comp_map] at h01 h02 h12
  rw [h01, h02, h12]
  have hd := congrArg F.tripleMap.map d.cocycle
  simp only [StrictDiagram.toDiagram, eqToIso.hom, eqToHom_app,
    Functor.map_comp, eqToHom_map] at hd
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  let e0 := (congrArg E.firstSecond.obj (Functor.congr_obj F.first d.localObject)).trans
    (Functor.congr_obj F.firstSecond (D.first.obj d.localObject))
  let e2 := ((congrArg E.secondThird.obj (Functor.congr_obj F.second d.localObject)).trans
    (Functor.congr_obj F.secondThird (D.second.obj d.localObject))).symm
  have hh := congrArg (fun k => eqToHom e0 ≫ k ≫ eqToHom e2) hd
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans] using hh

/-- Both Čech equations follow from the supplied datum and diagram squares. -/
def mapDatum (d : Datum D.toDiagram) : Datum E.toDiagram where
  localObject := F.localMap.obj d.localObject
  overlap := F.overlap d
  diagonal := F.diagonal_law d
  cocycle := F.cocycle_law d

private theorem map_commutes {d e : Datum D.toDiagram} (f : d ⟶ e) :
    E.first.map (F.localMap.map f.localArrow) ≫ (F.overlap e).hom =
      (F.overlap d).hom ≫ E.second.map (F.localMap.map f.localArrow) := by
  have h0 := Functor.congr_hom F.first f.localArrow
  have h1 := Functor.congr_hom F.second f.localArrow
  dsimp only [Functor.comp_map] at h0 h1
  rw [h0, h1]
  dsimp only [overlap, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    Functor.mapIso_hom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hh : D.first.map f.localArrow ≫ e.overlap.hom =
      d.overlap.hom ≫ D.second.map f.localArrow := f.commutes
  rw [← Functor.map_comp_assoc, hh, Functor.map_comp]
  simp only [Category.assoc]

/-- Change of diagram preserves the selected local arrow and overlap square. -/
def functor : Datum D.toDiagram ⥤ Datum E.toDiagram where
  obj := F.mapDatum
  map f := ⟨F.localMap.map f.localArrow, F.map_commutes f⟩
  map_id x := Datum.Hom.ext _ _ (F.localMap.map_id x.localObject)
  map_comp f g := Datum.Hom.ext _ _ (F.localMap.map_comp f.localArrow g.localArrow)

/-- Comprehension projections and substitutions retain their exact local action. -/
theorem functor_local : F.functor ⋙ Datum.localFunctor =
    Datum.localFunctor ⋙ F.localMap := rfl

end StrictMap
end SquareKit.Internal.PathTransport.CechMatching
