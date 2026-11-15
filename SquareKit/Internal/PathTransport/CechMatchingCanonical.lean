import SquareKit.Internal.PathTransport.CechMatchingMapComposition

/-! Canonical matching restrictions commute with maps of strict diagrams. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.StrictMap
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {D E : StrictDiagram.{u,v}} {C : Type v} [Category.{u} C]

private theorem map_equalDatum (F : StrictMap D E) (R : C ⥤ D.localCategory)
    (hD : R ⋙ D.first = R ⋙ D.second)
    (hE : (R ⋙ F.localMap) ⋙ E.first = (R ⋙ F.localMap) ⋙ E.second) (x : C) :
    F.functor.obj ((D.equalFunctor R hD).obj x) =
      (E.equalFunctor (R ⋙ F.localMap) hE).obj x := by
  refine Datum.ext rfl ?_
  apply heq_of_eq
  apply Iso.ext
  simp only [functor, mapDatum, overlap, StrictDiagram.equalFunctor, StrictDiagram.equalDatum,
    Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, Functor.mapIso_hom,
    eqToHom_map, eqToHom_trans]

/-- The comparison includes actual local arrows and the canonical overlaps. -/
theorem equalFunctor_map (F : StrictMap D E) (R : C ⥤ D.localCategory)
    (hD : R ⋙ D.first = R ⋙ D.second)
    (hE : (R ⋙ F.localMap) ⋙ E.first = (R ⋙ F.localMap) ⋙ E.second) :
    D.equalFunctor R hD ⋙ F.functor = E.equalFunctor (R ⋙ F.localMap) hE := by
  refine CategoryTheory.Functor.ext (map_equalDatum F R hD hE) ?_
  intro x y f
  apply Datum.Hom.ext
  simp only [Functor.comp_map, functor, StrictDiagram.equalFunctor,
    Datum.comp_localArrow, Datum.eqToHom_localArrow, eqToHom_refl,
    Category.id_comp, Category.comp_id]

end SquareKit.Internal.PathTransport.CechMatching.StrictMap
