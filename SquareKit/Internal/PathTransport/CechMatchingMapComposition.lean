import SquareKit.Internal.PathTransport.CechMatchingMap

/-! Identity and composition of maps on independent matching data. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.StrictMap
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {D E K : StrictDiagram.{u,v}}

@[ext] theorem ext (F G : StrictMap D E) (h0 : F.localMap = G.localMap)
    (h1 : F.doubleMap = G.doubleMap) (h2 : F.tripleMap = G.tripleMap) : F = G := by
  cases F; cases G
  cases h0; cases h1; cases h2
  rfl

def id (D : StrictDiagram.{u,v}) : StrictMap D D where
  localMap := 𝟭 _
  doubleMap := 𝟭 _
  tripleMap := 𝟭 _
  first := rfl
  second := rfl
  diagonal := rfl
  firstSecond := rfl
  firstThird := rfl
  secondThird := rfl

def comp (F : StrictMap D E) (G : StrictMap E K) : StrictMap D K where
  localMap := F.localMap ⋙ G.localMap
  doubleMap := F.doubleMap ⋙ G.doubleMap
  tripleMap := F.tripleMap ⋙ G.tripleMap
  first := by rw [Functor.assoc, G.first, ← Functor.assoc, F.first, Functor.assoc]
  second := by rw [Functor.assoc, G.second, ← Functor.assoc, F.second, Functor.assoc]
  diagonal := by rw [Functor.assoc, G.diagonal, ← Functor.assoc, F.diagonal, Functor.assoc]
  firstSecond := by rw [Functor.assoc, G.firstSecond, ← Functor.assoc, F.firstSecond, Functor.assoc]
  firstThird := by rw [Functor.assoc, G.firstThird, ← Functor.assoc, F.firstThird, Functor.assoc]
  secondThird := by rw [Functor.assoc, G.secondThird, ← Functor.assoc, F.secondThird, Functor.assoc]

theorem mapDatum_id (d : Datum D.toDiagram) : (id D).mapDatum d = d := by
  refine Datum.ext (d := _) (e := _) ?_ ?_
  · rfl
  apply heq_of_eq
  apply Iso.ext
  simp only [mapDatum, overlap, id, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    eqToIso.inv, Functor.mapIso_hom, Functor.id_map, eqToHom_refl, Category.id_comp]
  exact Category.comp_id _

theorem functor_id : (id D).functor = 𝟭 (Datum D.toDiagram) := by
  refine CategoryTheory.Functor.ext (mapDatum_id) ?_
  intro d e f
  apply Datum.Hom.ext
  simp [functor, mapDatum, id]

theorem mapDatum_comp (F : StrictMap D E) (G : StrictMap E K) (d : Datum D.toDiagram) :
    (F.comp G).mapDatum d = G.mapDatum (F.mapDatum d) := by
  refine Datum.ext (d := _) (e := _) ?_ ?_
  · rfl
  apply heq_of_eq
  apply Iso.ext
  simp only [mapDatum, overlap, comp, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    eqToIso.inv, Functor.mapIso_hom, Functor.comp_map, Functor.map_comp, eqToHom_map,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

theorem functor_comp (F : StrictMap D E) (G : StrictMap E K) :
    (F.comp G).functor = F.functor ⋙ G.functor := by
  refine CategoryTheory.Functor.ext (mapDatum_comp F G) ?_
  intro d e f
  apply Datum.Hom.ext
  simp only [functor, Functor.comp_map, comp, Datum.comp_localArrow, Datum.eqToHom_localArrow,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Strict inverse parameter diagrams induce inverse matching functors. -/
def equivalence (F : StrictMap D E) (G : StrictMap E D)
    (hFG : F.comp G = id D) (hGF : G.comp F = id E) :
    Datum D.toDiagram ≌ Datum E.toDiagram where
  functor := F.functor
  inverse := G.functor
  unitIso := eqToIso (by rw [← functor_comp, hFG, functor_id])
  counitIso := eqToIso (by rw [← functor_comp, hGF, functor_id])
  functor_unitIso_comp x := by
    simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans, eqToHom_refl]

end SquareKit.Internal.PathTransport.CechMatching.StrictMap
