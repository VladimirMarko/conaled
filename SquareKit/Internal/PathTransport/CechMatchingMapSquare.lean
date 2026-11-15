import SquareKit.Internal.PathTransport.CechMatchingMap

/-! A mapped overlap square is the image of the original square, with its endpoint transports. -/
namespace SquareKit.Internal.PathTransport.CechMatching
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {D E : StrictDiagram.{u,v}} (F : StrictMap D E)
variable {d e : Datum D.toDiagram} (f : d.localObject ⟶ e.localObject)

theorem StrictMap.square_iff :
    E.first.map (F.localMap.map f) ≫ (F.overlap e).hom =
      (F.overlap d).hom ≫ E.second.map (F.localMap.map f) ↔
    F.doubleMap.map (D.first.map f ≫ e.overlap.hom) =
      F.doubleMap.map (d.overlap.hom ≫ D.second.map f) := by
  have h0 := Functor.congr_hom F.first f
  have h1 := Functor.congr_hom F.second f
  dsimp only [Functor.comp_map] at h0 h1
  rw [h0, h1]
  dsimp only [StrictMap.overlap, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    Functor.mapIso_hom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [cancel_epi]
  simp only [← Category.assoc]
  rw [cancel_mono]
  simp only [Functor.map_comp]

end SquareKit.Internal.PathTransport.CechMatching
