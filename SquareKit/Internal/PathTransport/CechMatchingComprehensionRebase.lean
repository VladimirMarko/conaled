import SquareKit.Internal.PathTransport.CechMatching

/-! Changing the local representative of independent matching data transports
its overlap and both equations by the supplied isomorphism. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace Datum
variable {D : Diagram.{u,v}}

def rebaseOverlap (d : Datum D) {y : D.localCategory} (i : d.localObject ≅ y) :
    D.first.obj y ≅ D.second.obj y :=
  (D.first.mapIso i).symm ≪≫ d.overlap ≪≫ D.second.mapIso i

private theorem rebase_diagonal (d : Datum D) {y : D.localCategory}
    (i : d.localObject ≅ y) :
    D.diagonal.map (rebaseOverlap d i).hom =
      D.diagonalFirst.hom.app y ≫ D.diagonalSecond.inv.app y := by
  dsimp only [rebaseOverlap, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    Functor.mapIso_hom]
  rw [Functor.map_comp, Functor.map_comp, d.diagonal]
  have h1 := D.diagonalFirst.hom.naturality i.inv
  have h2 := D.diagonalSecond.inv.naturality i.hom
  dsimp only [Functor.comp_map, Functor.id_map] at h1 h2
  simp only [← Category.assoc]
  rw [h1]
  simp only [Category.assoc]
  rw [← h2]
  simp

private theorem rebase_cocycle (d : Datum D) {y : D.localCategory}
    (i : d.localObject ≅ y) :
    D.firstSecond.map (rebaseOverlap d i).hom ≫ D.tripleMiddle.hom.app y ≫
      D.secondThird.map (rebaseOverlap d i).hom =
    D.tripleFirst.hom.app y ≫ D.firstThird.map (rebaseOverlap d i).hom ≫
      D.tripleLast.hom.app y := by
  dsimp only [rebaseOverlap, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  have hm := D.tripleMiddle.hom.naturality i.hom
  have hf := D.tripleFirst.hom.naturality i.inv
  have hl := D.tripleLast.hom.naturality i.hom
  dsimp only [Functor.comp_map] at hm hf hl
  rw [← Category.assoc (D.firstSecond.map (D.second.map i.hom)), hm]
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.hom_inv_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [D.first.map_id, D.secondThird.map_id, Category.id_comp]
  rw [← Category.assoc (D.tripleFirst.hom.app y), ← hf]
  simp only [Category.assoc]
  rw [hl]
  have hd := congrArg (fun k => D.firstSecond.map (D.first.map i.inv) ≫ k ≫
    D.secondThird.map (D.second.map i.hom)) d.cocycle
  simpa only [Category.assoc] using hd

def rebase (d : Datum D) {y : D.localCategory} (i : d.localObject ≅ y) : Datum D where
  localObject := y
  overlap := rebaseOverlap d i
  diagonal := rebase_diagonal d i
  cocycle := rebase_cocycle d i

def rebaseArrow (d : Datum D) {y : D.localCategory} (i : d.localObject ≅ y) :
    d ⟶ rebase d i where
  localArrow := i.hom
  commutes := by
    dsimp only [rebase, rebaseOverlap, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Functor.mapIso_inv]
    rw [← Category.assoc, ← D.first.map_comp]
    simp

def rebaseIso (d : Datum D) {y : D.localCategory} (i : d.localObject ≅ y) :
    d ≅ rebase d i := asIso (rebaseArrow d i)

@[simp] theorem rebaseIso_local (d : Datum D) {y : D.localCategory}
    (i : d.localObject ≅ y) : (rebaseIso d i).hom.localArrow = i.hom := rfl

end Datum
end SquareKit.Internal.PathTransport.CechMatching
