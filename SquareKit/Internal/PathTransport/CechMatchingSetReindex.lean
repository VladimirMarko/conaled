import SquareKit.Internal.PathTransport.CechMatchingSetFamily
import SquareKit.Internal.PathTransport.CechMatchingMap

/-! Set matching is unchanged by pulling its restriction diagram along a strict map. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.SetFamily
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D E : StrictDiagram.{u,u}} (S : StrictMap D E)
variable (L : E.localCategory ⥤ Type u) (O : E.doubleCategory ⥤ Type u)
variable (first : L ⟶ E.first ⋙ O) (second : L ⟶ E.second ⋙ O)

def pullFirst : S.localMap ⋙ L ⟶ D.first ⋙ S.doubleMap ⋙ O :=
  whiskerLeft S.localMap first ≫ eqToHom (congrArg (· ⋙ O) S.first)

def pullSecond : S.localMap ⋙ L ⟶ D.second ⋙ S.doubleMap ⋙ O :=
  whiskerLeft S.localMap second ≫ eqToHom (congrArg (· ⋙ O) S.second)

theorem pull_condition (d : Datum D.toDiagram) (x : L.obj (S.localMap.obj d.localObject)) :
    (S.doubleMap ⋙ O).map d.overlap.hom ((pullFirst S L O first).app d.localObject x) =
      (pullSecond S L O second).app d.localObject x ↔
    O.map (S.overlap d).hom (first.app (S.localMap.obj d.localObject) x) =
      second.app (S.localMap.obj d.localObject) x := by
  have h1 : (pullFirst S L O first).app d.localObject =
      first.app (S.localMap.obj d.localObject) ≫
        O.map (eqToHom (Functor.congr_obj S.first d.localObject)) := by
    simp only [pullFirst, NatTrans.comp_app, whiskerLeft_app, eqToHom_app, eqToHom_map]
  have h2 : (pullSecond S L O second).app d.localObject =
      second.app (S.localMap.obj d.localObject) ≫
        O.map (eqToHom (Functor.congr_obj S.second d.localObject)) := by
    simp only [pullSecond, NatTrans.comp_app, whiskerLeft_app, eqToHom_app, eqToHom_map]
  rw [h1, h2]
  simp only [StrictMap.overlap, Iso.trans_hom, eqToIso.hom, Iso.symm_hom,
    eqToIso.inv, Functor.mapIso_hom, Functor.comp_map, Functor.map_comp]
  dsimp only [StrictDiagram.toDiagram] at *
  constructor
  · intro hh
    have hi := congrArg (fun z => O.map (eqToHom (Functor.congr_obj S.second d.localObject).symm) z) hh
    simpa [Functor.map_comp, types_comp_apply] using hi
  · intro hh
    have hi := congrArg (fun z => O.map (eqToHom (Functor.congr_obj S.second d.localObject)) z) hh
    simpa [Functor.map_comp, types_comp_apply] using hi

/-- Pullback matching retains the exact local value and its overlap condition. -/
def pullEquiv (d : Datum D.toDiagram) :
    Fiber (S.localMap ⋙ L) (S.doubleMap ⋙ O)
      (pullFirst S L O first) (pullSecond S L O second) d ≃
      Fiber L O first second (S.mapDatum d) where
  toFun x := ⟨x.val, (pull_condition S L O first second d x.val).mp x.property⟩
  invFun x := ⟨x.val, (pull_condition S L O first second d x.val).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identification is natural in arbitrary matching-context arrows. -/
def pullFamilyIso :
    family (S.localMap ⋙ L) (S.doubleMap ⋙ O)
      (pullFirst S L O first) (pullSecond S L O second) ≅
      S.functor ⋙ family L O first second :=
  NatIso.ofComponents (fun d => (pullEquiv S L O first second d).toIso) (by
    intro d e f
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl)

@[simp] theorem pullEquiv_value (d : Datum D.toDiagram)
    (x : Fiber (S.localMap ⋙ L) (S.doubleMap ⋙ O)
      (pullFirst S L O first) (pullSecond S L O second) d) :
    HEq (pullEquiv S L O first second d x).val x.val := HEq.rfl

end SquareKit.Internal.PathTransport.CechMatching.SetFamily
