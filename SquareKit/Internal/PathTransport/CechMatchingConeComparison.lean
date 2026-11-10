import SquareKit.Internal.PathTransport.CechMatchingCone

/-! Selected local isomorphisms satisfying the overlap square compare full matching cones. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {D : Diagram.{u,v}} {C : Type w} [Category.{u} C]
variable {L K : C ⥤ D.localCategory}
variable {η : L ⋙ D.first ≅ L ⋙ D.second} {θ : K ⋙ D.first ≅ K ⋙ D.second}
variable (hL : ConeLaws L η) (hK : ConeLaws K θ) (e : L ≅ K)
variable (square : isoWhiskerRight e D.first ≪≫ θ = η ≪≫ isoWhiskerRight e D.second)

def coneComparison : coneFunctor L η hL ≅ coneFunctor K θ hK :=
  NatIso.ofComponents (fun c => asIso (show (coneFunctor L η hL).obj c ⟶
      (coneFunctor K θ hK).obj c from {
    localArrow := e.hom.app c
    commutes := congrArg (fun k => k.hom.app c) square })) (by
      intro x y f
      apply Datum.Hom.ext
      exact e.hom.naturality f)

@[simp] theorem coneComparison_local (c : C) :
    ((coneComparison hL hK e square).hom.app c).localArrow = e.hom.app c := rfl

/-- Compare a precomposed canonical restriction with a supplied matching cone. -/
def precomposedCanonicalComparison {D : StrictDiagram.{u,v}}
    {B : Type w} [Category.{u} B] (R : C ⥤ B) (F : B ⥤ D.localCategory)
    (hF : F ⋙ D.first = F ⋙ D.second)
    (L : C ⥤ D.localCategory) (θ : L ⋙ D.first ≅ L ⋙ D.second)
    (hL : ConeLaws (D := D.toDiagram) L θ) (e : R ⋙ F ≅ L)
    (square : isoWhiskerRight e D.first ≪≫ θ =
      isoWhiskerLeft R (eqToIso hF) ≪≫ isoWhiskerRight e D.second) :
    R ⋙ D.equalFunctor F hF ≅ coneFunctor L θ hL :=
  NatIso.ofComponents (fun c => asIso (show (R ⋙ D.equalFunctor F hF).obj c ⟶
      (coneFunctor L θ hL).obj c from {
    localArrow := e.hom.app c
    commutes := by
      have h := congrArg (fun k => k.hom.app c) square
      simpa only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
        eqToIso.hom, eqToHom_app, isoWhiskerRight_hom, whiskerRight_app,
        StrictDiagram.equalFunctor, StrictDiagram.equalDatum, StrictDiagram.toDiagram,
        coneFunctor, Functor.comp_obj, Iso.app_hom] using h })) (by
      intro x y f
      apply Datum.Hom.ext
      exact e.hom.naturality f)

/-- Relabeling the source local functor preserves its selected overlap square. -/
theorem canonicalSquare_relabel {D : Diagram.{u,v}}
    {L L' K : C ⥤ D.localCategory} (h : L = L') (e : L' ≅ K)
    (θ : K ⋙ D.first ≅ K ⋙ D.second)
    (hL : L ⋙ D.first = L ⋙ D.second) (hL' : L' ⋙ D.first = L' ⋙ D.second)
    (square : isoWhiskerRight e D.first ≪≫ θ = eqToIso hL' ≪≫ isoWhiskerRight e D.second) :
    isoWhiskerRight (eqToIso h ≪≫ e) D.first ≪≫ θ =
      eqToIso hL ≪≫ isoWhiskerRight (eqToIso h ≪≫ e) D.second := by
  cases h
  simpa only [eqToIso_refl, Iso.refl_trans] using square

end SquareKit.Internal.PathTransport.CechMatching
