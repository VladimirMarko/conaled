import SquareKit.Internal.PathTransport.CechMatchingCone
import SquareKit.Internal.PathTransport.CechMatchingMapComposition

/-! Maps of matching cones preserve the complete functor when the supplied
local action and selected overlap agree after their explicit transports. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.ConeMap
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w z
variable {D E : StrictDiagram.{u,v}} (S : StrictMap D E)
variable {C : Type w} [Category.{u} C] {B : Type z} [Category.{u} B]
variable (L : C ⥤ D.localCategory) (K : B ⥤ E.localCategory) (T : C ⥤ B)
variable (η : L ⋙ D.first ≅ L ⋙ D.second) (θ : K ⋙ E.first ≅ K ⋙ E.second)

def mappedOverlap : (L ⋙ S.localMap) ⋙ E.first ≅ (L ⋙ S.localMap) ⋙ E.second :=
  isoWhiskerLeft L (eqToIso S.first) ≪≫ isoWhiskerRight η S.doubleMap ≪≫
    (isoWhiskerLeft L (eqToIso S.second)).symm

def transportedOverlap (hL : L ⋙ S.localMap = T ⋙ K) :
    (T ⋙ K) ⋙ E.first ≅ (T ⋙ K) ⋙ E.second :=
  (isoWhiskerRight (eqToIso hL) E.first).symm ≪≫ mappedOverlap S L η ≪≫
    isoWhiskerRight (eqToIso hL) E.second

private theorem iso_heq {X Y : E.localCategory} (h : X = Y)
    (p : E.first.obj X ≅ E.second.obj X) (q : E.first.obj Y ≅ E.second.obj Y)
    (hp : (E.first.mapIso (eqToIso h)).symm ≪≫ p ≪≫ E.second.mapIso (eqToIso h) = q) :
    HEq p q := by
  subst Y
  apply heq_of_eq
  simpa using hp

theorem coneFunctor_map (h : ConeLaws (D := D.toDiagram) L η) (k : ConeLaws (D := E.toDiagram) K θ)
    (hL : L ⋙ S.localMap = T ⋙ K)
    (hη : transportedOverlap S L K T η hL = isoWhiskerLeft T θ) :
    coneFunctor L η h ⋙ S.functor = T ⋙ coneFunctor K θ k := by
  have ho (c : C) : (coneFunctor L η h ⋙ S.functor).obj c =
      (T ⋙ coneFunctor K θ k).obj c := by
    apply Datum.ext (Functor.congr_obj hL c)
    apply iso_heq (Functor.congr_obj hL c)
    apply Iso.ext
    simpa [transportedOverlap, mappedOverlap, StrictMap.functor, StrictMap.mapDatum,
      StrictMap.overlap, coneFunctor] using congrArg (fun i => i.hom.app c) hη
  refine CategoryTheory.Functor.ext ho ?_
  intro x y f
  apply Datum.Hom.ext
  simp only [Functor.comp_map, coneFunctor, StrictMap.functor,
    Datum.comp_localArrow, Datum.eqToHom_localArrow]
  exact Functor.congr_hom hL f

end SquareKit.Internal.PathTransport.CechMatching.ConeMap
