import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberArrowEquiv

/-! Endpoint comparison conjugates the actual fixed-base hom map. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {D : StrictDiagram.{u,u}} (A : FamilyData D) (h : A.Coherence)
variable {Z : Type v} [Category.{u} Z]
variable (E : Z ⥤ Datum (A.total h).toDiagram) (d : Datum D.toDiagram)
variable (he : E ⋙ (A.projection h).functor = (Functor.const Z).obj d)

theorem fixedBaseArrow_endpoint {x y : Z} (p : x ⟶ y)
    (e f : Datum (A.total h).toDiagram)
    (hep : (A.projection h).functor.obj e = d) (hfp : (A.projection h).functor.obj f = d)
    (ex : E.obj x = e) (ey : E.obj y = f)
    (hx : fixedBaseObject A h E d he x = Fiber.ofDatum e hep)
    (hy : fixedBaseObject A h E d he y = Fiber.ofDatum f hfp)
    (q : e ⟶ f) (hq : q = eqToHom ex.symm ≫ E.map p ≫ eqToHom ey)
    (hp : (A.projection h).functor.map q ≫ eqToHom hfp = eqToHom hep) :
    ofDatumArrow hep hfp q hp =
      eqToHom hx.symm ≫ (fixedBaseFunctor A h E d he).map p ≫ eqToHom hy := by
  subst e; subst f; subst q
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end SquareKit.Internal.PathTransport.CechMatching.Comprehension
