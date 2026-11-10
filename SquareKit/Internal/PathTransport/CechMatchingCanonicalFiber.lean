import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberArrow

/-! Canonical local representatives for extracted matching fibers. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D : StrictDiagram.{u,u}} (A : FamilyData D) (h : A.Coherence)
variable (e : Datum (A.total h).toDiagram) (d : Datum D.toDiagram)
variable (hd : (A.projection h).functor.obj e = d)
variable (x : A.localFamily.obj d.localObject)
variable (hx : e.localObject = liftLocal A d x)

def canonicalDatum : Datum (A.total h).toDiagram := e.rebase (eqToIso hx)

include hd in
theorem canonicalDatum_projection :
    (A.projection h).functor.obj (canonicalDatum A h e d x hx) = d := by
  let p := (A.projection h).functor.map (e.rebaseArrow (eqToIso hx))
  let q := eqToHom hd
  apply Datum.target_eq p q rfl
  apply heq_of_eq
  change (eqToHom hx).base = (eqToHom hd).localArrow
  rw [Grothendieck.base_eqToHom, Datum.eqToHom_localArrow]

def canonicalFiber : Fiber A h d :=
  Fiber.ofDatum (canonicalDatum A h e d x hx)
    (canonicalDatum_projection A h e d hd x hx)

theorem canonicalFiber_local : (canonicalFiber A h e d hd x hx).localFiber = x :=
  eq_of_heq (Fiber.localFiber_ofDatum _ _)

private theorem canonicalArrow_vertical :
    (A.projection h).functor.map (e.rebaseArrow (eqToIso hx)) ≫
      eqToHom (canonicalDatum_projection A h e d hd x hx) = eqToHom hd := by
  apply (Datum.localFunctor).map_injective
  change (eqToHom hx).base ≫
    (eqToHom (canonicalDatum_projection A h e d hd x hx)).localArrow =
      (eqToHom hd).localArrow
  rw [Grothendieck.base_eqToHom, Datum.eqToHom_localArrow, Datum.eqToHom_localArrow]
  simp only [eqToHom_trans]

def canonicalFiberIso : Fiber.ofDatum e hd ≅ canonicalFiber A h e d hd x hx :=
  asIso (ofDatumArrow hd (canonicalDatum_projection A h e d hd x hx)
    (e.rebaseArrow (eqToIso hx)) (canonicalArrow_vertical A h e d hd x hx))

end SquareKit.Internal.PathTransport.CechMatching.Comprehension
