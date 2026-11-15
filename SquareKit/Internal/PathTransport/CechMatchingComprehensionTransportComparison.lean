import SquareKit.Internal.PathTransport.CechMatchingComprehensionFactor
import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberFunctor

/-! Selected transport comparisons for the fibers extracted from an actual
functor over the base. No strict family naturality is an input. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory CategoryTheory.Functor
open GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
namespace Evaluation
variable {D : StrictDiagram.{u,u}} (A : FamilyData D) (h : A.Coherence)
variable {C : Grpd.{u,u}} (G : C ⥤ Grpd.{u,u}) (R : C ⥤ Datum D.toDiagram)
variable (E : Extend G ⥤ Datum (A.total h).toDiagram)
variable (hE : E ⋙ (A.projection h).functor =
  Grothendieck.forget (G ⋙ Grpd.forgetToCat) ⋙ R)

include hE in
theorem fiber_projection (c : C) :
    (Grothendieck.ι (G ⋙ Grpd.forgetToCat) c ⋙ E) ⋙
      (A.projection h).functor = (Functor.const (G.obj c)).obj (R.obj c) := by
  rw [Functor.assoc, hE]
  exact inclusion_forget_comp G R c

def component (c : C) : G.obj c ⥤ Fiber A h (R.obj c) :=
  fixedBaseFunctor A h (Grothendieck.ι (G ⋙ Grpd.forgetToCat) c ⋙ E)
    (R.obj c) (fiber_projection A h G R E hE c)

def comparison (c : C) : component A h G R E hE c ⋙ Fiber.forget ≅
    Grothendieck.ι (G ⋙ Grpd.forgetToCat) c ⋙ E :=
  fixedBaseComparison A h _ _ _

def sourceTransport {c d : C} (f : c ⟶ d) :
    Grothendieck.ι (G ⋙ Grpd.forgetToCat) c ≅
      G.map f ⋙ Grothendieck.ι (G ⋙ Grpd.forgetToCat) d :=
  NatIso.ofComponents
    (fun x => (Grothendieck.transportIso ⟨c, x⟩ (asIso f)).symm)
    (fun k => (Grothendieck.ιNatTrans (F := G ⋙ Grpd.forgetToCat) f).naturality k)

def totalTransport {c d : C} (f : c ⟶ d) :
    component A h G R E hE c ⋙ Fiber.forget ≅
      G.map f ⋙ component A h G R E hE d ⋙ Fiber.forget :=
  comparison A h G R E hE c ≪≫
    isoWhiskerRight (sourceTransport G f) E ≪≫
      isoWhiskerLeft (G.map f) (comparison A h G R E hE d).symm

theorem totalTransport_base {c d : C} (f : c ⟶ d) (x : G.obj c) :
    ((totalTransport A h G R E hE f).hom.app x).localArrow.base =
      (R.map f).localArrow := by
  let P := (A.projection h).functor ⋙ Datum.localFunctor
  change P.map ((totalTransport A h G R E hE f).hom.app x) = _
  dsimp only [totalTransport, comparison, fixedBaseComparison, sourceTransport,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    asIso_hom, eqToIso.hom, eqToIso.inv]
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  have hh := Functor.congr_hom
    (congrArg (fun K => K ⋙ Datum.localFunctor) hE)
    ((Grothendieck.ιNatTrans (F := G ⋙ Grpd.forgetToCat) f).app x)
  dsimp only [Functor.comp_map, Grothendieck.forget_map,
    Grothendieck.ιNatTrans] at hh
  dsimp only [P, Functor.comp_map]
  erw [hh]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  rfl

def transportResidual {c d : C} (f : c ⟶ d) (x : G.obj c) :
    Fiber.transport (R.map f) ((component A h G R E hE c).obj x) ⟶
      (component A h G R E hE d).obj ((G.map f).obj x) :=
  Fiber.factorLift (R.map f) ((totalTransport A h G R E hE f).hom.app x)
    (totalTransport_base A h G R E hE f x)

def transportComparisonInv {c d : C} (f : c ⟶ d) :
    component A h G R E hE c ⋙ Fiber.transportFunctor (R.map f) ≅
      G.map f ⋙ component A h G R E hE d :=
  NatIso.ofComponents (fun x => asIso (transportResidual A h G R E hE f x)) (by
    intro x y g
    apply Fiber.Hom.ext
    have hn := (totalTransport A h G R E hE f).hom.naturality g
    change ((component A h G R E hE c).map g).matchingArrow ≫
        (totalTransport A h G R E hE f).hom.app y =
      (totalTransport A h G R E hE f).hom.app x ≫
        ((component A h G R E hE d).map ((G.map f).map g)).matchingArrow at hn
    change (inv (Fiber.lift (R.map f) _) ≫
        ((component A h G R E hE c).map g).matchingArrow ≫ Fiber.lift (R.map f) _) ≫
        (inv (Fiber.lift (R.map f) _) ≫ (totalTransport A h G R E hE f).hom.app y) =
      (inv (Fiber.lift (R.map f) _) ≫ (totalTransport A h G R E hE f).hom.app x) ≫
        ((component A h G R E hE d).map ((G.map f).map g)).matchingArrow
    simpa [Category.assoc] using congrArg
      (fun k => inv (Fiber.lift (R.map f) ((component A h G R E hE c).obj x)) ≫ k) hn)

/-- Evaluation commutes with transport through a selected natural isomorphism. -/
def transportComparison {c d : C} (f : c ⟶ d) :
    G.map f ⋙ component A h G R E hE d ≅
      component A h G R E hE c ⋙ Fiber.transportFunctor (R.map f) :=
  (transportComparisonInv A h G R E hE f).symm

/-- The comparison retains the evaluated source transport arrow exactly. -/
theorem transportComparison_factor {c d : C} (f : c ⟶ d) (x : G.obj c) :
    Fiber.lift (R.map f) ((component A h G R E hE c).obj x) ≫
      ((transportComparison A h G R E hE f).inv.app x).matchingArrow =
    (totalTransport A h G R E hE f).hom.app x :=
  Fiber.lift_factorLift (R.map f) ((totalTransport A h G R E hE f).hom.app x)
    (totalTransport_base A h G R E hE f x)

end Evaluation
end SquareKit.Internal.PathTransport.CechMatching.Comprehension
