import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiber
import SquareKit.Internal.PathTransport.CechMatchingComprehensionRebase

/-! Relative matching objects transport along the actual local-family action. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D : StrictDiagram.{u,u}} {A : FamilyData D} {h : A.Coherence}
namespace Fiber
variable {d e : Datum D.toDiagram}

def transportLocalIso (f : d ⟶ e) (x : Fiber A h d) :
    x.datum.localObject ≅ liftLocal A e ((A.localFamily.map f.localArrow).obj x.localFiber) :=
  (Grothendieck.transportIso x.datum.localObject (asIso f.localArrow)).symm

def transportedDatum (f : d ⟶ e) (x : Fiber A h d) : Datum (A.total h).toDiagram :=
  x.datum.rebase (transportLocalIso f x)

def transportArrow (f : d ⟶ e) (x : Fiber A h d) : x.datum ⟶ transportedDatum f x :=
  x.datum.rebaseArrow (transportLocalIso f x)

theorem transported_projection (f : d ⟶ e) (x : Fiber A h d) :
    (A.projection h).mapDatum (transportedDatum f x) = e := by
  let p := (A.projection h).functor.map (transportArrow f x)
  let q := eqToHom (projection_datum x) ≫ f
  apply Datum.target_eq p q rfl
  apply heq_of_eq
  change f.localArrow = (eqToHom (projection_datum x) ≫ f).localArrow
  simp only [Datum.comp_localArrow, Datum.eqToHom_localArrow, eqToHom_refl,
    Category.id_comp]

def transport (f : d ⟶ e) (x : Fiber A h d) : Fiber A h e :=
  ofDatum (transportedDatum f x) (transported_projection f x)

@[simp] theorem transport_datum (f : d ⟶ e) (x : Fiber A h d) :
    (transport f x).datum = transportedDatum f x := datum_ofDatum _ _

@[simp] theorem transport_localFiber (f : d ⟶ e) (x : Fiber A h d) :
    (transport f x).localFiber = (A.localFamily.map f.localArrow).obj x.localFiber :=
  eq_of_heq (localFiber_ofDatum _ _)

end Fiber
end SquareKit.Internal.PathTransport.CechMatching.Comprehension
