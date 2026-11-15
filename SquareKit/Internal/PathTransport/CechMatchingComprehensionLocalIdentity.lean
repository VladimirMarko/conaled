import SquareKit.Internal.PathTransport.CechMatchingComprehensionIdentity
import SquareKit.Internal.PathTransport.GrothendieckVertical

/-! Relative identity paths can be specified by their actual local fiber arrow. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension.Identity
open CategoryTheory
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D : StrictDiagram.{u,u}} {A : FamilyData D} {h : A.Coherence}
variable {d : Datum D.toDiagram} (x y : Fiber A h d)

abbrev localLift (p : x.localFiber ⟶ y.localFiber) : x.datum.localObject ⟶ y.datum.localObject :=
  (Grothendieck.ι (A.localFamily ⋙ Grpd.forgetToCat) d.localObject).map p

/-- The equation uses the actual total overlap arrows of both endpoints. -/
def LocalPaths := {p : x.localFiber ⟶ y.localFiber //
  A.firstMap.map (localLift x y p) ≫ y.overlap.hom =
    x.overlap.hom ≫ A.secondMap.map (localLift x y p)}

def localArrowEquiv : LocalPaths x y ≃ (x ⟶ y) where
  toFun p := ⟨⟨localLift x y p.val, p.property⟩, rfl⟩
  invFun p := ⟨GrothendieckVertical.arrow (A.localFamily ⋙ Grpd.forgetToCat)
    p.matchingArrow.localArrow p.vertical, by
      change A.firstMap.map _ ≫ _ = _ ≫ A.secondMap.map _
      dsimp only [localLift]
      erw [GrothendieckVertical.inclusion_arrow]
      exact p.matchingArrow.commutes⟩
  left_inv p := by
    apply Subtype.ext
    apply (Grothendieck.ι (A.localFamily ⋙ Grpd.forgetToCat) d.localObject).map_injective
    exact GrothendieckVertical.inclusion_arrow (A.localFamily ⋙ Grpd.forgetToCat) (localLift x y p.val) rfl
  right_inv p := by
    apply Fiber.Hom.ext
    apply Datum.Hom.ext
    exact GrothendieckVertical.inclusion_arrow (A.localFamily ⋙ Grpd.forgetToCat) p.matchingArrow.localArrow p.vertical

@[simp] theorem localArrowEquiv_local (p : LocalPaths x y) :
    ((localArrowEquiv x y) p).matchingArrow.localArrow = localLift x y p.val := rfl

variable {C : Type u} [Groupoid.{u} C]

/-- Fully faithful evaluation recovers every compatible local identity arrow. -/
def localRestrictionEquiv (R : C ⥤ Fiber A h d) [R.Full] [R.Faithful] (a b : C) :
    (a ⟶ b) ≃ LocalPaths (R.obj a) (R.obj b) :=
  ((Functor.FullyFaithful.ofFullyFaithful R).homEquiv (X := a) (Y := b)).trans
    (localArrowEquiv (R.obj a) (R.obj b)).symm

@[simp] theorem localRestrictionEquiv_arrow (R : C ⥤ Fiber A h d) [R.Full] [R.Faithful]
    (a b : C) (p : a ⟶ b) :
    localLift (R.obj a) (R.obj b) (localRestrictionEquiv R a b p).val =
      (R.map p).matchingArrow.localArrow :=
  GrothendieckVertical.inclusion_arrow (A.localFamily ⋙ Grpd.forgetToCat)
    (R.map p).matchingArrow.localArrow (R.map p).vertical

end SquareKit.Internal.PathTransport.CechMatching.Comprehension.Identity
