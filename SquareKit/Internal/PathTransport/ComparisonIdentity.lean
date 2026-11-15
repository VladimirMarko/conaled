import SquareKit.Internal.PathTransport.ComparisonComprehension
import SquareKit.Internal.PathTransport.FamilyMapIdentity

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
private theorem grpd_transport_obj {C D : Grpd.{u,u}} (h : C = D) (x : C) :
    HEq ((eqToHom h).obj x) x := by cases h; rfl

private theorem family_transport_map {C : Type u} [Category.{u} C]
    {A B : C ⥤ Grpd.{u,u}} (h : A = B) (γ : C) {x y : A.obj γ} (p : x ⟶ y) :
    HEq (((eqToHom h).app γ).map p) p := by cases h; rfl

private theorem discrete_mk_heq {α β : Type u} {x : α} {y : β} (h : HEq x y) :
    HEq (Discrete.mk x) (Discrete.mk y) := by cases h; rfl

namespace Family
variable {Γ : Context.{u}}

/-- Compare identity fibers by mapping their selected arrows. Endpoint
identifications are derived from the compared sections. -/
def identity (A : Family Γ) (x y : Section A) : Family Γ where
  left := identityFamily A.left x.left y.left
  right := identityFamily A.right x.right y.right
  map := identityMap A.map x.left y.left ≫
    eqToHom (by rw [x.commutes, y.commutes]; rfl)

def reflexivity (A : Family Γ) (x : Section A) : Section (A.identity x x) where
  left := reflexivitySection A.left x.left
  right := reflexivitySection A.right x.right
  commutes := by
    dsimp [identity]
    rw [GroupoidModel.Section.familyImage_comp,
      reflexivity_familyImage, GroupoidModel.Section.familyImage_eqToHom]
    exact reflexivity_cast x.commutes

theorem identity_sub {Δ : Context.{u}} (A : Family Γ) (x y : Section A)
    (σ : Substitution Δ Γ) :
    (A.identity x y).reindex σ = (A.reindex σ).identity (x.reindex σ) (y.reindex σ) := by
  refine @Family.ext _ _ _ rfl rfl ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext γ
  fapply CategoryTheory.Functor.ext
  · intro p
    dsimp [identity, reindex, identityMap, directIdentityMap, discrete]
    simp only [eqToHom_app, Grpd.comp_eq_comp, CategoryTheory.Functor.comp_obj]
    apply eq_of_heq
    apply (grpd_transport_obj _ _).trans
    apply (grpd_transport_obj _ _).trans
    apply HEq.symm
    apply (grpd_transport_obj _ _).trans
    apply discrete_mk_heq
    simp only [CategoryTheory.Functor.comp_map]
    exact family_transport_map _ _ _
  · intro p q f
    exact congrArg Discrete.Hom.mk rfl

theorem refl_sub {Δ : Context.{u}} (A : Family Γ) (x : Section A) (σ : Substitution Δ Γ) :
    HEq ((A.reflexivity x).reindex σ) ((A.reindex σ).reflexivity (x.reindex σ)) :=
  Section.hext (A.identity_sub x x σ) HEq.rfl HEq.rfl

end Family
end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
