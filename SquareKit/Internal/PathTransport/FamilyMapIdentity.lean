import SquareKit.Internal.PathTransport.FamilyMapPath

/-! Action of an arbitrary family map on actual identity arrows. This
construction is independent of comparison-model packaging. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Type u} [Category.{u} Γ] {A B : Γ ⥤ Grpd.{u,u}}

/-- Identity comparison applies the component functor to the selected arrow. -/
def directIdentityMap (α : A ⟶ B) (x y : Section A) :
    directIdentity A x y ⟶ directIdentity B (x.familyImage α) (y.familyImage α) where
  app γ := ↾fun p => (α.app γ).map p
  naturality {γ δ} f := by
    ext p
    have hn := NatIso.naturality_2 (eqToIso (α.naturality f)) p
    change (α.app δ).map (inv (x.map f) ≫ (A.map f).map p ≫ y.map f) =
      inv ((x.familyImage α).map f) ≫ (B.map f).map ((α.app γ).map p) ≫
        (y.familyImage α).map f
    dsimp [Section.familyImage, Grothendieck.map, Section.lift, Grpd.forgetToCat]
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_inv,
      IsIso.inv_comp, Category.assoc]
    simp only [Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, inv_eqToHom]
    simpa only [eqToIso.hom, eqToIso.inv, eqToHom_app, Grpd.comp_eq_comp,
      CategoryTheory.Functor.comp_map, inv_eqToHom, Category.assoc] using
      congrArg (fun k => inv ((α.app δ).map (x.map f)) ≫ k ≫
        (α.app δ).map (y.map f)) hn.symm

def identityMap (α : A ⟶ B) (x y : Section A) :
    identityFamily A x y ⟶ identityFamily B (x.familyImage α) (y.familyImage α) :=
  whiskerRight (directIdentityMap α x y) discrete

theorem identityMap_arrow (α : A ⟶ B) (x y : Section A) (γ : Γ)
    (p : x.obj γ ⟶ y.obj γ) :
    ((identityMap α x y).app γ).obj (Discrete.mk p) = Discrete.mk ((α.app γ).map p) := rfl

theorem reflexivity_familyImage (α : A ⟶ B) (x : Section A) :
    (reflexivitySection A x).familyImage (identityMap α x x) =
      reflexivitySection B (x.familyImage α) := by
  apply Section.lift_injective
  fapply CategoryTheory.Functor.ext
  · intro γ
    apply congrArg (fun p => (⟨γ, Discrete.mk p⟩ : Extend
      (identityFamily B (x.familyImage α) (x.familyImage α))))
    exact (α.app γ).map_id _
  · intro γ δ f
    fapply Grothendieck.ext
    · simp [Section.familyImage, Section.lift, Grothendieck.base_eqToHom]
    · exact congrArg Discrete.Hom.mk rfl

theorem reflexivity_cast {x y : Section A} (h : x = y) :
    cast (congrArg Section (congrArg (fun t => identityFamily A t t) h))
      (reflexivitySection A x) = reflexivitySection A y := by
  cases h
  rfl

end SquareKit.Internal.PathTransport.GroupoidModel
