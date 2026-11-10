import SquareKit.Internal.PathTransport.FamilyMapElimination

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Type u} [Category.{u} Γ] {A B : Γ ⥤ Grpd.{u,u}}

/-- Component presentation of the existing family image, with the same lift. -/
def Section.familyImage (α : A ⟶ B) (x : Section A) : Section B where
  obj γ := (α.app γ).obj (x.obj γ)
  map f := (Grothendieck.map (whiskerRight α Grpd.forgetToCat)).map (x.lift.map f) |>.fiber
  map_id γ := by
    have h := Grothendieck.congr ((x.lift ⋙ Grothendieck.map
      (whiskerRight α Grpd.forgetToCat)).map_id γ)
    simpa using h
  map_comp f g := by
    have h := Grothendieck.congr ((x.lift ⋙ Grothendieck.map
      (whiskerRight α Grpd.forgetToCat)).map_comp f g)
    simpa [Grothendieck.map, Section.lift, Grpd.forgetToCat, Category.assoc] using h

theorem Section.familyImage_lift (α : A ⟶ B) (x : Section A) :
    (x.familyImage α).lift = x.lift ⋙ Grothendieck.map (whiskerRight α Grpd.forgetToCat) := rfl

theorem Section.familyImage_eq (α : A ⟶ B) (x : Section A) :
    x.familyImage α = x.mapFamily α := by
  apply Section.lift_injective
  rw [Section.familyImage_lift, Section.mapFamily_lift]

namespace PathComparison
variable (α : A ⟶ B) (x : Section A)

def familyMap : PathCtx A x ⥤ PathCtx B (x.familyImage α) where
  obj a := ⟨(Grothendieck.map (whiskerRight α Grpd.forgetToCat)).obj a.base,
    Discrete.mk ((α.app a.base.base).map a.fiber.as)⟩
  map {a b} f :=
    ⟨(Grothendieck.map (whiskerRight α Grpd.forgetToCat)).map f.base,
      Discrete.eqToHom (by
        have h := f.fiber.eq
        change inv ((x.familyImage α).map f.base.base) ≫
          (B.map f.base.base).map ((α.app a.base.base).map a.fiber.as) ≫
          ((Grothendieck.map (whiskerRight α Grpd.forgetToCat)).map f.base).fiber =
          (α.app b.base.base).map b.fiber.as
        change inv (x.map f.base.base) ≫
          (A.map f.base.base).map a.fiber.as ≫ f.base.fiber = b.fiber.as at h
        have hn := NatIso.naturality_2 (eqToIso (α.naturality f.base.base)) a.fiber.as
        dsimp [Section.familyImage, Grothendieck.map, Section.lift, Grpd.forgetToCat]
        rw [← h]
        simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_inv,
          IsIso.inv_comp, Category.assoc]
        simp only [Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, inv_eqToHom]
        simpa only [eqToIso.hom, eqToIso.inv, eqToHom_app, Grpd.comp_eq_comp,
          CategoryTheory.Functor.comp_map, inv_eqToHom, Category.assoc] using
          congrArg (fun k => inv ((α.app b.base.base).map (x.map f.base.base)) ≫
            k ≫ (α.app b.base.base).map f.base.fiber) hn)⟩
  map_id a := by
    fapply Grothendieck.ext
    · exact (Grothendieck.map (whiskerRight α Grpd.forgetToCat)).map_id a.base
    · exact congrArg Discrete.Hom.mk rfl
  map_comp f g := by
    fapply Grothendieck.ext
    · exact (Grothendieck.map (whiskerRight α Grpd.forgetToCat)).map_comp f.base g.base
    · exact congrArg Discrete.Hom.mk rfl

theorem familyMap_retract : familyMap α x ⋙ retract B (x.familyImage α) = retract A x := rfl

theorem familyMap_reflexive : reflexive A x ⋙ familyMap α x = reflexive B (x.familyImage α) := by
  fapply CategoryTheory.Functor.ext
  · intro γ
    apply congrArg (fun p => (⟨(x.familyImage α).lift.obj γ,Discrete.mk p⟩ : PathCtx B (x.familyImage α)))
    exact (α.app γ).map_id _
  · intro γ δ f
    fapply Grothendieck.ext
    · simp [familyMap, reflexive, Grothendieck.base_eqToHom]
      rfl
    · exact congrArg Discrete.Hom.mk rfl

theorem familyMap_arrow (a : PathCtx A x) :
    (Grothendieck.map (whiskerRight α Grpd.forgetToCat)).map (arrow A x a) =
      arrow B (x.familyImage α) ((familyMap α x).obj a) := by
  fapply Grothendieck.ext
  · rfl
  · simp [arrow, Grothendieck.ι, Grothendieck.map, familyMap,
      Grpd.forgetToCat, eqToHom_map]

variable [IsGroupoid Γ]

theorem familyMapSquare : EquivalenceSquare.Square
    (pathEquivalence B (x.familyImage α)) (pathEquivalence A x)
    (familyMap α x) (𝟭 Γ) where
  forward := familyMap_reflexive α x
  inverse := rfl
  counitInv := by
    apply NatTrans.ext
    funext a
    apply (weaken (PathFamily B (x.familyImage α))).map_injective
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, eqToHom_app]
    simp only [weaken, Grothendieck.forget_map,
      Grothendieck.comp_base, Grothendieck.base_eqToHom, eqToHom_refl, Category.comp_id]
    change ((weaken (PathFamily B (x.familyImage α))).mapIso
      ((familyMap α x).mapIso ((contraction A x).app a))).inv =
      ((weaken (PathFamily B (x.familyImage α))).mapIso
        ((contraction B (x.familyImage α)).app ((familyMap α x).obj a))).inv
    apply (Iso.inv_eq_inv _ _).mpr
    exact familyMap_arrow α x a

end PathComparison
end SquareKit.Internal.PathTransport.GroupoidModel
