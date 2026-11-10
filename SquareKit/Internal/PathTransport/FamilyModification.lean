import SquareKit.Internal.PathTransport.ComparisonComposition

/-! Selected component natural isomorphisms between ordinary family maps.
The record is external to the strict comparison model. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C : Type u} [Category.{u} C] {A B : C ⥤ Grpd.{u,u}}

/-- Family-map naturality expressed as equality of fiber functors. -/
theorem familyMap_naturality (α : A ⟶ B) {c d : C} (f : c ⟶ d) :
    (A.map f ⋙ α.app d : A.obj c ⥤ B.obj d) = α.app c ⋙ B.map f := α.naturality f

/-- Component isomorphisms commute with every base arrow, as an equation of
natural isomorphisms of functors between the actual fibers. -/
structure FamilyModification (α β : A ⟶ B) where
  app : ∀ c, (show A.obj c ⥤ B.obj c from α.app c) ≅ β.app c
  naturality : ∀ {c d} (f : c ⟶ d),
    isoWhiskerLeft (A.map f) (app d) ≪≫ eqToIso (familyMap_naturality β f) =
      eqToIso (familyMap_naturality α f) ≪≫ isoWhiskerRight (app c) (B.map f)

namespace FamilyModification
variable {α β : A ⟶ B}

def ofEq (h : α = β) : FamilyModification α β := by
  cases h
  refine ⟨fun c => Iso.refl _, ?_⟩
  intro c d f
  ext x
  simp

/-- The selected fiber isomorphism, regarded in the total category. -/
def totalComponent (m : FamilyModification α β) (x : Extend A) :
    (Grothendieck.map (whiskerRight α Grpd.forgetToCat)).obj x ≅
      (Grothendieck.map (whiskerRight β Grpd.forgetToCat)).obj x :=
  (Grothendieck.ι (B ⋙ Grpd.forgetToCat) x.base).mapIso ((m.app x.base).app x.fiber)

theorem totalComponent_naturality (m : FamilyModification α β)
    {x y : Extend A} (f : x ⟶ y) :
    (Grothendieck.map (whiskerRight α Grpd.forgetToCat)).map f ≫ (m.totalComponent y).hom =
      (m.totalComponent x).hom ≫ (Grothendieck.map (whiskerRight β Grpd.forgetToCat)).map f := by
  have hn := congrArg (fun i => i.hom.app x.fiber) (m.naturality f.base)
  have hf := (m.app y.base).hom.naturality f.fiber
  fapply Grothendieck.ext
  · simp [totalComponent]
  · dsimp [totalComponent, Grothendieck.map, Grothendieck.ι, Grpd.forgetToCat]
    simp only [Functor.map_comp, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, eqToHom_map, Category.assoc]
    have hi := NatIso.naturality_2 (eqToIso (B.map_id y.base)) ((α.app y.base).map f.fiber)
    simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, Grpd.id_eq_id, Functor.id_map] at hi
    rw [← hi]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [hf]
    simp only [Iso.trans_hom, eqToIso.hom, NatTrans.comp_app, eqToHom_app] at hn
    have he := congrArg (fun k =>
      eqToHom (congrArg (fun F => F.obj x.fiber) (familyMap_naturality α f.base).symm) ≫ k ≫
        eqToHom (congrArg (fun F => F.obj x.fiber) (familyMap_naturality β f.base).symm) ≫
          (β.app y.base).map f.fiber) hn
    dsimp only [Grpd.forgetToCat] at he ⊢
    simp only [isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
      whiskerRight_app, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp] at he
    convert he using 1 <;> simp

def totalIso (m : FamilyModification α β) :
    Grothendieck.map (whiskerRight α Grpd.forgetToCat) ≅
      Grothendieck.map (whiskerRight β Grpd.forgetToCat) :=
  NatIso.ofComponents m.totalComponent (fun f => m.totalComponent_naturality f)

end FamilyModification
end SquareKit.Internal.PathTransport.GroupoidModel
