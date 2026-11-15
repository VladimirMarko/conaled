import SquareKit.Internal.PathTransport.FamilyModification

/-! Reflect vertical natural isomorphisms through fiber inclusion. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C : Type u} [Category.{u} C] (B : C ⥤ Grpd.{u,u})

/-- The fiber arrow of a total arrow whose selected base is identity. -/
def verticalFiber {c : C} {x y : B.obj c}
    (f : (Grothendieck.ι (B ⋙ Grpd.forgetToCat) c).obj x ⟶
      (Grothendieck.ι (B ⋙ Grpd.forgetToCat) c).obj y) (h : f.base = 𝟙 c) : x ⟶ y :=
  eqToHom (by rw [h]; simp) ≫ f.fiber

@[simp] theorem inclusion_verticalFiber {c : C} {x y : B.obj c}
    (f : (Grothendieck.ι (B ⋙ Grpd.forgetToCat) c).obj x ⟶
      (Grothendieck.ι (B ⋙ Grpd.forgetToCat) c).obj y) (h : f.base = 𝟙 c) :
    (Grothendieck.ι (B ⋙ Grpd.forgetToCat) c).map (verticalFiber B f h) = f := by
  fapply Grothendieck.ext
  · exact h.symm
  · simp [verticalFiber, Grothendieck.ι]

/-- A selected vertical total isomorphism determines a fiber natural
isomorphism; naturality follows by faithfulness of fiber inclusion. -/
def verticalFiberIso {E : Type u} [Category.{u} E] {c : C}
    {F G : E ⥤ B.obj c}
    (e : F ⋙ Grothendieck.ι (B ⋙ Grpd.forgetToCat) c ≅
      G ⋙ Grothendieck.ι (B ⋙ Grpd.forgetToCat) c)
    (h : ∀ x, (e.hom.app x).base = 𝟙 c) : F ≅ G := by
  refine NatIso.ofComponents (fun x => asIso (verticalFiber B (e.hom.app x) (h x))) ?_
  intro x y f
  apply (Grothendieck.ι (B ⋙ Grpd.forgetToCat) c).map_injective
  simpa only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, asIso_hom, inclusion_verticalFiber] using e.hom.naturality f

theorem verticalFiberIso_inclusion {E : Type u} [Category.{u} E] {c : C}
    {F G : E ⥤ B.obj c}
    (e : F ⋙ Grothendieck.ι (B ⋙ Grpd.forgetToCat) c ≅
      G ⋙ Grothendieck.ι (B ⋙ Grpd.forgetToCat) c)
    (h : ∀ x, (e.hom.app x).base = 𝟙 c) :
    isoWhiskerRight (verticalFiberIso B e h) (Grothendieck.ι (B ⋙ Grpd.forgetToCat) c) = e := by
  ext x
  exact inclusion_verticalFiber B _ (h x)

end SquareKit.Internal.PathTransport.GroupoidModel
