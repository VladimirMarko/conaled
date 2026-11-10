import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.HomCongr

/-! Equivalences of fibers induce equivalences of context extensions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.GrothendieckEquivalence
open CategoryTheory
universe u v w z
variable {C : Type u} [Category.{v} C] {F G : C ⥤ Cat.{z,w}}
variable (α : F ⟶ G)

/-- Lift the fiber arrow using the component functor; the base arrow is kept. -/
def preimage [∀ c, (α.app c).toFunctor.Full]
    {X Y : Grothendieck F} (f : (Grothendieck.map α).obj X ⟶ (Grothendieck.map α).obj Y) : X ⟶ Y where
  base := f.base
  fiber := (α.app Y.base).toFunctor.preimage
    ((eqToHom (α.naturality f.base)).toNatTrans.app X.fiber ≫ f.fiber)

@[simp] theorem map_preimage [∀ c, (α.app c).toFunctor.Full]
    {X Y : Grothendieck F} (f : (Grothendieck.map α).obj X ⟶ (Grothendieck.map α).obj Y) :
    (Grothendieck.map α).map (preimage α f) = f := by
  fapply Grothendieck.ext
  · rfl
  · simp [Grothendieck.map, preimage]

@[simp] theorem preimage_map [∀ c, (α.app c).toFunctor.Full]
    [∀ c, (α.app c).toFunctor.Faithful] {X Y : Grothendieck F} (f : X ⟶ Y) :
    preimage α ((Grothendieck.map α).map f) = f := by
  fapply Grothendieck.ext
  · rfl
  · simp only [eqToHom_refl, Category.id_comp]
    apply (α.app Y.base).toFunctor.map_injective
    simp [preimage, Grothendieck.map]

instance map_full [∀ c, (α.app c).toFunctor.Full] : (Grothendieck.map α).Full where
  map_surjective f := ⟨preimage α f, map_preimage α f⟩

instance map_faithful [∀ c, (α.app c).toFunctor.Faithful] :
    (Grothendieck.map α).Faithful where
  map_injective {X Y} f g h := by
    cases f with | mk b p =>
      cases g with | mk c q =>
        have hb : b = c := congrArg Grothendieck.Hom.base h
        cases hb
        fapply Grothendieck.ext
        · rfl
        · simp only [eqToHom_refl, Category.id_comp]
          apply (α.app Y.base).toFunctor.map_injective
          have hf := Grothendieck.congr h
          simp [Grothendieck.map] at hf
          exact (cancel_epi _).mp hf

instance map_essSurj [∀ c, (α.app c).toFunctor.EssSurj] :
    (Grothendieck.map α).EssSurj where
  mem_essImage Y := by
    let x := (α.app Y.base).toFunctor.objPreimage Y.fiber
    refine ⟨⟨Y.base, x⟩, ⟨?_⟩⟩
    refine Grothendieck.isoMk (X := (Grothendieck.map α).obj ⟨Y.base, x⟩)
      (Y := Y) (Iso.refl Y.base) ?_
    exact eqToIso (by
      change (G.map (𝟙 Y.base)).toFunctor.obj ((α.app Y.base).toFunctor.obj x) = _
      rw [G.map_id]
      rfl) ≪≫ (α.app Y.base).toFunctor.objObjPreimageIso Y.fiber

/-- A pointwise equivalence suffices; components need not be strict
isomorphisms of categories or bijections of object representations. -/
def fiberEquivalence [∀ c, (α.app c).toFunctor.IsEquivalence] :
    Grothendieck F ≌ Grothendieck G := by
  letI : (Grothendieck.map α).IsEquivalence := {}
  exact (Grothendieck.map α).asEquivalence

/-- Combine the fiber equivalence with an equivalence of base contexts. -/
def extendEquivalence {D : Type*} [Category* D] (e : C ≌ D)
    (B : D ⥤ Cat.{z,w}) (β : F ⟶ e.functor ⋙ B)
    [∀ c, (β.app c).toFunctor.IsEquivalence] : Grothendieck F ≌ Grothendieck B :=
  (fiberEquivalence β).trans (Grothendieck.preEquivalence B e)

/-- Context extension keeps its actual base comparison. -/
theorem extendEquivalence_projection {D : Type*} [Category* D] (e : C ≌ D)
    (B : D ⥤ Cat.{z,w}) (β : F ⟶ e.functor ⋙ B)
    [∀ c, (β.app c).toFunctor.IsEquivalence] :
    (extendEquivalence e B β).functor ⋙ Grothendieck.forget B =
      Grothendieck.forget F ⋙ e.functor := rfl

/-- Identity objects descend as actual arrows under a fully faithful functor. -/
def identityEquiv {D : Type*} [Category* D] (F : C ⥤ D)
    [F.Full] [F.Faithful] (x y : C) : (x ⟶ y) ≃ (F.obj x ⟶ F.obj y) :=
  (Functor.FullyFaithful.ofFullyFaithful F).homEquiv

@[simp] theorem identityEquiv_comp {D : Type*} [Category* D] (F : C ⥤ D)
    [F.Full] [F.Faithful] {x y z : C} (p : x ⟶ y) (q : y ⟶ z) :
    identityEquiv F x z (p ≫ q) = identityEquiv F x y p ≫ identityEquiv F y z q :=
  F.map_comp p q

/-- Endpoint recovery isomorphisms conjugate the retained arrow. -/
def identityComparisonEquiv {D : Type*} [Category* D] (F : C ⥤ D)
    [F.Full] [F.Faithful] {x y : C} {x' y' : D}
    (cx : F.obj x ≅ x') (cy : F.obj y ≅ y') : (x ⟶ y) ≃ (x' ⟶ y') :=
  (identityEquiv F x y).trans (Iso.homCongr cx cy)

@[simp] theorem identityComparisonEquiv_apply {D : Type*} [Category* D] (F : C ⥤ D)
    [F.Full] [F.Faithful] {x y : C} {x' y' : D}
    (cx : F.obj x ≅ x') (cy : F.obj y ≅ y') (p : x ⟶ y) :
    identityComparisonEquiv F cx cy p = cx.inv ≫ F.map p ≫ cy.hom := rfl

end SquareKit.GrothendieckEquivalence
