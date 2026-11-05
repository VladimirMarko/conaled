import SquareKit.Internal.PathTransport.TwoFamilyCoherence

/-! Maps of total families induced by coherent family transformations. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory StrictTwoTransformation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w u' v' w'
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]
variable {F G : Family.{u,v,w,u',v',w'} Γ}

namespace StrongMap
theorem map₂_eqToHom {A B : StrictTwoCategory.{u',v',w'}} (H : A ⟶ B)
    {a b : A} {f g : a ⟶ b} (h : f = g) :
    H.map₂ (eqToHom h) = eqToHom (congrArg H.map h) := by
  cases h
  exact H.map₂_id f

@[simp] theorem map_eqToHom {A B : StrictTwoCategory.{u',v',w'}} (H : A ⟶ B)
    {a b : A} (h : a = b) : H.map (eqToHom h) = eqToHom (congrArg H.obj h) := by
  cases h
  exact H.map_id a
@[simp] theorem classifier_eqToHom_app {A B : StrictTwoCategory.{u',v',w'}}
    {H K : A ⟶ B} (h : H = K) (a : A) :
    (eqToHom h : H ⟶ K).app a = eqToHom (congrArg (fun L => L.obj a) h) := by
  cases h
  rfl
@[simp] theorem classifier_whiskerLeft_app {A B C : StrictTwoCategory.{u',v',w'}}
    (H : A ⟶ B) {K L : B ⟶ C} (θ : K ⟶ L) (a : A) :
    (H ◁ θ).app a = θ.app (H.obj a) := rfl
@[simp] theorem classifier_whiskerRight_app {A B C : StrictTwoCategory.{u',v',w'}}
    {H K : A ⟶ B} (θ : H ⟶ K) (L : B ⟶ C) (a : A) :
    (θ ▷ L).app a = L.map (θ.app a) := rfl
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)

/-- The component functor acts on the dependent object. -/
abbrev obj (x : Total F) : Total G := ⟨x.base, (η.app x.base).obj x.fiber⟩

/-- The inverse naturality comparison supplies the required fiber arrow. -/
abbrev map {x y : Total F} (p : Hom F x y) : Hom G (obj η x) (obj η y) :=
  ⟨p.base, (η.naturality p.base).inv.app x.fiber ≫ (η.app y.base).map p.fiber⟩

omit [Bicategory.Strict Γ] in
theorem comparison_id (x : Γ) (a : F.obj x) :
    (η.naturality (𝟙 x)).inv.app a =
      eqToHom (congrArg (fun H : G.obj x ⟶ G.obj x => H.obj ((η.app x).obj a))
        (G.map_id x)) ≫
      (η.app x).map (eqToHom (congrArg (fun H : F.obj x ⟶ F.obj x => H.obj a)
        (F.map_id x)).symm) := by
  have h := congrArg (fun θ => θ.app a) (η.naturality_id_inv x)
  rw [G.mapId_eq_eqToIso, F.mapId_eq_eqToIso,
    Strict.rightUnitor_eqToIso, Strict.leftUnitor_eqToIso] at h
  repeat rw [Trans.comp_app] at h
  simp only [eqToIso.hom, eqToIso.inv] at h
  repeat rw [Trans.eqToHom_app] at h
  simpa [classifier_whiskerLeft_app, classifier_whiskerRight_app, classifier_eqToHom_app] using h

omit [Bicategory.Strict Γ] in
theorem comparison_comp {x y z : Γ} (f : x ⟶ y) (g : y ⟶ z) (a : F.obj x) :
    (η.naturality (f ≫ g)).inv.app a =
      compBoundary G f g ((η.app x).obj a) ≫
      (G.map g).map ((η.naturality f).inv.app a) ≫
      (η.naturality g).inv.app ((F.map f).obj a) ≫
      (η.app z).map (eqToHom (congrArg (fun H : F.obj x ⟶ F.obj z => H.obj a)
        (F.map_comp f g)).symm) := by
  have h := congrArg (fun θ => θ.app a) (η.naturality_comp_inv f g)
  rw [G.mapComp_eq_eqToIso, F.mapComp_eq_eqToIso] at h
  simp only [Strict.associator_eqToIso] at h
  repeat rw [Trans.comp_app] at h
  simp only [eqToIso.hom, eqToIso.inv] at h
  repeat rw [Trans.eqToHom_app] at h
  simpa [classifier_whiskerLeft_app, classifier_whiskerRight_app, classifier_eqToHom_app, compBoundary] using h

theorem map_identity (x : Total F) : map η (identity F x) = identity G (obj η x) := by
  apply toUnderlyingHom_injective G
  refine Grothendieck.ext _ _ (by rfl) ?_
  simp only [eqToHom_refl, Category.id_comp]
  change (η.naturality (𝟙 x.base)).inv.app x.fiber ≫
    (η.app x.base).map (eqToHom (congrArg (fun H : F.obj x.base ⟶ F.obj x.base => H.obj x.fiber)
      (F.map_id x.base))) = _
  rw [comparison_id]
  simp [obj, toUnderlyingHom, identity, map_eqToHom, TwoGroupoidHom.arrow]

theorem map_compose {x y z : Total F} (p : Hom F x y) (q : Hom F y z) :
    map η (compose F p q) = compose G (map η p) (map η q) := by
  apply toUnderlyingHom_injective G
  refine Grothendieck.ext _ _ (by rfl) ?_
  simp only [eqToHom_refl, Category.id_comp]
  change (η.naturality (p.base ≫ q.base)).inv.app x.fiber ≫
    (η.app z.base).map (compBoundary F p.base q.base x.fiber ≫
      (F.map q.base).map p.fiber ≫ q.fiber) = _
  rw [comparison_comp]
  simp only [(η.app z.base).map_comp, map_eqToHom, Category.assoc, compBoundary,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  change _ = compBoundary G p.base q.base ((η.app x.base).obj x.fiber) ≫
    (G.map q.base).map ((η.naturality p.base).inv.app x.fiber ≫
      (η.app y.base).map p.fiber) ≫
      (η.naturality q.base).inv.app y.fiber ≫ (η.app z.base).map q.fiber
  rw [(G.map q.base).map_comp]
  simp only [Category.assoc]
  have h := (η.naturality q.base).inv.naturality p.fiber
  change (G.map q.base).map ((η.app y.base).map p.fiber) ≫
    (η.naturality q.base).inv.app y.fiber =
    (η.naturality q.base).inv.app ((F.map p.base).obj x.fiber) ≫
      (η.app z.base).map ((F.map q.base).map p.fiber) at h
  rw [← Category.assoc ((η.naturality q.base).inv.app ((F.map p.base).obj x.fiber)),
    ← h, Category.assoc]
  rfl

/-- A coherent family transformation induces a genuine functor on total objects
and arrows; its comparison components need not be identities. -/
def toFunctor : Total F ⥤ Total G where
  obj := obj η
  map := map η
  map_id := map_identity η
  map_comp := map_compose η

omit [Bicategory.Strict Γ] in
theorem comparison_naturality {x y : Γ} {f g : x ⟶ y} (α : f ⟶ g) (a : F.obj x) :
    (η.naturality f).inv.app a ≫ (η.app y).map ((F.map₂ α).app a) =
      (G.map₂ α).app ((η.app x).obj a) ≫ (η.naturality g).inv.app a := by
  have h := congrArg (fun θ => (η.naturality f).inv ≫ θ ≫ (η.naturality g).inv)
    (η.naturality_naturality α)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] at h
  have k := congrArg (fun θ => θ.app a) h
  repeat rw [Trans.comp_app] at k
  simpa using k

/-- Transport of a total cell retains its base cell and maps its genuine fiber
2-cell. The final equality changes only its typed boundary. -/
def map₂ {x y : Total F} {p q : Hom F x y} (α : p ⟶ q) : map η p ⟶ map η q where
  base := α.base
  fiber :=
    (η.naturality p.base).inv.app x.fiber ◁ (η.app y.base).map₂ α.fiber ≫
    eqToHom (by
      change (η.naturality p.base).inv.app x.fiber ≫
        (η.app y.base).map ((F.map₂ α.base).app x.fiber ≫ q.fiber) =
        (G.map₂ α.base).app ((η.app x.base).obj x.fiber) ≫
          ((η.naturality q.base).inv.app x.fiber ≫ (η.app y.base).map q.fiber)
      rw [(η.app y.base).map_comp, ← Category.assoc, comparison_naturality,
        Category.assoc])

omit [Bicategory.Strict Γ] in
@[simp] theorem map₂_base {x y : Total F} {p q : Hom F x y} (α : p ⟶ q) :
    (map₂ η α).base = α.base := rfl

private theorem unop2_eqToHom {B : Type*} [Bicategory B] {x y : Bᵒᵖ}
    {f g : x ⟶ y} (h : f = g) :
    (eqToHom h).unop2 = eqToHom (congrArg Quiver.Hom.unop h) := by
  cases h
  rfl


private theorem fiber_id {C B : Type*} [Category C] [Bicategory B] [Bicategory.Strict B]
    {E : C ⥤ B} {b : B} (p : TwoGroupoidHom.Total E b) :
    (𝟙 p : p ⟶ p).fiber = eqToHom (by change p.fiber = E.map (𝟙 p.base) ≫ p.fiber; simp) := by
  simp [TwoGroupoidHom.homFamily, Pseudofunctor.comp, Functor.toPseudofunctor',
    pseudofunctorOfIsLocallyDiscrete, Bicategory.yoneda₀, unop2_eqToHom,
    Bicategory.eqToHom_whiskerRight, Bicategory.Strict.leftUnitor_eqToIso]

private theorem whisker_map_eqToHom {A B : StrictTwoCategory.{u',v',w'}} (H : A ⟶ B)
    {a b : A} {z : B} (c : z ⟶ H.obj a) {f g : a ⟶ b} (h : f = g) :
    c ◁ H.map₂ (eqToHom h) = eqToHom (congrArg (fun k => c ≫ H.map k) h) := by
  cases h
  change c ◁ H.map₂ (𝟙 f) = 𝟙 (c ≫ H.map f)
  exact (congrArg (fun k => c ◁ k) (H.map₂_id f)).trans (whiskerLeft_id c (H.map f))

omit [Bicategory.Strict Γ] in
set_option maxHeartbeats 20000 in
theorem map₂_id {x y : Total F} (p : Hom F x y) : map₂ η (𝟙 p) = 𝟙 (map η p) := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
  change (_ ◁ (η.app y.base).map₂ (𝟙 p : p ⟶ p).fiber) ≫ eqToHom _ =
    (𝟙 (map η p) : map η p ⟶ map η p).fiber ≫ eqToHom _
  dsimp only [obj, map]
  simp only [fiber_id]
  calc
    _ = _ := congrArg (fun z => z ≫ eqToHom _) (whisker_map_eqToHom
      (η.app y.base) ((η.naturality p.base).inv.app x.fiber) _)
    _ = _ := by simp only [eqToHom_trans]

private theorem conjugate_whiskerLeft {B : Type*} [Bicategory B]
    {a b c : B} {f g : a ⟶ b} (h : f = g) {i j : b ⟶ c} (η : i ⟶ j)
    {k l : a ⟶ c} (hi : k = f ≫ i) (hj : f ≫ j = l)
    (hi' : k = g ≫ i) (hj' : g ≫ j = l) :
    eqToHom hi ≫ f ◁ η ≫ eqToHom hj = eqToHom hi' ≫ g ◁ η ≫ eqToHom hj' := by
  cases h
  rfl

omit [Bicategory.Strict Γ] in
set_option maxHeartbeats 100000 in
/-- Coherent transport preserves vertical pasting of total 2-cells. -/
theorem map₂_comp {x y : Total F} {p q r : Hom F x y} (α : p ⟶ q) (β : q ⟶ r) :
    map₂ η (α ≫ β) = map₂ η α ≫ map₂ η β := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
  simp only [map₂, fiber_comp]
  change ((η.naturality p.base).inv.app x.fiber ◁
    (η.app y.base).map₂ (α.fiber ≫ (F.map₂ α.base).app x.fiber ◁ β.fiber ≫ eqToHom _)) ≫ eqToHom _ =
    (((η.naturality p.base).inv.app x.fiber ◁ (η.app y.base).map₂ α.fiber ≫ eqToHom _) ≫
      (G.map₂ α.base).app ((η.app x.base).obj x.fiber) ◁
        ((η.naturality q.base).inv.app x.fiber ◁ (η.app y.base).map₂ β.fiber ≫ eqToHom _) ≫
      eqToHom _) ≫ eqToHom _
  simp only [PrelaxFunctor.map₂_comp]
  simp only [Pseudofunctor.map₂_whisker_left, (η.app y.base).mapComp_eq_eqToIso,
    eqToIso.hom, eqToIso.inv, PrelaxFunctor.map₂_eqToHom, whiskerLeft_comp,
    Bicategory.whiskerLeft_eqToHom, Category.assoc, eqToHom_trans]
  simp only [nested_whiskerLeft, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  apply congrArg (fun z => ((η.naturality p.base).inv.app x.fiber ◁
    (η.app y.base).map₂ α.fiber) ≫ z)
  exact conjugate_whiskerLeft (comparison_naturality η α.base x.fiber)
    ((η.app y.base).map₂ β.fiber) _ _ _ _


/-- The complete hom-category action of a coherent family map. -/
def homFunctor (x y : Total F) : Hom F x y ⥤ Hom G (obj η x) (obj η y) where
  obj := map η
  map := map₂ η
  map_id := map₂_id η
  map_comp := map₂_comp η

end StrongMap
end SquareKit.Internal.PathTransport.TwoFamily
