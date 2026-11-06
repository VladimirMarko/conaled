import SquareKit.Internal.PathTransport.TwoFamilyHigher

/-! Inclusion of a dependent fiber, retaining its full higher structure. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (γ : Γ)

/-- Include the objects and arrows of a fiber in the dependent total category. -/
def fiberInclusionFunctor : F.obj γ ⥤ Total F where
  obj a := ⟨γ,a⟩
  map := fun {a _b} u => ⟨𝟙 γ, eqToHom (congrArg
    (fun H : F.obj γ ⟶ F.obj γ => H.obj a) (F.map_id γ)) ≫ u⟩
  map_id a := toUnderlyingHom_injective F ((Grothendieck.ι (underlying F) γ).map_id a)
  map_comp u v := toUnderlyingHom_injective F ((Grothendieck.ι (underlying F) γ).map_comp u v)

/-- The higher inclusion keeps the actual fiber 2-cell. -/
def fiberInclusionCell {a b : F.obj γ} {u v : a ⟶ b} (α : u ⟶ v) :
    (fiberInclusionFunctor F γ).map u ⟶ (fiberInclusionFunctor F γ).map v :=
  TwoGroupoidHom.cell (E := evaluation F a) (b := b)
    (f := ((fiberInclusionFunctor F γ).map u).fiber)
    (g := ((fiberInclusionFunctor F γ).map v).fiber) (𝟙 (𝟙 γ))
    (eqToHom (congrArg (fun H => H.obj a) (F.map_id γ)) ◁ α ≫ eqToHom (by
      change _ = (F.map₂ (𝟙 (𝟙 γ))).app a ≫ _
      rw [F.map₂_id]
      exact (Category.id_comp _).symm))

private theorem unop2_eqToHom {B : Type*} [Bicategory B]
    {a b : Bᵒᵖ} {f g : a ⟶ b} (h : f = g) :
    (eqToHom h).unop2 = eqToHom (congrArg Quiver.Hom.unop h) := by cases h; rfl

private theorem fiber_id {C B : Type*} [Category C] [Bicategory B] [Strict B]
    {E : C ⥤ B} {b : B} (p : TwoGroupoidHom.Total E b) :
    (𝟙 p : p ⟶ p).fiber = eqToHom (by change p.fiber = E.map (𝟙 p.base) ≫ p.fiber; simp) := by
  simp [TwoGroupoidHom.homFamily, Pseudofunctor.comp, Functor.toPseudofunctor',
    pseudofunctorOfIsLocallyDiscrete, Bicategory.yoneda₀, unop2_eqToHom,
    Bicategory.eqToHom_whiskerRight, Strict.leftUnitor_eqToIso]

private theorem identity_whisker_pasting {B : Type*} [Bicategory B] [Strict B]
    {a b : B} (δ : a ⟶ a) (hδ : δ = 𝟙 a) {f g h : a ⟶ b}
    (α : f ⟶ g) (β : g ⟶ h) (e₁ : g = δ ≫ g) (e₂ : h = δ ≫ h) :
    α ≫ β ≫ eqToHom e₂ = α ≫ eqToHom e₁ ≫ δ ◁ β := by
  subst δ
  simp [Bicategory.id_whiskerLeft, Strict.leftUnitor_eqToIso]

theorem fiberInclusionCell_id {a b : F.obj γ} (u : a ⟶ b) :
    fiberInclusionCell F γ (𝟙 u) = 𝟙 ((fiberInclusionFunctor F γ).map u) := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
  rw [fiber_id]
  simp [fiberInclusionFunctor, fiberInclusionCell, TwoGroupoidHom.cell, TwoGroupoidHom.homFamily,
    Pseudofunctor.comp, Functor.toPseudofunctor', pseudofunctorOfIsLocallyDiscrete,
    Bicategory.yoneda₀, whiskerLeft_id]

theorem fiberInclusionCell_comp {a b : F.obj γ} {u v t : a ⟶ b}
    (α : u ⟶ v) (β : v ⟶ t) :
    fiberInclusionCell F γ (α ≫ β) = fiberInclusionCell F γ α ≫ fiberInclusionCell F γ β := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (Category.id_comp _).symm ?_
  rw [fiber_comp]
  simp [fiberInclusionFunctor, fiberInclusionCell, TwoGroupoidHom.cell, TwoGroupoidHom.homFamily,
    Pseudofunctor.comp, Functor.toPseudofunctor', pseudofunctorOfIsLocallyDiscrete,
    Bicategory.yoneda₀, whiskerLeft_comp]
  exact identity_whisker_pasting ((evaluation F a).map (𝟙 (𝟙 γ)))
    ((evaluation F a).map_id _) _ _ _ _

omit [Strict Γ] in
private theorem cell_transport_fiber_heq {x y : Total F}
    {p p' q q' : Hom F x y} (hp : p = p') (hq : q = q') (α : p' ⟶ q') :
    HEq (eqToHom hp ≫ α ≫ eqToHom hq.symm).fiber α.fiber := by
  cases hp; cases hq
  simp only [eqToHom_refl]
  rw [Category.comp_id α, Category.id_comp α]

theorem fiberInclusionCell_fiber_heq {a b : F.obj γ} {u v : a ⟶ b} (α : u ⟶ v) :
    HEq (fiberInclusionCell F γ α).fiber α := by
  change HEq (eqToHom _ ◁ α ≫ eqToHom _) α
  exact (comp_eqToHom_heq _ _).trans (eqToHom_left_heq _ _)

private theorem left_identity_transport {D : Type*} [Bicategory D] [Strict D]
    (H : StrictPseudofunctor D D) (hH : H = StrictPseudofunctor.id D)
    {a b c : D} (ea : H.obj a = a) (eb : H.obj b = b)
    (δ : H.obj b ⟶ H.obj b) (hδ : δ = 𝟙 _)
    (u : a ⟶ b) {v t : b ⟶ c} (β : v ⟶ t)
    (e : eqToHom eb ≫ t = δ ≫ (eqToHom eb ≫ t)) :
    HEq (H.map (eqToHom ea ≫ u) ◁ (eqToHom eb ◁ β ≫ eqToHom e)) (u ◁ β) := by
  subst H
  subst δ
  simp [StrictPseudofunctor.id, StrictlyUnitaryPseudofunctor.id, Pseudofunctor.id,
    PrelaxFunctor.id, Bicategory.id_whiskerLeft, Strict.leftUnitor_eqToIso,
    whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom,
    Strict.associator_eqToIso, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]

omit [Strict Γ] in
private theorem cell_comp_base {x y : Total F} {p q r : Hom F x y}
    (α : p ⟶ q) (β : q ⟶ r) : (α ≫ β).base = α.base ≫ β.base := rfl

theorem fiberInclusionCell_whiskerLeft {a b c : F.obj γ} (u : a ⟶ b)
    {v t : b ⟶ c} (β : v ⟶ t) :
    fiberInclusionCell F γ (u ◁ β) =
      eqToHom ((fiberInclusionFunctor F γ).map_comp u v) ≫
        (fiberInclusionFunctor F γ).map u ◁ fiberInclusionCell F γ β ≫
          eqToHom ((fiberInclusionFunctor F γ).map_comp u t).symm := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp only [cell_comp_base F, total_eqToHom_base F]
    change 𝟙 (𝟙 γ) = eqToHom _ ≫ (𝟙 γ ◁ 𝟙 (𝟙 γ)) ≫ eqToHom _
    simp [whiskerLeft_id]
  · apply eq_of_heq
    simp only [heq_comp_eqToHom_iff]
    apply HEq.trans (fiberInclusionCell_fiber_heq F γ (u ◁ β))
    symm
    apply HEq.trans (cell_transport_fiber_heq F
      ((fiberInclusionFunctor F γ).map_comp u v) ((fiberInclusionFunctor F γ).map_comp u t) _)
    change HEq (compBoundary F (𝟙 γ) (𝟙 γ) a ◁
      ((F.map (𝟙 γ)).map ((fiberInclusionFunctor F γ).map u).fiber ◁
        (fiberInclusionCell F γ β).fiber) ≫ eqToHom _) (u ◁ β)
    apply HEq.trans (comp_eqToHom_heq _ _)
    apply HEq.trans (eqToHom_left_heq _ _)
    exact left_identity_transport (F.map (𝟙 γ)) (F.map_id γ) _ _
      ((F.map₂ (𝟙 (𝟙 γ))).app b) (by rw [F.map₂_id]; rfl) u β _

private theorem right_identity_transport {D : Type*} [Bicategory D] [Strict D]
    (H : StrictPseudofunctor D D) (hH : H = StrictPseudofunctor.id D)
    {a b c : D} (ea : H.obj a = a) (eb : H.obj b = b)
    (δ : H.obj a ⟶ H.obj a) (hδ : δ = 𝟙 _)
    {u v : a ⟶ b} (α : u ⟶ v) (q : b ⟶ c)
    (e : eqToHom ea ≫ v = δ ≫ (eqToHom ea ≫ v)) :
    HEq (H.map₂ (eqToHom ea ◁ α ≫ eqToHom e) ▷ (eqToHom eb ≫ q)) (α ▷ q) := by
  subst H
  subst δ
  simp [StrictPseudofunctor.id, StrictlyUnitaryPseudofunctor.id, Pseudofunctor.id,
    PrelaxFunctor.id, Bicategory.id_whiskerLeft, Strict.leftUnitor_eqToIso,
    comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Strict.associator_eqToIso,
    Strict.rightUnitor_eqToIso,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]

private theorem boundary_whiskerRight_heq {D : Type*} [Bicategory D] [Strict D]
    {a b c d : D} (e : a = b) {f g : b ⟶ c} (α : f ⟶ g) (q : c ⟶ d) :
    HEq ((eqToHom e ◁ α) ▷ q) (α ▷ q) := by
  rw [Bicategory.whisker_assoc]
  simp only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv]
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans (comp_eqToHom_heq _ _)
  exact eqToHom_left_heq _ _

theorem fiberInclusionCell_whiskerRight {a b c : F.obj γ} {u v : a ⟶ b}
    (α : u ⟶ v) (q : b ⟶ c) :
    fiberInclusionCell F γ (α ▷ q) =
      eqToHom ((fiberInclusionFunctor F γ).map_comp u q) ≫
        fiberInclusionCell F γ α ▷ (fiberInclusionFunctor F γ).map q ≫
          eqToHom ((fiberInclusionFunctor F γ).map_comp v q).symm := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp only [cell_comp_base F, total_eqToHom_base F]
    change 𝟙 (𝟙 γ) = eqToHom _ ≫ (𝟙 (𝟙 γ) ▷ 𝟙 γ) ≫ eqToHom _
    simp
  · apply eq_of_heq
    simp only [heq_comp_eqToHom_iff]
    apply HEq.trans (fiberInclusionCell_fiber_heq F γ (α ▷ q))
    symm
    apply HEq.trans (cell_transport_fiber_heq F
      ((fiberInclusionFunctor F γ).map_comp u q) ((fiberInclusionFunctor F γ).map_comp v q) _)
    change HEq (eqToHom _ ≫
      (compBoundary F (𝟙 γ) (𝟙 γ) a ◁ (F.map (𝟙 γ)).map₂
        (fiberInclusionCell F γ α).fiber) ▷ ((fiberInclusionFunctor F γ).map q).fiber ≫
          eqToHom _) (α ▷ q)
    apply HEq.trans (eqToHom_comp_heq _ _)
    apply HEq.trans (comp_eqToHom_heq _ _)
    apply HEq.trans (boundary_whiskerRight_heq _ _ _)
    exact right_identity_transport (F.map (𝟙 γ)) (F.map_id γ) _ _
      ((F.map₂ (𝟙 (𝟙 γ))).app a) (by rw [F.map₂_id]; rfl) α q _

/-- Canonical strict inclusion of every dependent fiber, in all three dimensions. -/
def fiberInclusion : StrictPseudofunctor (F.obj γ) (Total F) :=
  StrictPseudofunctor.mk'' {
    obj := (fiberInclusionFunctor F γ).obj
    map := (fiberInclusionFunctor F γ).map
    map₂ := fiberInclusionCell F γ
    map_id := (fiberInclusionFunctor F γ).map_id
    map_comp := (fiberInclusionFunctor F γ).map_comp
    map₂_id := fiberInclusionCell_id F γ
    map₂_comp := fiberInclusionCell_comp F γ
    map₂_whisker_left := fun u _ _ β => fiberInclusionCell_whiskerLeft F γ u β
    map₂_whisker_right := fiberInclusionCell_whiskerRight F γ
  }

universe uB vB wB
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))

/-- Restrict an arbitrary dependent family to one full higher fiber of the earlier family. -/
def fiberRestriction : Family (F.obj γ) := (fiberInclusion F γ).comp B

/-- The iterated total category supplying a dependent Sigma fiber. -/
def sigmaFiber : StrictTwoCategory.{max u uB,max v vB,max w wB} :=
  ⟨Total (fiberRestriction F γ B)⟩

instance restrictedFiberGroupoid [∀ x, IsGroupoid (B.obj x)] (a : F.obj γ) :
    IsGroupoid ((fiberRestriction F γ B).obj a) :=
  inferInstanceAs (IsGroupoid (B.obj ⟨γ,a⟩))

instance restrictedFiberLocallyGroupoid [∀ x, IsLocallyGroupoid (B.obj x)] (a : F.obj γ) :
    IsLocallyGroupoid ((fiberRestriction F γ B).obj a) :=
  inferInstanceAs (IsLocallyGroupoid (B.obj ⟨γ,a⟩))

instance sigmaFiberGroupoid [IsGroupoid (F.obj γ)] [∀ x, IsGroupoid (B.obj x)] :
    IsGroupoid (sigmaFiber F γ B) := totalIsGroupoid (fiberRestriction F γ B)

instance sigmaFiberLocallyGroupoid [IsLocallyGroupoid (F.obj γ)]
    [∀ x, IsLocallyGroupoid (B.obj x)] : IsLocallyGroupoid (sigmaFiber F γ B) :=
  totalLocallyGroupoid (fiberRestriction F γ B)

end SquareKit.Internal.PathTransport.TwoFamily
