import SquareKit.Internal.PathTransport.TwoOpenIdentity
import SquareKit.Internal.PathTransport.TwoFamilyCoherence
import SquareKit.Internal.PathTransport.TwoIdentityHomFunctoriality

/-! Higher action of the open identity family on genuine endpoint 2-cells. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, Bicategory.IsLocallyGroupoid (F.obj γ)]

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

private theorem product_eqToHom_fst {B : Type*} [Bicategory B]
    {x y : B × B} {f g : x ⟶ y} (e : f = g) :
    (eqToHom e).1 = eqToHom (congrArg Prod.fst e) := by
  cases e
  rfl
private theorem product_eqToHom_snd {B : Type*} [Bicategory B]
    {x y : B × B} {f g : x ⟶ y} (e : f = g) :
    (eqToHom e).2 = eqToHom (congrArg Prod.snd e) := by
  cases e
  rfl

theorem openIdCell_id {x y : Total (endpointFamily F)} (p : x ⟶ y) :
    openIdCell F (𝟙 p) = 𝟙 (openIdMap F p) := by
  have hid : (𝟙 p : p ⟶ p).fiber = eqToHom (by
      change p.fiber = (evaluation (endpointFamily F) x.fiber).map (𝟙 p.base) ≫ p.fiber
      simp) := fiber_id p
  have hid₁ : (𝟙 p : p ⟶ p).fiber.1 = eqToHom (by
      change p.fiber.1 = (F.map₂ (𝟙 p.base)).app x.fiber.1 ≫ p.fiber.1
      rw [F.map₂_id]
      exact (Category.id_comp _).symm) := (congrArg Prod.fst hid).trans (product_eqToHom_fst (B := F.obj y.base) _)
  have hid₂ : (𝟙 p : p ⟶ p).fiber.2 = eqToHom (by
      change p.fiber.2 = (F.map₂ (𝟙 p.base)).app x.fiber.2 ≫ p.fiber.2
      rw [F.map₂_id]
      exact (Category.id_comp _).symm) := (congrArg Prod.snd hid).trans (product_eqToHom_snd (B := F.obj y.base) _)
  ext k
  simp [openIdCell, TwoIdentityTransport.homComparison, TwoIdentityTransport.homNaturality,
    TwoIdentityTransport.inverseMate, hid₁, hid₂, Strict.associator_eqToIso,
    evaluation, endpointFamily, doubleClassifier, doubleFunctor, doubleTrans]

private theorem homComparison_congr {A B : StrictTwoCategory.{u,v,w}}
    [Bicategory.IsLocallyGroupoid B]
    {H K : StrictPseudofunctor A B} {η θ : StrictTwoTransformation.Trans H K}
    (e : η = θ) {a a' : A} {b b' : B}
    {u : H.obj a ⟶ b} {u' : K.obj a ⟶ b} [IsIso u] [IsIso u']
    {v : H.obj a' ⟶ b'} {v' : K.obj a' ⟶ b'}
    (ρ : u ⟶ θ.app a ≫ u') (σ : v ⟶ θ.app a' ≫ v') :
    TwoIdentityTransport.homComparison η
      (ρ ≫ eqToHom (congrArg (fun t => t.app a ≫ u') e.symm))
      (σ ≫ eqToHom (congrArg (fun t => t.app a' ≫ v') e.symm)) =
    TwoIdentityTransport.homComparison θ ρ σ := by
  cases e
  simp only [eqToHom_refl, Category.comp_id]

theorem openIdCell_comp {x y : Total (endpointFamily F)} {p q r : x ⟶ y}
    (α : p ⟶ q) (β : q ⟶ r) :
    openIdCell F (α ≫ β) = openIdCell F α ≫ openIdCell F β := by
  let : IsIso p.fiber.1 := IsGroupoid.all_isIso (C := F.obj y.base) p.fiber.1
  let : IsIso q.fiber.1 := IsGroupoid.all_isIso (C := F.obj y.base) q.fiber.1
  let : IsIso r.fiber.1 := IsGroupoid.all_isIso (C := F.obj y.base) r.fiber.1
  let E := evaluation (endpointFamily F) x.fiber (y := y.base)
  have h : E.map α.base ≫ E.map β.base ≫ r.fiber = E.map (α.base ≫ β.base) ≫ r.fiber := by
    rw [E.map_comp, Category.assoc]
  have hc := fiber_comp α β
  have hc₁ := congrArg Prod.fst hc
  have hc₂ := congrArg Prod.snd hc
  dsimp only [openIdCell]
  rw [← TwoIdentityTransport.homComparison_comp]
  have he : F.map₂ (α.base ≫ β.base) = (F.map₂ α.base).comp (F.map₂ β.base) :=
    F.map₂_comp α.base β.base
  have hh := homComparison_congr he
    (α.fiber.1 ≫ (F.map₂ α.base).app x.fiber.1 ◁ β.fiber.1 ≫
      eqToHom (Category.assoc _ _ _).symm)
    (α.fiber.2 ≫ (F.map₂ α.base).app x.fiber.2 ◁ β.fiber.2 ≫
      eqToHom (Category.assoc _ _ _).symm)
  convert hh using 1
  · rfl
  · congr 1
    · change (α ≫ β).fiber.1 = α.fiber.1 ≫
        (F.map₂ α.base).app x.fiber.1 ◁ β.fiber.1 ≫ (eqToHom h).1 at hc₁
      rw [product_eqToHom_fst (B := F.obj y.base)] at hc₁
      simpa only [Category.assoc, eqToHom_trans] using hc₁
    · change (α ≫ β).fiber.2 = α.fiber.2 ≫
        (F.map₂ α.base).app x.fiber.2 ◁ β.fiber.2 ≫ (eqToHom h).2 at hc₂
      rw [product_eqToHom_snd (B := F.obj y.base)] at hc₂
      simpa only [Category.assoc, eqToHom_trans] using hc₂

/-- The complete endpoint hom-category acts functorially on identity transports. -/
noncomputable def openIdHomFunctor (x y : Total (endpointFamily F)) :
    (x ⟶ y) ⥤ ((x.fiber.1 ⟶ x.fiber.2) ⥤ (y.fiber.1 ⟶ y.fiber.2)) where
  obj := openIdMap F
  map := openIdCell F
  map_id := openIdCell_id F
  map_comp := openIdCell_comp F

/-- The identity action retains both endpoint cells and all arrows of the fiber hom-category. -/
noncomputable def openIdPrelax : PrelaxFunctor (Total (endpointFamily F)) Cat.{w,v} where
  obj x := Cat.of (x.fiber.1 ⟶ x.fiber.2)
  map p := (openIdMap F p).toCatHom
  map₂ α := (openIdCell F α).toCatHom₂
  map₂_id p := congrArg NatTrans.toCatHom₂ (openIdCell_id F p)
  map₂_comp α β := congrArg NatTrans.toCatHom₂ (openIdCell_comp F α β)

/-- Embedding the hom-groupoids preserves their arrows as higher identity paths.
Horizontal compatibility is not part of this prelax structure. -/
noncomputable def openIdHigherPrelax :
    PrelaxFunctor (Total (endpointFamily F)) StrictTwoCategory.{v,w,w} :=
  (openIdPrelax F).comp TwoIdentityTransport.locallyDiscreteEmbedding.toPrelaxFunctor

theorem openIdHigherPrelax_map_id (x : Total (endpointFamily F)) :
    (openIdHigherPrelax F).map (𝟙 x) = 𝟙 ((openIdHigherPrelax F).obj x) := by
  change TwoIdentityTransport.locallyDiscreteEmbedding.map
    ((openIdMap F (𝟙 x)).toCatHom) = _
  rw [openIdMap_id]
  exact TwoIdentityTransport.locallyDiscreteEmbedding.map_id _

theorem openIdHigherPrelax_map_comp {x y z : Total (endpointFamily F)}
    (p : x ⟶ y) (q : y ⟶ z) :
    (openIdHigherPrelax F).map (p ≫ q) =
      (openIdHigherPrelax F).map p ≫ (openIdHigherPrelax F).map q := by
  change TwoIdentityTransport.locallyDiscreteEmbedding.map
    ((openIdMap F (p ≫ q)).toCatHom) = _
  rw [openIdMap_comp]
  exact TwoIdentityTransport.locallyDiscreteEmbedding.map_comp
    (openIdMap F p).toCatHom (openIdMap F q).toCatHom

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
private theorem endpoint_comp_fst_heq {x y z : Total (endpointFamily F)}
    (p : x ⟶ y) (q : y ⟶ z) :
    HEq (p ≫ q).fiber.1 ((F.map q.base).map p.fiber.1 ≫ q.fiber.1) := by
  change HEq ((compBoundary (endpointFamily F) p.base q.base x.fiber).1 ≫
    (F.map q.base).map p.fiber.1 ≫ q.fiber.1) _
  dsimp only [compBoundary]
  rw [CategoryTheory.eqToHom_fst]
  exact eqToHom_comp_heq _ _

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
private theorem endpoint_comp_snd_heq {x y z : Total (endpointFamily F)}
    (p : x ⟶ y) (q : y ⟶ z) :
    HEq (p ≫ q).fiber.2 ((F.map q.base).map p.fiber.2 ≫ q.fiber.2) := by
  change HEq ((compBoundary (endpointFamily F) p.base q.base x.fiber).2 ≫
    (F.map q.base).map p.fiber.2 ≫ q.fiber.2) _
  dsimp only [compBoundary]
  rw [CategoryTheory.eqToHom_snd]
  exact eqToHom_comp_heq _ _

private theorem eqToHom_left_whiskerRight_heq {D : Type*} [Bicategory D] [Bicategory.Strict D]
    {a a' b c : D} (e : a = a') {f g : a' ⟶ b} (α : f ⟶ g) (q : b ⟶ c) :
    HEq ((eqToHom e ◁ α) ▷ q) (α ▷ q) := by
  cases e
  simp [Bicategory.id_whiskerLeft, Strict.leftUnitor_eqToIso]

private theorem product_comp_fst {D : Type*} [Bicategory D]
    {a b : D × D} {f g h : a ⟶ b} (α : f ⟶ g) (β : g ⟶ h) :
    (α ≫ β).1 = α.1 ≫ β.1 := rfl
private theorem product_whiskerLeft_fst {D : Type*} [Bicategory D]
    {a b c : D × D} (f : a ⟶ b) {g h : b ⟶ c} (α : g ⟶ h) :
    (f ◁ α).1 = f.1 ◁ α.1 := rfl
private theorem product_whiskerRight_fst {D : Type*} [Bicategory D]
    {a b c : D × D} {f g : a ⟶ b} (α : f ⟶ g) (h : b ⟶ c) :
    (α ▷ h).1 = α.1 ▷ h.1 := rfl

private theorem product_cast_right_fst_heq {D : Type*} [Bicategory D] [Bicategory.Strict D]
    {a a' b c : D × D} (e : a = a') {f g : a' ⟶ b} (α : f ⟶ g) (q : b ⟶ c)
    {k l : a ⟶ c} (hi : k = (eqToHom e ≫ f) ≫ q) (hj : (eqToHom e ≫ g) ≫ q = l) :
    HEq (eqToHom hi ≫ (eqToHom e ◁ α) ▷ q ≫ eqToHom hj).1 (α.1 ▷ q.1) := by
  simp only [product_comp_fst, product_eqToHom_fst, product_whiskerRight_fst,
    product_whiskerLeft_fst]
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans (comp_eqToHom_heq _ _)
  have he : (eqToHom e).1 = eqToHom (congrArg Prod.fst e) := by cases e; rfl
  change HEq (((eqToHom e).1 ◁ α.1) ▷ q.1) (α.1 ▷ q.1)
  rw [he]
  exact eqToHom_left_whiskerRight_heq _ _ _

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
private theorem endpoint_right_fst_heq {x y z : Total (endpointFamily F)}
    {p p' : x ⟶ y} (α : p ⟶ p') (q : y ⟶ z) :
    HEq (α ▷ q).fiber.1 ((F.map q.base).map₂ α.fiber.1 ▷ q.fiber.1) := by
  change HEq (TwoFamily.whiskerRight (endpointFamily F) α q).fiber.1 _
  exact product_cast_right_fst_heq (D := F.obj z.base) _ _ _ _ _

private theorem product_comp_snd {D : Type*} [Bicategory D]
    {a b : D × D} {f g h : a ⟶ b} (α : f ⟶ g) (β : g ⟶ h) :
    (α ≫ β).2 = α.2 ≫ β.2 := rfl
private theorem product_whiskerLeft_snd {D : Type*} [Bicategory D]
    {a b c : D × D} (f : a ⟶ b) {g h : b ⟶ c} (α : g ⟶ h) :
    (f ◁ α).2 = f.2 ◁ α.2 := rfl
private theorem product_whiskerRight_snd {D : Type*} [Bicategory D]
    {a b c : D × D} {f g : a ⟶ b} (α : f ⟶ g) (h : b ⟶ c) :
    (α ▷ h).2 = α.2 ▷ h.2 := rfl

private theorem product_cast_right_snd_heq {D : Type*} [Bicategory D] [Bicategory.Strict D]
    {a a' b c : D × D} (e : a = a') {f g : a' ⟶ b} (α : f ⟶ g) (q : b ⟶ c)
    {k l : a ⟶ c} (hi : k = (eqToHom e ≫ f) ≫ q) (hj : (eqToHom e ≫ g) ≫ q = l) :
    HEq (eqToHom hi ≫ (eqToHom e ◁ α) ▷ q ≫ eqToHom hj).2 (α.2 ▷ q.2) := by
  simp only [product_comp_snd, product_eqToHom_snd, product_whiskerRight_snd,
    product_whiskerLeft_snd]
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans (comp_eqToHom_heq _ _)
  have he : (eqToHom e).2 = eqToHom (congrArg Prod.snd e) := by cases e; rfl
  change HEq (((eqToHom e).2 ◁ α.2) ▷ q.2) (α.2 ▷ q.2)
  rw [he]
  exact eqToHom_left_whiskerRight_heq _ _ _

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
private theorem endpoint_right_snd_heq {x y z : Total (endpointFamily F)}
    {p p' : x ⟶ y} (α : p ⟶ p') (q : y ⟶ z) :
    HEq (α ▷ q).fiber.2 ((F.map q.base).map₂ α.fiber.2 ▷ q.fiber.2) := by
  change HEq (TwoFamily.whiskerRight (endpointFamily F) α q).fiber.2 _
  exact product_cast_right_snd_heq (D := F.obj z.base) _ _ _ _ _

/-- Right whiskering of arbitrary endpoint cells acts by later hom transport. -/
theorem openIdCell_whiskerRight {x y z : Total (endpointFamily F)}
    {p p' : x ⟶ y} (α : p ⟶ p') (q : y ⟶ z) :
    openIdCell F (α ▷ q) = eqToHom (openIdMap_comp F p q) ≫
      Functor.whiskerRight (openIdCell F α) (openIdMap F q) ≫
        eqToHom (openIdMap_comp F p' q).symm := by
  let : IsIso p.fiber.1 := IsGroupoid.all_isIso (C := F.obj y.base) _
  let : IsIso p'.fiber.1 := IsGroupoid.all_isIso (C := F.obj y.base) _
  let : IsIso q.fiber.1 := IsGroupoid.all_isIso (C := F.obj z.base) _
  let : IsIso (p ≫ q).fiber.1 := IsGroupoid.all_isIso (C := F.obj z.base) _
  let : IsIso (p' ≫ q).fiber.1 := IsGroupoid.all_isIso (C := F.obj z.base) _
  have h := TwoIdentityTransport.homComparison_whiskerRight
    (F.map₂ α.base) (F.map q.base) α.fiber.1 α.fiber.2 q.fiber.1 q.fiber.2
  have hh := heq_of_eq h
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] at hh
  apply eq_of_heq
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  refine HEq.trans ?_ hh
  have hη := heq_of_eq (F.map₂_whisker_right α.base q.base)
  simp only [F.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] at hη
  dsimp only [openIdCell]
  apply TwoIdentityTransport.homComparison_heq
    (F.map_comp p.base q.base) (F.map_comp p'.base q.base) _ _ hη
  · exact endpoint_comp_fst_heq F p q
  · exact endpoint_comp_fst_heq F p' q
  · exact endpoint_comp_snd_heq F p q
  · exact endpoint_comp_snd_heq F p' q
  · apply HEq.trans (endpoint_right_fst_heq F α q)
    symm
    simp only [comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Category.assoc,
      eqToHom_trans, comp_eqToHom_heq_iff]
    rfl
  · apply HEq.trans (endpoint_right_snd_heq F α q)
    symm
    simp only [comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Category.assoc,
      eqToHom_trans, comp_eqToHom_heq_iff]
    rfl


private theorem product_cast_left_fst_heq {D : Type*} [Bicategory D] [Bicategory.Strict D]
    {a a' b c : D × D} (e : a = a') (f : a' ⟶ b) {i j : b ⟶ c} (β : i ⟶ j)
    {l : a ⟶ c} (hj : eqToHom e ≫ (f ≫ j) = l) :
    HEq (eqToHom e ◁ (f ◁ β) ≫ eqToHom hj).1 (f.1 ◁ β.1) := by
  simp only [product_comp_fst, product_eqToHom_fst, product_whiskerLeft_fst]
  apply HEq.trans (comp_eqToHom_heq _ _)
  have he : (eqToHom e).1 = eqToHom (congrArg Prod.fst e) := by cases e; rfl
  change HEq ((eqToHom e).1 ◁ (f.1 ◁ β.1)) (f.1 ◁ β.1)
  rw [he]
  exact TwoFamily.eqToHom_left_heq _ _

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
private theorem endpoint_left_fst_heq {x y z : Total (endpointFamily F)}
    (p : x ⟶ y) {q q' : y ⟶ z} (β : q ⟶ q') :
    HEq (p ◁ β).fiber.1 ((F.map q.base).map p.fiber.1 ◁ β.fiber.1) := by
  change HEq (TwoFamily.whiskerLeft (endpointFamily F) p β).fiber.1 _
  exact product_cast_left_fst_heq (D := F.obj z.base) _ _ _ _

private theorem product_cast_left_snd_heq {D : Type*} [Bicategory D] [Bicategory.Strict D]
    {a a' b c : D × D} (e : a = a') (f : a' ⟶ b) {i j : b ⟶ c} (β : i ⟶ j)
    {l : a ⟶ c} (hj : eqToHom e ≫ (f ≫ j) = l) :
    HEq (eqToHom e ◁ (f ◁ β) ≫ eqToHom hj).2 (f.2 ◁ β.2) := by
  simp only [product_comp_snd, product_eqToHom_snd, product_whiskerLeft_snd]
  apply HEq.trans (comp_eqToHom_heq _ _)
  have he : (eqToHom e).2 = eqToHom (congrArg Prod.snd e) := by cases e; rfl
  change HEq ((eqToHom e).2 ◁ (f.2 ◁ β.2)) (f.2 ◁ β.2)
  rw [he]
  exact TwoFamily.eqToHom_left_heq _ _

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
private theorem endpoint_left_snd_heq {x y z : Total (endpointFamily F)}
    (p : x ⟶ y) {q q' : y ⟶ z} (β : q ⟶ q') :
    HEq (p ◁ β).fiber.2 ((F.map q.base).map p.fiber.2 ◁ β.fiber.2) := by
  change HEq (TwoFamily.whiskerLeft (endpointFamily F) p β).fiber.2 _
  exact product_cast_left_snd_heq (D := F.obj z.base) _ _ _ _

/-- Left whiskering of arbitrary endpoint cells acts by earlier hom transport. -/
theorem openIdCell_whiskerLeft {x y z : Total (endpointFamily F)}
    (p : x ⟶ y) {q q' : y ⟶ z} (β : q ⟶ q') :
    openIdCell F (p ◁ β) = eqToHom (openIdMap_comp F p q) ≫
      Functor.whiskerLeft (openIdMap F p) (openIdCell F β) ≫
        eqToHom (openIdMap_comp F p q').symm := by
  let : IsIso p.fiber.1 := IsGroupoid.all_isIso (C := F.obj y.base) _
  let : IsIso q.fiber.1 := IsGroupoid.all_isIso (C := F.obj z.base) _
  let : IsIso q'.fiber.1 := IsGroupoid.all_isIso (C := F.obj z.base) _
  let : IsIso (p ≫ q).fiber.1 := IsGroupoid.all_isIso (C := F.obj z.base) _
  let : IsIso (p ≫ q').fiber.1 := IsGroupoid.all_isIso (C := F.obj z.base) _
  have h := TwoIdentityTransport.homComparison_whiskerLeft
    (F.map p.base) (F.map₂ β.base) p.fiber.1 p.fiber.2 β.fiber.1 β.fiber.2
  have hh := heq_of_eq h
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] at hh
  apply eq_of_heq
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  refine HEq.trans ?_ hh
  have hη := heq_of_eq (F.map₂_whisker_left p.base β.base)
  simp only [F.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] at hη
  dsimp only [openIdCell]
  apply TwoIdentityTransport.homComparison_heq
    (F.map_comp p.base q.base) (F.map_comp p.base q'.base) _ _ hη
  · exact endpoint_comp_fst_heq F p q
  · exact endpoint_comp_fst_heq F p q'
  · exact endpoint_comp_snd_heq F p q
  · exact endpoint_comp_snd_heq F p q'
  · exact (endpoint_left_fst_heq F p β).trans (comp_eqToHom_heq _ _).symm
  · exact (endpoint_left_snd_heq F p β).trans (comp_eqToHom_heq _ _).symm

/-- Open identity transport, including horizontal endpoint composition. -/
noncomputable def openIdCat : StrictPseudofunctor (Total (endpointFamily F)) Cat.{w,v} :=
  StrictPseudofunctor.mk'' {
    __ := openIdPrelax F
    map_id := fun x => congrArg Functor.toCatHom (openIdMap_id F x)
    map_comp := fun p q => congrArg Functor.toCatHom (openIdMap_comp F p q)
    map₂_whisker_left := fun p q q' β => by
      apply Cat.Hom₂.ext
      simpa [openIdPrelax] using openIdCell_whiskerLeft F p β
    map₂_whisker_right := fun α q => by
      apply Cat.Hom₂.ext
      simpa [openIdPrelax] using openIdCell_whiskerRight F α q
  }

/-- The higher open identity family retains the full fiber hom-groupoid. -/
noncomputable def openIdHigher :
    StrictPseudofunctor (Total (endpointFamily F)) StrictTwoCategory.{v,w,w} :=
  (openIdCat F).comp TwoIdentityTransport.locallyDiscreteEmbedding

end SquareKit.Internal.PathTransport.TwoFamily
