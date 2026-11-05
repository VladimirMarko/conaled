import SquareKit.Internal.PathTransport.TwoOpenIdentity
import SquareKit.Internal.PathTransport.TwoFamilyCoherence

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

end SquareKit.Internal.PathTransport.TwoFamily
