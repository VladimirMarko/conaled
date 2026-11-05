import SquareKit.Internal.PathTransport.TwoOpenIdentityHigher
import SquareKit.Internal.PathTransport.TwoFamilyHigher
import SquareKit.Internal.PathTransport.TwoFamilyMap

/-! Path contexts retain both endpoint data and the full identity hom-groupoid. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
section DiagonalCancellation
universe uc vc wc ud vd wd
variable {A : Type uc} [Bicategory.{wc,vc} A] [Strict A]
variable {B : Type ud} [Bicategory.{wd,vd} B] [Strict B] [IsLocallyGroupoid B]
omit [IsLocallyGroupoid B] in
private theorem nested_right {a b c d : B} {f g : a ⟶ b} (α : f ⟶ g)
    (q : b ⟶ c) (r : c ⟶ d) :
    (α ▷ q) ▷ r = eqToHom (Category.assoc f q r) ≫
      α ▷ (q ≫ r) ≫ eqToHom (Category.assoc g q r).symm := by
  rw [Bicategory.whiskerRight_comp]
  simp [Strict.associator_eqToIso]

private theorem cancellation_core {a a' b : B} {u : a ⟶ b} {u' : a' ⟶ b}
    [IsIso u] [IsIso u'] {h : a ⟶ a'} (ρ : u ⟶ h ≫ u')
    (q : b ⟶ b) (hq : q = 𝟙 b) {k l : b ⟶ b}
    (hi : k = inv u ≫ u)
    (hm : inv u ≫ h ≫ u' = inv u ≫ (h ≫ u') ≫ q)
    (ht : inv u ≫ u ≫ q = l) (he : k = l) :
    eqToHom hi ≫ inv u ◁ ρ ≫ eqToHom hm ≫
      inv u ◁ (inv ρ ▷ q) ≫ eqToHom ht = eqToHom he := by
  subst q
  simp only [whiskerRight_id, Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
    whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  simp only [eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (inv u ◁ ρ) (inv u ◁ inv ρ), ← whiskerLeft_comp]
  simp only [IsIso.hom_inv_id, whiskerLeft_id, Category.id_comp, eqToHom_trans]

private theorem cancellation {a a' b : B} {u : a ⟶ b} {u' : a' ⟶ b}
    [IsIso u] [IsIso u'] {h : a ⟶ a'} (ρ : u ⟶ h ≫ u')
    (f : a ⟶ a) (g : a' ⟶ a') (hf : f = 𝟙 a) (hg : g = 𝟙 a')
    (hm : inv u ≫ f ≫ h ≫ u' = inv u ≫ (((h ≫ u') ≫ inv u') ≫ g) ≫ u')
    (ht : inv u ≫ ((u ≫ inv u') ≫ g) ≫ u' = inv u' ≫ g ≫ u')
    (he : inv u ≫ f ≫ u = inv u' ≫ g ≫ u') :
    inv u ◁ f ◁ ρ ≫ eqToHom hm ≫
      inv u ◁ inv ρ ▷ inv u' ▷ g ▷ u' ≫ eqToHom ht = eqToHom he := by
  subst f
  subst g
  simp only [id_whiskerLeft, whiskerRight_id, Strict.leftUnitor_eqToIso,
    Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv, whiskerLeft_comp,
    Bicategory.whiskerLeft_eqToHom, comp_whiskerRight, Bicategory.eqToHom_whiskerRight,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  simp only [nested_right]
  simp only [whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]
  exact cancellation_core ρ (inv u' ≫ u') (IsIso.inv_hom_id u') _ _ _ _

omit [Strict A] in
/-- Identical endpoint comparison cells preserve the identity path. -/
theorem homComparison_diagonal {H K : StrictPseudofunctor A B} (η : StrictTwoTransformation.Trans H K)
    {a : A} {b : B} {u : H.obj a ⟶ b} {u' : K.obj a ⟶ b} [IsIso u] [IsIso u']
    (ρ : u ⟶ η.app a ≫ u') :
    (TwoIdentityTransport.homComparison η ρ ρ).app (𝟙 a) =
      eqToHom (by simp [TwoIdentityTransport.homTransport, H.map_id, K.map_id]) := by
  simp [TwoIdentityTransport.homComparison, TwoIdentityTransport.homNaturality,
    TwoIdentityTransport.inverseMate, Strict.associator_eqToIso, H.map_id, K.map_id]

  exact cancellation ρ (H.map (𝟙 a)) (K.map (𝟙 a)) (H.map_id a) (K.map_id a) _ _ _

end DiagonalCancellation

universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]

/-- The context of two dependent endpoints and a path between them. -/
abbrev PathContext := Total (openIdHigher F)

instance openIdFiberGroupoid (x : Total (endpointFamily F)) :
    IsGroupoid ((openIdHigher F).obj x) := by
  change IsGroupoid (LocallyDiscrete (x.fiber.1 ⟶ x.fiber.2))
  refine ⟨fun f => ?_⟩
  let : IsIso f.as := IsGroupoid.all_isIso (C := x.fiber.1 ⟶ x.fiber.2) _
  exact ⟨⟨⟨inv f.as⟩, Discrete.ext (IsIso.hom_inv_id f.as),
    Discrete.ext (IsIso.inv_hom_id f.as)⟩⟩

instance openIdFiberLocallyGroupoid (x : Total (endpointFamily F)) :
    IsLocallyGroupoid ((openIdHigher F).obj x) := by
  change IsLocallyGroupoid (LocallyDiscrete (x.fiber.1 ⟶ x.fiber.2))
  intro a b
  change IsGroupoid (Discrete (a.as ⟶ b.as))
  infer_instance

/-- Forget the path while retaining both endpoints and all endpoint cells. -/
noncomputable def pathEndpoints :
    StrictPseudofunctor (PathContext F) (Total (endpointFamily F)) :=
  projectionHigher (openIdHigher F)

/-- Duplicate a dependent endpoint in every dimension. -/
def diagonalTotal : StrictPseudofunctor (Total F) (Total (endpointFamily F)) :=
  StrongMap.toHigher (diagonalFamily F).toStrong

/-- The first dependent endpoint, retaining its genuine cells. -/
noncomputable def pathFirst : StrictPseudofunctor (PathContext F) (Total F) :=
  (pathEndpoints F).comp (StrongMap.toHigher (firstEndpoint F).toStrong)

/-- The second dependent endpoint, retaining its genuine cells. -/
noncomputable def pathSecond : StrictPseudofunctor (PathContext F) (Total F) :=
  (pathEndpoints F).comp (StrongMap.toHigher (secondEndpoint F).toStrong)

instance pathContextGroupoid [IsGroupoid Γ] : IsGroupoid (PathContext F) :=
  totalIsGroupoid (openIdHigher F)

instance pathContextLocallyGroupoid [IsLocallyGroupoid Γ] :
    IsLocallyGroupoid (PathContext F) := totalLocallyGroupoid (openIdHigher F)

/-- A path is genuine fiber data over a common base and two endpoints. -/
def pathObject (γ : Γ) (a b : F.obj γ) (p : a ⟶ b) : PathContext F :=
  ⟨⟨γ, (a,b)⟩, ⟨p⟩⟩

/-- Reflexivity at an arbitrary dependent object is its identity arrow. -/
def pathReflexivityObj (x : Total F) : PathContext F :=
  pathObject F x.base x.fiber x.fiber (𝟙 x.fiber)

theorem pathFirst_object (γ : Γ) (a b : F.obj γ) (p : a ⟶ b) :
    (pathFirst F).obj (pathObject F γ a b p) = ⟨γ,a⟩ := rfl

theorem pathSecond_object (γ : Γ) (a b : F.obj γ) (p : a ⟶ b) :
    (pathSecond F).obj (pathObject F γ a b p) = ⟨γ,b⟩ := rfl

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
theorem diagonal_fiber_fst {x y : Total F} (p : x ⟶ y) :
    ((diagonalTotal F).map p).fiber.1 = p.fiber := by
  simp [diagonalTotal, StrongMap.toHigher, StrongMap.map,
    StrictTwoTransformation.Trans.toStrong, diagonalFamily, diagonalFunctor]
  change (𝟙 _ ≫ p.fiber) = p.fiber
  exact Category.id_comp _

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
theorem diagonal_fiber_snd {x y : Total F} (p : x ⟶ y) :
    ((diagonalTotal F).map p).fiber.2 = p.fiber := by
  simp [diagonalTotal, StrongMap.toHigher, StrongMap.map,
    StrictTwoTransformation.Trans.toStrong, diagonalFamily, diagonalFunctor]
  change (𝟙 _ ≫ p.fiber) = p.fiber
  exact Category.id_comp _

private theorem homTransport_identity {A B : Type*} [Bicategory A] [Bicategory B]
    [Strict A] [Strict B] (H : StrictPseudofunctor A B) {a : A} {b : B}
    (u : H.obj a ⟶ b) [IsIso u] :
    (TwoIdentityTransport.homTransport H u u).obj (𝟙 a) = 𝟙 b := by
  simp [TwoIdentityTransport.homTransport, H.map_id]

omit [∀ γ, IsLocallyGroupoid (F.obj γ)] in
/-- Diagonal endpoint transport preserves the identity path as an object. -/
theorem diagonal_identity {x y : Total F} (p : x ⟶ y) :
    (openIdMap F ((diagonalTotal F).map p)).obj (𝟙 x.fiber) = 𝟙 y.fiber := by
  let : IsIso p.fiber := IsGroupoid.all_isIso (C := F.obj y.base) _
  change (TwoIdentityTransport.homTransport (F.map p.base)
    ((diagonalTotal F).map p).fiber.1 ((diagonalTotal F).map p).fiber.2).obj (𝟙 x.fiber) = _
  simpa only [diagonal_fiber_fst, diagonal_fiber_snd] using
    homTransport_identity (F.map p.base) p.fiber

/-- The reflexive path over each dependent arrow uses diagonal endpoint transport. -/
noncomputable def pathReflexivityMap {x y : Total F} (p : x ⟶ y) :
    pathReflexivityObj F x ⟶ pathReflexivityObj F y :=
  ⟨(diagonalTotal F).map p, Discrete.mk (eqToHom (diagonal_identity F p))⟩

private theorem product_comp_fst {D : Type*} [Bicategory D]
    {a b : D × D} {f g h : a ⟶ b} (α : f ⟶ g) (β : g ⟶ h) :
    (α ≫ β).1 = α.1 ≫ β.1 := rfl
private theorem product_eqToHom_fst {D : Type*} [Bicategory D]
    {a b : D × D} {f g : a ⟶ b} (h : f = g) :
    (eqToHom h).1 = eqToHom (congrArg Prod.fst h) := by cases h; rfl
private theorem product_whiskerLeft_fst {D : Type*} [Bicategory D]
    {a b c : D × D} (f : a ⟶ b) {g h : b ⟶ c} (α : g ⟶ h) :
    (f ◁ α).1 = f.1 ◁ α.1 := rfl

private theorem product_cast_fst_heq {D : Type*} [Bicategory D] [Strict D]
    {a a' b : D × D} (e : a = a') {f g : a' ⟶ b} (α : f ⟶ g)
    {l : a ⟶ b} (hj : eqToHom e ≫ g = l) :
    HEq (eqToHom e ◁ α ≫ eqToHom hj).1 α.1 := by
  simp only [product_comp_fst, product_eqToHom_fst, product_whiskerLeft_fst]
  apply HEq.trans (comp_eqToHom_heq _ _)
  have he : (eqToHom e).1 = eqToHom (congrArg Prod.fst e) := by cases e; rfl
  change HEq ((eqToHom e).1 ◁ α.1) α.1
  rw [he]
  exact eqToHom_left_heq _ _

private theorem product_functor_cast_fst_heq {A D : Type*} [Bicategory A]
    [Bicategory D] [Strict D] {H K : StrictPseudofunctor A (D × D)}
    (e : H = K) (a : A) {b : D × D} {f g : K.obj a ⟶ b} (α : f ⟶ g)
    {l : H.obj a ⟶ b} (hj : (eqToHom e).app a ≫ g = l) :
    HEq ((eqToHom e).app a ◁ α ≫ eqToHom hj).1 α.1 := by
  cases e
  exact product_cast_fst_heq rfl α hj

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
/-- The diagonal retains the original fiber cell at its first endpoint. -/
theorem diagonal_cell_fst_heq {x y : Total F} {p q : x ⟶ y} (α : p ⟶ q) :
    HEq ((diagonalTotal F).map₂ α).fiber.1 α.fiber := by
  simp [diagonalTotal, StrongMap.toHigher, StrongMap.map₂,
    StrictTwoTransformation.Trans.toStrong, diagonalFamily, diagonalFunctor]
  exact product_functor_cast_fst_heq (D := F.obj y.base)
    (H := (diagonalFunctor (F.obj x.base)).comp (doubleFunctor (F.map p.base)))
    (K := (F.map p.base).comp (diagonalFunctor (F.obj y.base))) _ x.fiber
    (b := (y.fiber, y.fiber)) (f := (p.fiber, p.fiber))
    (g := ((F.map₂ α.base).app x.fiber ≫ q.fiber,
      (F.map₂ α.base).app x.fiber ≫ q.fiber)) (α.fiber, α.fiber) _

private theorem product_comp_snd {D : Type*} [Bicategory D]
    {a b : D × D} {f g h : a ⟶ b} (α : f ⟶ g) (β : g ⟶ h) :
    (α ≫ β).2 = α.2 ≫ β.2 := rfl
private theorem product_eqToHom_snd {D : Type*} [Bicategory D]
    {a b : D × D} {f g : a ⟶ b} (h : f = g) :
    (eqToHom h).2 = eqToHom (congrArg Prod.snd h) := by cases h; rfl
private theorem product_whiskerLeft_snd {D : Type*} [Bicategory D]
    {a b c : D × D} (f : a ⟶ b) {g h : b ⟶ c} (α : g ⟶ h) :
    (f ◁ α).2 = f.2 ◁ α.2 := rfl

private theorem product_cast_snd_heq {D : Type*} [Bicategory D] [Strict D]
    {a a' b : D × D} (e : a = a') {f g : a' ⟶ b} (α : f ⟶ g)
    {l : a ⟶ b} (hj : eqToHom e ≫ g = l) :
    HEq (eqToHom e ◁ α ≫ eqToHom hj).2 α.2 := by
  simp only [product_comp_snd, product_eqToHom_snd, product_whiskerLeft_snd]
  apply HEq.trans (comp_eqToHom_heq _ _)
  have he : (eqToHom e).2 = eqToHom (congrArg Prod.snd e) := by cases e; rfl
  change HEq ((eqToHom e).2 ◁ α.2) α.2
  rw [he]
  exact eqToHom_left_heq _ _

private theorem product_functor_cast_snd_heq {A D : Type*} [Bicategory A]
    [Bicategory D] [Strict D] {H K : StrictPseudofunctor A (D × D)}
    (e : H = K) (a : A) {b : D × D} {f g : K.obj a ⟶ b} (α : f ⟶ g)
    {l : H.obj a ⟶ b} (hj : (eqToHom e).app a ≫ g = l) :
    HEq ((eqToHom e).app a ◁ α ≫ eqToHom hj).2 α.2 := by
  cases e
  exact product_cast_snd_heq rfl α hj

omit [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)] in
/-- The diagonal retains the original fiber cell at its second endpoint. -/
theorem diagonal_cell_snd_heq {x y : Total F} {p q : x ⟶ y} (α : p ⟶ q) :
    HEq ((diagonalTotal F).map₂ α).fiber.2 α.fiber := by
  simp [diagonalTotal, StrongMap.toHigher, StrongMap.map₂,
    StrictTwoTransformation.Trans.toStrong, diagonalFamily, diagonalFunctor]
  exact product_functor_cast_snd_heq (D := F.obj y.base)
    (H := (diagonalFunctor (F.obj x.base)).comp (doubleFunctor (F.map p.base)))
    (K := (F.map p.base).comp (diagonalFunctor (F.obj y.base))) _ x.fiber
    (b := (y.fiber, y.fiber)) (f := (p.fiber, p.fiber))
    (g := ((F.map₂ α.base).app x.fiber ≫ q.fiber,
      (F.map₂ α.base).app x.fiber ≫ q.fiber)) (α.fiber, α.fiber) _

theorem pathFirst_map_fiber {x y : PathContext F} (p : x ⟶ y) :
    ((pathFirst F).map p).fiber = p.base.fiber.1 := by
  simp [pathFirst, pathEndpoints, projectionHigher, StrongMap.toHigher, StrongMap.map,
    StrictTwoTransformation.Trans.toStrong, firstEndpoint]
  exact Category.id_comp p.base.fiber.1

theorem pathSecond_map_fiber {x y : PathContext F} (p : x ⟶ y) :
    ((pathSecond F).map p).fiber = p.base.fiber.2 := by
  simp [pathSecond, pathEndpoints, projectionHigher, StrongMap.toHigher, StrongMap.map,
    StrictTwoTransformation.Trans.toStrong, secondEndpoint]
  exact Category.id_comp p.base.fiber.2

private theorem app_heq {C D : Type*} [Category* C] [Category* D]
    {H H' K K' : C ⥤ D} (eH : H = H') (eK : K = K')
    (η : H ⟶ K) (η' : H' ⟶ K') (h : HEq η η') (a : C) :
    HEq (η.app a) (η'.app a) := by
  cases eH; cases eK; cases eq_of_heq h; rfl

private theorem casts_heq {C : Type*} [Category* C] {a b a' b' : C}
    (h : a = b) (h' : a' = b') (ha : a = a') : HEq (eqToHom h) (eqToHom h') := by
  cases ha; cases h; cases h'; rfl

/-- Diagonal comparison retains an arbitrary cell while its two endpoints cancel on reflexivity. -/
theorem diagonal_comparison {x y : Total F} {p q : x ⟶ y} (α : p ⟶ q) :
    (openIdCell F ((diagonalTotal F).map₂ α)).app (𝟙 x.fiber) =
      eqToHom ((diagonal_identity F p).trans (diagonal_identity F q).symm) := by
  let : IsIso p.fiber := IsGroupoid.all_isIso (C := F.obj y.base) _
  let : IsIso q.fiber := IsGroupoid.all_isIso (C := F.obj y.base) _
  let : IsIso ((diagonalTotal F).map p).fiber.1 := IsGroupoid.all_isIso (C := F.obj y.base) _
  let : IsIso ((diagonalTotal F).map q).fiber.1 := IsGroupoid.all_isIso (C := F.obj y.base) _
  have ep : openIdMap F ((diagonalTotal F).map p) =
      TwoIdentityTransport.homTransport (F.map p.base) p.fiber p.fiber := by
    simp only [openIdMap, diagonal_fiber_fst, diagonal_fiber_snd]
    rfl
  have eq : openIdMap F ((diagonalTotal F).map q) =
      TwoIdentityTransport.homTransport (F.map q.base) q.fiber q.fiber := by
    simp only [openIdMap, diagonal_fiber_fst, diagonal_fiber_snd]
    rfl
  have hn : HEq (openIdCell F ((diagonalTotal F).map₂ α))
      (TwoIdentityTransport.homComparison (F.map₂ α.base) α.fiber α.fiber) := by
    dsimp only [openIdCell]
    apply TwoIdentityTransport.homComparison_heq rfl rfl _ _ (HEq.refl _)
    · exact heq_of_eq (diagonal_fiber_fst F p)
    · exact heq_of_eq (diagonal_fiber_fst F q)
    · exact heq_of_eq (diagonal_fiber_snd F p)
    · exact heq_of_eq (diagonal_fiber_snd F q)
    · exact diagonal_cell_fst_heq F α
    · exact diagonal_cell_snd_heq F α
  apply eq_of_heq
  apply HEq.trans (app_heq ep eq _ _ hn (𝟙 x.fiber))
  apply HEq.trans (heq_of_eq (homComparison_diagonal (F.map₂ α.base) α.fiber))
  exact casts_heq _ _ (congrArg (fun H => H.obj (𝟙 x.fiber)) ep.symm)

/-- Reflexivity sends every genuine dependent 2-cell to its diagonal lift. -/
noncomputable def pathReflexivityCell {x y : Total F} {p q : x ⟶ y} (α : p ⟶ q) :
    pathReflexivityMap F p ⟶ pathReflexivityMap F q :=
  TwoGroupoidHom.cell (E := evaluation (openIdHigher F) (pathReflexivityObj F x).fiber)
    (f := (pathReflexivityMap F p).fiber) (g := (pathReflexivityMap F q).fiber)
    ((diagonalTotal F).map₂ α) (eqToHom (by
      apply Discrete.ext
      change eqToHom (diagonal_identity F p) =
        (openIdCell F ((diagonalTotal F).map₂ α)).app (𝟙 x.fiber) ≫
          eqToHom (diagonal_identity F q)
      rw [diagonal_comparison, eqToHom_trans]))

end SquareKit.Internal.PathTransport.TwoFamily
