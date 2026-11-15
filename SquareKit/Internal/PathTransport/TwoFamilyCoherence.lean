import SquareKit.Internal.PathTransport.TwoFamily

/-!
# Coherence of the total two-family

The existing total arrows and hom categories form a strict bicategory. Whiskering uses
actual fiber 2-cells; its laws follow from strict functoriality and naturality. Equality
transports account for the chosen composite boundaries. Interchange uses `naturality₂`,
and the pentagon and triangle use the ordinary total category's equality laws.
-/

namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w u' v' w'
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]

instance totalHomCategory (F : Family Γ) (x y : Total F) : Category (x ⟶ y) :=
  inferInstanceAs (Category (Hom F x y))

omit [Bicategory.Strict Γ] in
private theorem evaluation_map (F : Family Γ) {x y : Γ} (a : F.obj x)
    {f g : x ⟶ y} (α : f ⟶ g) : (evaluation F a).map α = (F.map₂ α).app a := rfl

private theorem unop2_eqToHom {B : Type*} [Bicategory B]
    {x y : Bᵒᵖ} {f g : x ⟶ y} (h : f = g) :
    (eqToHom h).unop2 = eqToHom (congrArg Quiver.Hom.unop h) := by
  cases h
  rfl

private theorem conjugate_whiskerLeft {B : Type*} [Bicategory B]
    {a b c : B} {f g : a ⟶ b} (h : f = g) {i j : b ⟶ c} (η : i ⟶ j)
    {k l : a ⟶ c} (hi : k = f ≫ i) (hj : f ≫ j = l)
    (hi' : k = g ≫ i) (hj' : g ≫ j = l) :
    eqToHom hi ≫ f ◁ η ≫ eqToHom hj = eqToHom hi' ≫ g ◁ η ≫ eqToHom hj' := by
  cases h
  rfl

private theorem mixed_whisker {B : Type*} [Bicategory B] [Bicategory.Strict B]
    {a b c d : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) (i : c ⟶ d) :
    (f ◁ η) ▷ i = eqToHom (Category.assoc f g i) ≫
      f ◁ (η ▷ i) ≫ eqToHom (Category.assoc f h i).symm := by
  rw [Bicategory.whisker_assoc]
  simp [Bicategory.Strict.associator_eqToIso]

theorem nested_whiskerLeft {B : Type*} [Bicategory B] [Bicategory.Strict B]
    {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) {h i : c ⟶ d} (η : h ⟶ i) :
    f ◁ g ◁ η = eqToHom (Category.assoc f g h).symm ≫
      (f ≫ g) ◁ η ≫ eqToHom (Category.assoc f g i) := by
  rw [Bicategory.comp_whiskerLeft]
  simp [Bicategory.Strict.associator_eqToIso]

theorem whiskerLeft_identity (F : Family Γ) {x y z : Total F}
    (p : Hom F x y) (q : Hom F y z) : whiskerLeft F p (𝟙 q) = 𝟙 (compose F p q) := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (Bicategory.whiskerLeft_id _ _)
  simp [whiskerLeft, TwoGroupoidHom.cell, TwoGroupoidHom.homFamily,
    Pseudofunctor.comp, Functor.toPseudofunctor', pseudofunctorOfIsLocallyDiscrete,
    Bicategory.yoneda₀, unop2_eqToHom, Bicategory.eqToHom_whiskerRight,
    Bicategory.Strict.leftUnitor_eqToIso]

theorem identity_whiskerRight (F : Family Γ) {x y z : Total F}
    (p : Hom F x y) (q : Hom F y z) : whiskerRight F (𝟙 p) q = 𝟙 (compose F p q) := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (Bicategory.id_whiskerRight _ _)
  simp [whiskerRight, TwoGroupoidHom.cell, TwoGroupoidHom.homFamily,
    Pseudofunctor.comp, Functor.toPseudofunctor', pseudofunctorOfIsLocallyDiscrete,
    Bicategory.yoneda₀, PrelaxFunctor.map₂_eqToHom, unop2_eqToHom, Bicategory.eqToHom_whiskerRight,
    Bicategory.Strict.leftUnitor_eqToIso]

theorem whiskerLeft_vertical (F : Family Γ) {x y z : Total F}
    (p : Hom F x y) {q q' q'' : Hom F y z} (β : q ⟶ q') (γ : q' ⟶ q'') :
    whiskerLeft F p (β ≫ γ) = whiskerLeft F p β ≫ whiskerLeft F p γ := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (Bicategory.whiskerLeft_comp _ _ _)
  simp [whiskerLeft, TwoGroupoidHom.cell, TwoGroupoidHom.homFamily,
    Pseudofunctor.comp, Functor.toPseudofunctor', pseudofunctorOfIsLocallyDiscrete,
    Bicategory.yoneda₀, unop2_eqToHom, Bicategory.eqToHom_whiskerRight,
    Bicategory.Strict.associator_eqToIso,
    Quiver.Hom.toLoc, Category.assoc]
  simp only [nested_whiskerLeft, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc, eqToHom_trans_assoc]

  simp only [eqToHom_trans]
  congr 2
  apply conjugate_whiskerLeft
  simp only [evaluation_map, action_whiskerLeft, compBoundary, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [(F.map₂ β.base).naturality p.fiber]
  rfl

theorem vertical_whiskerRight (F : Family Γ) {x y z : Total F}
    {p p' p'' : Hom F x y} (α : p ⟶ p') (β : p' ⟶ p'') (q : Hom F y z) :
    whiskerRight F (α ≫ β) q = whiskerRight F α q ≫ whiskerRight F β q := by
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (Bicategory.comp_whiskerRight _ _ _)
  simp [whiskerRight, TwoGroupoidHom.cell, TwoGroupoidHom.homFamily,
    Pseudofunctor.comp, Functor.toPseudofunctor', pseudofunctorOfIsLocallyDiscrete,
    Bicategory.yoneda₀, PrelaxFunctor.map₂_eqToHom, unop2_eqToHom,
    Bicategory.eqToHom_whiskerRight, Bicategory.Strict.associator_eqToIso,
    Quiver.Hom.toLoc, Category.assoc, StrictPseudofunctor.mapComp_eq_eqToIso]
  simp only [nested_whiskerLeft,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  congr 1
  apply conjugate_whiskerLeft
  simp only [evaluation_map, action_whiskerRight, compBoundary, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

theorem whiskerLeft_eqToHom (F : Family Γ) {x y z : Total F}
    (p : Hom F x y) {q q' : Hom F y z} (h : q = q') :
    whiskerLeft F p (eqToHom h) = eqToHom (congrArg (compose F p) h) := by
  cases h
  exact whiskerLeft_identity F p q

theorem eqToHom_whiskerRight (F : Family Γ) {x y z : Total F}
    {p p' : Hom F x y} (h : p = p') (q : Hom F y z) :
    whiskerRight F (eqToHom h) q = eqToHom (congrArg (fun r => compose F r q) h) := by
  cases h
  exact identity_whiskerRight F p q

omit [Bicategory.Strict Γ] in
theorem total_eqToHom_base (F : Family Γ) {x y : Total F}
    {p q : Hom F x y} (h : p = q) :
    (eqToHom h).base = eqToHom (congrArg (fun r : Hom F x y => r.base) h) := by
  cases h
  rfl

omit [Bicategory.Strict Γ] in
theorem total_eqToHom_fiber (F : Family Γ) {x y : Total F}
    {p q : Hom F x y} (h : p = q) :
    (eqToHom h).fiber = eqToHom (by
      cases h
      change p.fiber = (evaluation F x.fiber).map (𝟙 p.base) ≫ p.fiber
      rw [Functor.map_id, Category.id_comp]) := by
  cases h
  simp [TwoGroupoidHom.homFamily, Pseudofunctor.comp, Functor.toPseudofunctor',
    pseudofunctorOfIsLocallyDiscrete, Bicategory.yoneda₀, unop2_eqToHom,
    Bicategory.eqToHom_whiskerRight, Bicategory.Strict.leftUnitor_eqToIso]

section
variable {C B : Type*} [Category C] [Bicategory B] [Bicategory.Strict B]
theorem fiber_comp {E : C ⥤ B} {b : B} {p q r : TwoGroupoidHom.Total E b}
    (α : p ⟶ q) (β : q ⟶ r) :
    (α ≫ β).fiber = α.fiber ≫ E.map α.base ◁ β.fiber ≫ eqToHom (by
      change E.map α.base ≫ E.map β.base ≫ r.fiber = E.map (α.base ≫ β.base) ≫ r.fiber
      rw [E.map_comp, Category.assoc]) := by
  simp [TwoGroupoidHom.homFamily, Pseudofunctor.comp, Functor.toPseudofunctor',
    pseudofunctorOfIsLocallyDiscrete, Bicategory.yoneda₀, unop2_eqToHom,
    Bicategory.eqToHom_whiskerRight, Bicategory.Strict.associator_eqToIso]
  rfl
end

private theorem strict_map_eqToHom {A B : Type*} [Bicategory A] [Bicategory B]
    [Bicategory.Strict A] [Bicategory.Strict B]
    (H : StrictPseudofunctor A B) {a b : A} (h : a = b) :
    H.map (eqToHom h) = eqToHom (congrArg H.obj h) := by
  cases h
  exact H.map_id a

theorem identity_left_whisker (F : Family Γ) {x y : Total F}
    {p q : Hom F x y} (α : p ⟶ q)
    (hp : compose F (identity F x) p = p) (hq : compose F (identity F x) q = q) :
    whiskerLeft F (identity F x) α = eqToHom hp ≫ α ≫ eqToHom hq.symm := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, total_eqToHom_base]
    dsimp only [whiskerLeft, identity, compose, TwoGroupoidHom.arrow, TwoGroupoidHom.cell]
    convert Bicategory.id_whiskerLeft α.base using 1; simp [Bicategory.Strict.leftUnitor_eqToIso]
  · simp [whiskerLeft, TwoGroupoidHom.cell, total_eqToHom_fiber,
      TwoGroupoidHom.homFamily, Pseudofunctor.comp, Functor.toPseudofunctor',
      pseudofunctorOfIsLocallyDiscrete, Bicategory.yoneda₀, unop2_eqToHom,
      Bicategory.eqToHom_whiskerRight,
      Bicategory.Strict.associator_eqToIso, Quiver.Hom.toLoc, Category.assoc,
      total_eqToHom_base]
    simp only [nested_whiskerLeft, Category.assoc, eqToHom_trans]
    simp only [identity, compBoundary, TwoGroupoidHom.arrow]
    apply conjugate_whiskerLeft
    rw [total_eqToHom_base]
    change compBoundary F (𝟙 x.base) p.base x.fiber ≫ (F.map p.base).map (identity F x).fiber =
      (evaluation F x.fiber).map (eqToHom (congrArg (fun r : Hom F x y => r.base) hp))
    simp [identity, TwoGroupoidHom.arrow, compBoundary, strict_map_eqToHom, eqToHom_map]

section
variable {B : Type*} [Bicategory B] [Bicategory.Strict B]
theorem eqToHom_left_heq {x y z : B} (h : x = y) {f g : y ⟶ z} (α : f ⟶ g) :
    HEq (eqToHom h ◁ α) α := by
  cases h
  rw [eqToHom_refl, Bicategory.id_whiskerLeft]
  simp [Bicategory.Strict.leftUnitor_eqToIso]
theorem eqToHom_right_heq {x y z : B} {f g : x ⟶ y} (α : f ⟶ g) (h : y = z) :
    HEq (α ▷ eqToHom h) α := by
  cases h
  rw [eqToHom_refl, Bicategory.whiskerRight_id]
  simp [Bicategory.Strict.rightUnitor_eqToIso]
omit [Bicategory.Strict B] in
theorem strict_map₂_heq {A : Type*} [Bicategory A]
    {F G : StrictPseudofunctor A B} (h : F = G) {a b : A} {f g : a ⟶ b} (α : f ⟶ g) :
    HEq (F.map₂ α) (G.map₂ α) := by cases h; rfl
end

theorem identity_right_whisker (F : Family Γ) {x y : Total F}
    {p q : Hom F x y} (α : p ⟶ q)
    (hp : compose F p (identity F y) = p) (hq : compose F q (identity F y) = q) :
    whiskerRight F α (identity F y) = eqToHom hp ≫ α ≫ eqToHom hq.symm := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, total_eqToHom_base]
    dsimp only [whiskerRight, identity, compose, TwoGroupoidHom.arrow, TwoGroupoidHom.cell]
    convert Bicategory.whiskerRight_id α.base using 1; simp [Bicategory.Strict.rightUnitor_eqToIso]
  · simp [whiskerRight, TwoGroupoidHom.cell, total_eqToHom_fiber,
      TwoGroupoidHom.homFamily, Pseudofunctor.comp, Functor.toPseudofunctor',
      pseudofunctorOfIsLocallyDiscrete, Bicategory.yoneda₀, unop2_eqToHom,
      Bicategory.eqToHom_whiskerRight,
      Bicategory.Strict.associator_eqToIso, Quiver.Hom.toLoc, Category.assoc]
    simp only [identity, TwoGroupoidHom.arrow]
    simp only [compBoundary]
    apply eq_of_heq
    apply HEq.trans (b := α.fiber)
    · apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.trans (eqToHom_left_heq _ _)
      apply HEq.trans (eqToHom_right_heq _ _)
      exact strict_map₂_heq (F.map_id y.base) α.fiber
    · apply HEq.symm
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      rw [total_eqToHom_base]
      change HEq ((evaluation F x.fiber).map (eqToHom _) ◁ α.fiber) α.fiber
      rw [eqToHom_map]
      exact eqToHom_left_heq _ _

theorem compose_left_whisker (F : Family Γ) {x y z t : Total F}
    (p : Hom F x y) (q : Hom F y z) {r r' : Hom F z t} (α : r ⟶ r')
    (ha : compose F (compose F p q) r = compose F p (compose F q r))
    (hb : compose F (compose F p q) r' = compose F p (compose F q r')) :
    whiskerLeft F (compose F p q) α =
      eqToHom ha ≫ whiskerLeft F p (whiskerLeft F q α) ≫ eqToHom hb.symm := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, total_eqToHom_base]
    dsimp only [whiskerLeft, compose, TwoGroupoidHom.arrow, TwoGroupoidHom.cell]
    convert Bicategory.comp_whiskerLeft p.base q.base α.base using 1;
      simp [Bicategory.Strict.associator_eqToIso]
  · simp [whiskerLeft, TwoGroupoidHom.cell, total_eqToHom_fiber,
      TwoGroupoidHom.homFamily, Pseudofunctor.comp, Functor.toPseudofunctor',
      pseudofunctorOfIsLocallyDiscrete, Bicategory.yoneda₀, unop2_eqToHom,
      Bicategory.eqToHom_whiskerRight, Bicategory.Strict.associator_eqToIso,
      Quiver.Hom.toLoc, Category.assoc]
    simp only [nested_whiskerLeft, Bicategory.whiskerLeft_comp,
      Bicategory.whiskerLeft_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    apply conjugate_whiskerLeft
    rw [total_eqToHom_base]
    change _ = (evaluation F x.fiber).map (eqToHom _) ≫ _
    let r₀ : Hom F z ⟨t.base, (F.map r.base).obj z.fiber⟩ :=
      TwoGroupoidHom.arrow (evaluation F z.fiber) ((F.map r.base).obj z.fiber) r.base (𝟙 _)
    have h := Grothendieck.congr (Category.assoc (toUnderlyingHom F p)
      (toUnderlyingHom F q) (toUnderlyingHom F r₀))
    change compBoundary F (compose F p q).base r.base x.fiber ≫
      (F.map r.base).map (compose F p q).fiber ≫ 𝟙 _ =
      eqToHom (congrArg (evaluation F x.fiber).obj
        (congrArg (fun s : Hom F x t => s.base) ha)) ≫
      compBoundary F p.base (compose F q r).base x.fiber ≫
      (F.map (compose F q r).base).map p.fiber ≫
      compBoundary F q.base r.base y.fiber ≫ (F.map r.base).map q.fiber ≫ 𝟙 _ at h
    simpa only [Category.comp_id, eqToHom_map] using h

private theorem strict_map₂_whiskerRight_heq {A B : Type*} [Bicategory A] [Bicategory B]
    {H K : StrictPseudofunctor A B} (h : H = K) {a b : A} {f g : a ⟶ b}
    (α : f ⟶ g) {c : B} (q : H.obj b ⟶ c) (q' : K.obj b ⟶ c) (hq : HEq q q') :
    HEq (H.map₂ α ▷ q) (K.map₂ α ▷ q') := by
  cases h
  cases eq_of_heq hq
  rfl

private theorem nested_whiskerRight_heq {B : Type*} [Bicategory B] [Bicategory.Strict B]
    {a b c d : B} {f g : a ⟶ b} (α : f ⟶ g) (q : b ⟶ c) (r : c ⟶ d) :
    HEq ((α ▷ q) ▷ r) (α ▷ (q ≫ r)) := by
  rw [Bicategory.whiskerRight_comp]
  simp [Bicategory.Strict.associator_eqToIso]

private theorem total_eqToHom_left_heq (F : Family Γ) {x y : Total F}
    {p q : Hom F x y} (h : p = q) {b : F.obj y.base}
    {i j : (evaluation F x.fiber).obj q.base ⟶ b} (β : i ⟶ j) :
    HEq ((evaluation F x.fiber).map (eqToHom h).base ◁ β) β := by
  rw [total_eqToHom_base F h, eqToHom_map]
  exact eqToHom_left_heq _ _

private theorem strict_map_eqToHom_left_heq {A B : Type*} [Bicategory A] [Bicategory B]
    [Bicategory.Strict A] [Bicategory.Strict B] (H : StrictPseudofunctor A B)
    {a a' : A} (h : a = a') {b : B} {i j : H.obj a' ⟶ b} (β : i ⟶ j) :
    HEq (H.map (eqToHom h) ◁ β) β := by
  rw [strict_map_eqToHom]
  exact eqToHom_left_heq _ _

theorem whisker_right_compose (F : Family Γ) {x y z t : Total F}
    {p p' : Hom F x y} (α : p ⟶ p') (q : Hom F y z) (r : Hom F z t)
    (ha : compose F (compose F p q) r = compose F p (compose F q r))
    (hb : compose F (compose F p' q) r = compose F p' (compose F q r)) :
    whiskerRight F α (compose F q r) =
      eqToHom ha.symm ≫ whiskerRight F (whiskerRight F α q) r ≫ eqToHom hb := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, total_eqToHom_base]
    dsimp only [whiskerRight, compose, TwoGroupoidHom.arrow, TwoGroupoidHom.cell]
    convert Bicategory.whiskerRight_comp α.base q.base r.base using 1;
      simp [Bicategory.Strict.associator_eqToIso]
  · simp [whiskerRight, TwoGroupoidHom.cell, total_eqToHom_fiber,
      TwoGroupoidHom.homFamily, Pseudofunctor.comp, Functor.toPseudofunctor',
      pseudofunctorOfIsLocallyDiscrete, Bicategory.yoneda₀, unop2_eqToHom,
      Bicategory.eqToHom_whiskerRight, Bicategory.Strict.associator_eqToIso,
      PrelaxFunctor.map₂_eqToHom, StrictPseudofunctor.mapComp_eq_eqToIso,
      Quiver.Hom.toLoc, Category.assoc]
    apply eq_of_heq
    apply HEq.trans (b := (F.map r.base).map₂ ((F.map q.base).map₂ α.fiber) ▷
      ((F.map r.base).map q.fiber ≫ r.fiber))
    · apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.trans (eqToHom_left_heq _ _)
      apply strict_map₂_whiskerRight_heq (F.map_comp q.base r.base)
      exact eqToHom_comp_heq _ _
    · apply HEq.symm
      apply HEq.trans (eqToHom_comp_heq _ _)
      apply HEq.trans (comp_eqToHom_heq _ _)
      apply HEq.trans (total_eqToHom_left_heq F ha.symm _)
      apply HEq.trans (eqToHom_left_heq _ _)
      apply HEq.trans (strict_map_eqToHom_left_heq (F.map r.base) _ _)
      exact nested_whiskerRight_heq _ _ _

theorem mixed_whisker_assoc (F : Family Γ) {x y z t : Total F}
    (p : Hom F x y) {q q' : Hom F y z} (α : q ⟶ q') (r : Hom F z t)
    (ha : compose F (compose F p q) r = compose F p (compose F q r))
    (hb : compose F (compose F p q') r = compose F p (compose F q' r)) :
    whiskerRight F (whiskerLeft F p α) r =
      eqToHom ha ≫ whiskerLeft F p (whiskerRight F α r) ≫ eqToHom hb.symm := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_base, total_eqToHom_base]
    dsimp only [whiskerRight, whiskerLeft, compose, TwoGroupoidHom.arrow, TwoGroupoidHom.cell]
    convert Bicategory.whisker_assoc p.base α.base r.base using 1;
      simp [Bicategory.Strict.associator_eqToIso]
  · simp [whiskerRight, whiskerLeft, TwoGroupoidHom.cell, total_eqToHom_fiber,
      TwoGroupoidHom.homFamily, Pseudofunctor.comp, Functor.toPseudofunctor',
      pseudofunctorOfIsLocallyDiscrete, Bicategory.yoneda₀, unop2_eqToHom,
      Bicategory.eqToHom_whiskerRight, Bicategory.Strict.associator_eqToIso,
      PrelaxFunctor.map₂_eqToHom, StrictPseudofunctor.mapComp_eq_eqToIso,
      Quiver.Hom.toLoc, Category.assoc]
    simp only [nested_whiskerLeft, Bicategory.whiskerLeft_comp,
      Bicategory.whiskerLeft_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    apply conjugate_whiskerLeft
    rw [total_eqToHom_base F ha]
    change _ = (evaluation F x.fiber).map (eqToHom _) ≫ _
    let z₀ : Total F := ⟨z.base, (F.map q.base).obj y.fiber⟩
    let q₀ : Hom F y z₀ := TwoGroupoidHom.arrow (evaluation F y.fiber) z₀.fiber q.base (𝟙 _)
    let t₀ : Total F := ⟨t.base, (F.map r.base).obj z₀.fiber⟩
    let r₀ : Hom F z₀ t₀ := TwoGroupoidHom.arrow (evaluation F z₀.fiber) t₀.fiber r.base (𝟙 _)
    have h := Grothendieck.congr (Category.assoc (toUnderlyingHom F p)
      (toUnderlyingHom F q₀) (toUnderlyingHom F r₀))
    change compBoundary F (p.base ≫ q.base) r.base x.fiber ≫
      (F.map r.base).map (compBoundary F p.base q.base x.fiber ≫
        (F.map q.base).map p.fiber ≫ 𝟙 _) ≫ 𝟙 _ =
      eqToHom (congrArg (evaluation F x.fiber).obj
        (congrArg (fun s : Hom F x t => s.base) ha)) ≫
      compBoundary F p.base (q.base ≫ r.base) x.fiber ≫
      (F.map (q.base ≫ r.base)).map p.fiber ≫ compBoundary F q.base r.base y.fiber ≫
      (F.map r.base).map (𝟙 _) ≫ 𝟙 _ at h
    simpa only [(F.map r.base).map_comp, (F.map r.base).map_id,
      Category.comp_id, Category.assoc, eqToHom_map, compose, TwoGroupoidHom.arrow,
      evaluation, StrictTwoTransformation.evaluation, Functor.comp_obj] using h

theorem naturality_exchange {A B : Type*} [Bicategory A] [Bicategory B] [Bicategory.Strict B]
    {H K : StrictPseudofunctor A B} (τ : StrictTwoTransformation.Trans H K) {a b : A} {u v : a ⟶ b} (α : u ⟶ v)
    {c : B} {q : H.obj b ⟶ c} {q' : K.obj b ⟶ c} (β : q ⟶ τ.app b ≫ q') :
    H.map u ◁ β ≫ eqToHom (by rw [← Category.assoc, τ.naturality u, Category.assoc]) ≫
      τ.app a ◁ K.map₂ α ▷ q' =
    H.map₂ α ▷ q ≫ H.map v ◁ β ≫
      eqToHom (by rw [← Category.assoc, τ.naturality v, Category.assoc]) := by
  rw [← Bicategory.whisker_exchange_assoc]
  rw [Bicategory.whiskerRight_comp]
  simp only [Bicategory.Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv, Category.assoc]
  congr 1
  have h := congrArg (fun η =>
    eqToHom (Category.assoc (H.map u) (τ.app b) q').symm ≫
      (η ▷ q') ≫ eqToHom (Category.assoc (τ.app a) (K.map v) q'))
    (τ.naturality₂ α).symm
  simpa [Bicategory.whisker_assoc, Bicategory.Strict.associator_eqToIso,
    Category.assoc] using h

private theorem prefix_conjugate_heq {B : Type*} [Bicategory B]
    {a b c : B} {f g : a ⟶ b} (h : f = g) {i j : b ⟶ c} (η : i ⟶ j)
    {k l l' m : a ⟶ c} (A : m ⟶ k)
    (hi : k = f ≫ i) (hj : f ≫ j = l)
    (hi' : k = g ≫ i) (hj' : g ≫ j = l') :
    HEq (((A ≫ eqToHom hi) ≫ f ◁ η) ≫ eqToHom hj)
      (((A ≫ eqToHom hi') ≫ g ◁ η) ≫ eqToHom hj') := by
  cases h
  cases hj
  cases hj'
  rfl

theorem total_whisker_exchange (F : Family Γ) {x y z : Total F}
    {p p' : Hom F x y} (α : p ⟶ p') {q q' : Hom F y z} (β : q ⟶ q') :
    whiskerLeft F p β ≫ whiskerRight F α q' =
      whiskerRight F α q ≫ whiskerLeft F p' β := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (Bicategory.whisker_exchange α.base β.base) ?_
  simp [whiskerRight, whiskerLeft, TwoGroupoidHom.cell,
    TwoGroupoidHom.homFamily, Pseudofunctor.comp, Functor.toPseudofunctor',
    pseudofunctorOfIsLocallyDiscrete, Bicategory.yoneda₀, unop2_eqToHom,
    Bicategory.eqToHom_whiskerRight, Bicategory.Strict.associator_eqToIso,

    Quiver.Hom.toLoc, Category.assoc]
  simp only [nested_whiskerLeft, Bicategory.whiskerLeft_comp,
    Bicategory.whiskerLeft_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  have h := congrArg (fun ρ => compBoundary F p.base q.base x.fiber ◁ ρ)
    (naturality_exchange (F.map₂ β.base) α.fiber β.fiber)
  simp only [nested_whiskerLeft, Bicategory.whiskerLeft_comp,
    Bicategory.whiskerLeft_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans] at h
  have hL : (evaluation F x.fiber).map (p.base ◁ β.base) ≫
      compBoundary F p.base q'.base x.fiber =
      compBoundary F p.base q.base x.fiber ≫
        (F.map₂ β.base).app ((F.map p.base).obj x.fiber) := by
    simp only [evaluation_map, action_whiskerLeft, compBoundary, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have hR : (evaluation F x.fiber).map (α.base ▷ q.base) ≫
      compBoundary F p'.base q.base x.fiber ≫ (F.map q.base).map p'.fiber =
      compBoundary F p.base q.base x.fiber ≫
        (F.map q.base).map ((F.map₂ α.base).app x.fiber ≫ p'.fiber) := by
    simp only [evaluation_map, action_whiskerRight, compBoundary, Category.assoc,
      (F.map q.base).map_comp, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [← Category.assoc] at h ⊢
  apply eq_of_heq
  refine HEq.trans ?_ (HEq.trans (heq_of_eq h) ?_)
  · exact prefix_conjugate_heq hL _ _ _ _ _ _
  · exact (prefix_conjugate_heq hR _ _ _ _ _ _).symm


/-- The total bicategory retains the given base and fiber 2-cells. -/
instance totalBicategory (F : Family Γ) : Bicategory (Total F) where
  toCategoryStruct := (totalCategory F).toCategoryStruct
  homCategory := totalHomCategory F
  whiskerLeft := whiskerLeft F
  whiskerRight := whiskerRight F
  associator p q r := eqToIso (Category.assoc p q r)
  leftUnitor p := eqToIso (Category.id_comp p)
  rightUnitor p := eqToIso (Category.comp_id p)
  whiskerLeft_id := whiskerLeft_identity F
  whiskerLeft_comp := whiskerLeft_vertical F
  id_whiskerLeft α := identity_left_whisker F α ((totalCategory F).id_comp _) ((totalCategory F).id_comp _)
  comp_whiskerLeft := by
    intro a b c d p q r r' α
    exact compose_left_whisker F p q α (Category.assoc p q r) (Category.assoc p q r')
  id_whiskerRight := identity_whiskerRight F
  comp_whiskerRight := vertical_whiskerRight F
  whiskerRight_id α := identity_right_whisker F α ((totalCategory F).comp_id _) ((totalCategory F).comp_id _)
  whiskerRight_comp α q r := whisker_right_compose F α q r (Category.assoc _ q r) (Category.assoc _ q r)
  whisker_assoc := by
    intro a b c d p q q' α r
    exact mixed_whisker_assoc F p α r (Category.assoc p q r) (Category.assoc p q' r)
  whisker_exchange α β := total_whisker_exchange F α β
  pentagon p q r s := by
    simp only [eqToIso.hom]
    rw [TwoFamily.eqToHom_whiskerRight F, TwoFamily.whiskerLeft_eqToHom F]
    simp only [eqToHom_trans]
  triangle p q := by
    simp only [eqToIso.hom]
    rw [TwoFamily.eqToHom_whiskerRight F, TwoFamily.whiskerLeft_eqToHom F]
    simp only [eqToHom_trans]

/-- The structural isomorphisms are the total category's equality transports. -/
instance totalStrict (F : Family Γ) : Bicategory.Strict (Total F) where
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso := by
    intro a b c d p q r
    rfl

end SquareKit.Internal.PathTransport.TwoFamily
