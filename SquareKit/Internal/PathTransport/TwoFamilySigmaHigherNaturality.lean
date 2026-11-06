import SquareKit.Internal.PathTransport.TwoFamilySigmaNaturality

namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
universe u v w uΓ vΓ wΓ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))

private theorem boundary_right_heq {C : Type*} [Bicategory C] [Strict C]
    {a a' b c : C} (e : a' = a) {u v : a ⟶ b} (β : u ⟶ v) (q : b ⟶ c) :
    HEq ((eqToHom e ◁ β) ▷ q) (β ▷ q) := by
  cases e
  simp [Bicategory.id_whiskerLeft, Strict.leftUnitor_eqToIso,
    comp_whiskerRight, Bicategory.eqToHom_whiskerRight,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]

private theorem map_boundary_right_heq {C D : Type*} [Bicategory C] [Strict C]
    [Bicategory D] [Strict D] (H : StrictPseudofunctor C D)
    {a a' b : C} (e : a' = a) {u v : a ⟶ b} (β : u ⟶ v)
    {t : a' ⟶ b} (h : eqToHom e ≫ v = t) {c : D} (q : H.obj b ⟶ c) :
    HEq (H.map₂ (eqToHom e ◁ β ≫ eqToHom h) ▷ q) (H.map₂ β ▷ q) := by
  cases e
  simp [Bicategory.id_whiskerLeft, Strict.leftUnitor_eqToIso,
    H.map₂_comp, H.map₂_eqToHom, comp_whiskerRight, Bicategory.eqToHom_whiskerRight,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]

private theorem map_boundary_right_heq' {C D : Type*} [Bicategory C] [Strict C]
    [Bicategory D] [Strict D] (H : StrictPseudofunctor C D)
    {a a' b : C} (e : a' = a) (d : a' ⟶ a) (hd : d = eqToHom e)
    {u v : a ⟶ b} (β : u ⟶ v) {t : a' ⟶ b} (h : d ≫ v = t)
    {c : D} (q : H.obj b ⟶ c) :
    HEq (H.map₂ (d ◁ β ≫ eqToHom h) ▷ q) (H.map₂ β ▷ q) := by
  subst d
  exact map_boundary_right_heq H e β h q

private theorem map_paste₂_heq {C D : Type*} [Bicategory C] [Strict C]
    [Bicategory D] [Strict D] (H K : StrictPseudofunctor C D) (h : H = K)
    {a b : C} {u v : a ⟶ b} (β : u ⟶ v) {z : D} (k : K.obj b ⟶ z) :
    HEq (H.map₂ β ▷ (eqToHom (congrArg (fun L => L.obj b) h) ≫ k)) (K.map₂ β ▷ k) := by
  cases h
  rw [eqToHom_refl, Category.id_comp k]

private theorem sigma_higher_left_heq {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g)
    {x y : sigmaFiber F γ B} {p q : x ⟶ y} (β : p ⟶ q) :
    HEq (((sigmaMap F B f).map₂ β ▷ sigmaCellComponent F B α y).fiber)
      ((B.map (cartesianLift F f y.base ≫
        (fiberInclusion F δ).map ((F.map₂ α).app y.base))).map₂ β.fiber ▷
          (B.map₂ (cartesianComparisonCell F α y.base)).app y.fiber) := by
  change HEq (eqToHom _ ≫ (compBoundary (fiberRestriction F δ B) _ _ _ ◁
    ((B.map ((fiberInclusion F δ).map ((F.map₂ α).app y.base))).map₂
      ((sigmaMap F B f).map₂ β).fiber)) ▷ (sigmaCellComponent F B α y).fiber ≫ eqToHom _) _
  apply HEq.trans (eqToHom_comp_heq _ _)
  apply HEq.trans (comp_eqToHom_heq _ _)
  apply HEq.trans (boundary_right_heq _ _ _)
  change HEq ((B.map ((fiberInclusion F δ).map ((F.map₂ α).app y.base))).map₂
    ((eqToHom ((sigmaTransportComparison F B f).naturality p.base).symm).app x.fiber ◁
      (B.map (cartesianLift F f y.base)).map₂ β.fiber ≫ eqToHom _) ▷ _) _
  apply HEq.trans (map_boundary_right_heq'
    (B.map ((fiberInclusion F δ).map ((F.map₂ α).app y.base))) _
    ((eqToHom ((sigmaTransportComparison F B f).naturality p.base).symm).app x.fiber)
    (StrictTwoTransformation.Trans.eqToHom_app _ x.fiber)
    ((B.map (cartesianLift F f y.base)).map₂ β.fiber) _ (sigmaCellComponent F B α y).fiber)
  exact map_paste₂_heq _ _ (B.map_comp (cartesianLift F f y.base)
    ((fiberInclusion F δ).map ((F.map₂ α).app y.base))).symm β.fiber _

private theorem nested_boundary_left_heq {C : Type*} [Bicategory C] [Strict C]
    {a a' b b' c : C} (e : a' = a) (s : a ⟶ b') (d : b' = b)
    {u v : b ⟶ c} (β : u ⟶ v) {t : b' ⟶ c} (h : eqToHom d ≫ v = t) :
    HEq ((eqToHom e ≫ s) ◁ (eqToHom d ◁ β ≫ eqToHom h)) ((s ≫ eqToHom d) ◁ β) := by
  cases e
  rw [eqToHom_refl, Category.id_comp s]
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
  apply HEq.trans (comp_eqToHom_heq _ _)
  rw [nested_whiskerLeft]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

private theorem mapped_nested_left_heq {C D : Type*} [Bicategory C] [Strict C]
    [Bicategory D] [Strict D] (H : StrictPseudofunctor C D)
    {a a' b : C} (e : a' = a) (s : a ⟶ b) {b' c : D} (d : H.obj b = b')
    (j : H.obj b ⟶ b') (hj : j = eqToHom d)
    {u v : b' ⟶ c} (β : u ⟶ v) {t : H.obj b ⟶ c} (h : j ≫ v = t) :
    HEq (H.map (eqToHom e ≫ s) ◁ (j ◁ β ≫ eqToHom h)) ((H.map s ≫ j) ◁ β) := by
  subst j
  have he : H.map (eqToHom e) = eqToHom (congrArg H.obj e) := by
    cases e
    exact H.map_id _
  rw [H.map_comp, he]
  exact nested_boundary_left_heq _ _ _ _ _

private theorem sigma_higher_right_heq {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g)
    {x y : sigmaFiber F γ B} {p q : x ⟶ y} (β : p ⟶ q) :
    HEq ((sigmaCellComponent F B α x ◁ (sigmaMap F B g).map₂ β).fiber)
      (((B.map ((fiberInclusion F δ).map ((F.map g).map p.base))).map
        ((B.map₂ (cartesianComparisonCell F α x.base)).app x.fiber) ≫
          (eqToHom ((sigmaTransportComparison F B g).naturality p.base).symm).app x.fiber) ◁
            (B.map (cartesianLift F g y.base)).map₂ β.fiber) := by
  change HEq (compBoundary (fiberRestriction F δ B) _ _ _ ◁
    (((B.map ((fiberInclusion F δ).map ((F.map g).map p.base))).map
      (sigmaCellComponent F B α x).fiber) ◁ ((sigmaMap F B g).map₂ β).fiber) ≫ eqToHom _) _
  apply HEq.trans (comp_eqToHom_heq _ _)
  apply HEq.trans (eqToHom_left_heq _ _)
  change HEq ((B.map ((fiberInclusion F δ).map ((F.map g).map p.base))).map
    (eqToHom _ ≫ (B.map₂ (cartesianComparisonCell F α x.base)).app x.fiber) ◁
      ((eqToHom ((sigmaTransportComparison F B g).naturality p.base).symm).app x.fiber ◁
        (B.map (cartesianLift F g y.base)).map₂ β.fiber ≫ eqToHom _)) _
  exact mapped_nested_left_heq
    (B.map ((fiberInclusion F δ).map ((F.map g).map p.base))) _ _ _ _
    (StrictTwoTransformation.Trans.eqToHom_app _ x.fiber) _ _

private theorem classifier_comp_obj {C D E : StrictTwoCategory.{uB,vB,wB}}
    (H : C ⟶ D) (K : D ⟶ E) (x : C) : (H ≫ K).obj x = K.obj (H.obj x) := rfl

private theorem cell_comp_base {C : Type*} [Bicategory C] [Strict C] (G : Family C)
    {x y : Total G} {p q r : x ⟶ y} (α : p ⟶ q) (β : q ⟶ r) :
    (α ≫ β).base = α.base ≫ β.base := rfl

private theorem fiber_cast_right {C : Type*} [Bicategory C] [Strict C] (G : Family C)
    {x y : Total G} {p q r : x ⟶ y} (α : p ⟶ q) (h : q = r) :
    HEq (α ≫ eqToHom h).fiber α.fiber := by
  cases h
  rw [eqToHom_refl, Category.comp_id α]

private theorem fiber_cast_left {C : Type*} [Bicategory C] [Strict C] (G : Family C)
    {x y : Total G} {p q r : x ⟶ y} (h : p = q) (α : q ⟶ r) :
    HEq (eqToHom h ≫ α).fiber α.fiber := by
  cases h
  rw [eqToHom_refl, Category.id_comp α]

private theorem transformation_naturality₂_heq {C D : Type*} [Bicategory C] [Strict C]
    [Bicategory D] [Strict D] {H K : StrictPseudofunctor C D}
    (η : StrictTwoTransformation.Trans H K) {a b : C} {u v : a ⟶ b} (β : u ⟶ v) :
    HEq (H.map₂ β ▷ η.app b) (η.app a ◁ K.map₂ β) :=
  (comp_eqToHom_heq _ _).symm.trans ((heq_of_eq (η.naturality₂ β)).trans
    (eqToHom_comp_heq _ _))

private theorem whiskerLeft_heq {C : Type*} [Bicategory C]
    {a a' b c : C} (e : a = a') {s : a ⟶ b} {s' : a' ⟶ b}
    (hs : HEq s s') {u v : b ⟶ c} (β : u ⟶ v) : HEq (s ◁ β) (s' ◁ β) := by
  cases e
  cases eq_of_heq hs
  rfl

/-- Higher naturality retains both components of an arbitrary dependent total 2-cell. -/
theorem sigmaCellComponent_naturality₂ {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g)
    {x y : sigmaFiber F γ B} {p q : x ⟶ y} (β : p ⟶ q) :
    (sigmaMap F B f).map₂ β ▷ sigmaCellComponent F B α y ≫
        eqToHom (sigmaCellComponent_naturality F B α q) =
      eqToHom (sigmaCellComponent_naturality F B α p) ≫
        sigmaCellComponent F B α x ◁ (sigmaMap F B g).map₂ β := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
  · simp only [cell_comp_base (fiberRestriction F δ B), total_eqToHom_base (fiberRestriction F δ B)]
    change (F.map f).map₂ β.base ▷ (F.map₂ α).app y.base ≫
        eqToHom ((F.map₂ α).naturality q.base) =
      eqToHom ((F.map₂ α).naturality p.base) ≫
        (F.map₂ α).app x.base ◁ (F.map g).map₂ β.base
    exact (F.map₂ α).naturality₂ β.base
  · apply eq_of_heq
    simp only [heq_comp_eqToHom_iff]
    apply HEq.trans (fiber_cast_right (fiberRestriction F δ B) _ _)
    apply HEq.trans (sigma_higher_left_heq F B α β)
    apply HEq.trans _ (fiber_cast_left (fiberRestriction F δ B) _ _).symm
    apply HEq.trans _ (sigma_higher_right_heq F B α β).symm
    apply HEq.trans (transformation_naturality₂_heq
      (B.map₂ (cartesianComparisonCell F α y.base)) β.fiber)
    have he :
        (B.map (cartesianLift F f y.base ≫
          (fiberInclusion F δ).map ((F.map₂ α).app y.base))).obj
            ((B.map ((fiberInclusion F γ).map p.base)).obj x.fiber) =
        (B.map ((fiberInclusion F δ).map ((F.map g).map p.base))).obj
          ((B.map (cartesianLift F f x.base ≫
            (fiberInclusion F δ).map ((F.map₂ α).app x.base))).obj x.fiber) := by
      have h := congrArg (fun r => (B.map r).obj x.fiber)
        (cartesianComparisonCell_source F α p.base)
      simpa only [B.map_comp, classifier_comp_obj] using h
    apply whiskerLeft_heq he _ ((B.map (cartesianLift F g y.base)).map₂ β.fiber)
    rw [StrictTwoTransformation.Trans.eqToHom_app]
    exact (cartesianComparisonCell_mapped_naturality_heq F B α p.base x.fiber).trans
      (comp_eqToHom_heq _ _).symm

/-- A genuine base 2-cell induces a full strict transformation of Sigma transports. -/
def sigmaCell {γ δ : Γ} {f g : γ ⟶ δ} (α : f ⟶ g) :
    StrictTwoTransformation.Trans (sigmaMap F B f) (sigmaMap F B g) where
  app := sigmaCellComponent F B α
  naturality := sigmaCellComponent_naturality F B α
  naturality₂ := sigmaCellComponent_naturality₂ F B α

end SquareKit.Internal.PathTransport.TwoFamily
