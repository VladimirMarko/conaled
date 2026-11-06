import SquareKit.Internal.PathTransport.TwoFamilySigmaHigherNaturality
import SquareKit.Internal.PathTransport.TwoFunctorData
import SquareKit.Internal.PathTransport.TwoFamilyData
/-! Identity and composition of actual dependent Sigma transports. The proofs
retain both cell components and reuse equality of higher functor data. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
universe u v w uΓ vΓ wΓ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))

private theorem identity_heq_eqToHom {C : Type*} [Category C] {x y : C}
    (h : x = y) : HEq (𝟙 x) (eqToHom h) := by cases h; rfl

/-- The chosen lift of an identity is the total identity after its target cast. -/
theorem cartesianLift_id_heq (γ : Γ) (a : F.obj γ) :
    HEq (cartesianLift F (𝟙 γ) a) (𝟙 (show Total F from ⟨γ,a⟩)) := by
  have h : (fiberInclusion F γ).obj ((F.map (𝟙 γ)).obj a) =
      (fiberInclusion F γ).obj a := congrArg ((fiberInclusion F γ).obj)
        (congrArg (fun H : F.obj γ ⟶ F.obj γ => H.obj a) (F.map_id γ))
  apply total_hom_hext F rfl h
  · rfl
  · exact identity_heq_eqToHom
      (congrArg (fun H : F.obj γ ⟶ F.obj γ => H.obj a) (F.map_id γ))

private theorem family_map_obj_heq {C : Type*} [Bicategory C] [Strict C]
    (H : Family C) {x y y' : C} (hy : y = y') {p : x ⟶ y} {q : x ⟶ y'}
    (hp : HEq p q) (a : H.obj x) : HEq ((H.map p).obj a) ((H.map q).obj a) := by
  subst y'
  cases eq_of_heq hp
  rfl

/-- Identity transport fixes both dependent pair objects. -/
theorem sigmaMap_obj_id (γ : Γ) (x : sigmaFiber F γ B) :
    (sigmaMap F B (𝟙 γ)).obj x = x := by
  apply total_obj_hext (fiberRestriction F γ B)
  · change (F.map (𝟙 γ)).obj x.base = x.base
    exact congrArg (fun H : F.obj γ ⟶ F.obj γ => H.obj x.base) (F.map_id γ)
  · change HEq ((B.map (cartesianLift F (𝟙 γ) x.base)).obj x.fiber) x.fiber
    have h : (fiberInclusion F γ).obj ((F.map (𝟙 γ)).obj x.base) =
        (fiberInclusion F γ).obj x.base := congrArg ((fiberInclusion F γ).obj)
          (congrArg (fun H : F.obj γ ⟶ F.obj γ => H.obj x.base) (F.map_id γ))
    apply HEq.trans (family_map_obj_heq B h (cartesianLift_id_heq F γ x.base) x.fiber)
    exact heq_of_eq (congrArg (fun H : B.obj ⟨γ,x.base⟩ ⟶ B.obj ⟨γ,x.base⟩ =>
      H.obj x.fiber) (B.map_id ⟨γ,x.base⟩))

/-- The second arrow is the actual later-family action, up to its source cast. -/
theorem sigmaMap_map_fiber_heq {γ δ : Γ} (f : γ ⟶ δ)
    {x y : sigmaFiber F γ B} (p : x ⟶ y) :
    HEq ((sigmaMap F B f).map p).fiber
      ((B.map (cartesianLift F f y.base)).map p.fiber) := by
  change HEq ((eqToHom ((sigmaTransportComparison F B f).naturality p.base).symm).app x.fiber ≫
    (B.map (cartesianLift F f y.base)).map p.fiber) _
  rw [StrictTwoTransformation.Trans.eqToHom_app]
  exact eqToHom_comp_heq _ _

private theorem family_map_arrow_heq {C : Type*} [Bicategory C] [Strict C]
    (H : Family C) {x y y' : C} (hy : y = y') {p : x ⟶ y} {q : x ⟶ y'}
    (hp : HEq p q) {a b : H.obj x} (r : a ⟶ b) :
    HEq ((H.map p).map r) ((H.map q).map r) := by
  subst y'
  cases eq_of_heq hp
  rfl

private theorem functor_map_heq {C D : Type*} [Bicategory C] [Bicategory D]
    (H K : StrictPseudofunctor C D) (h : H = K) {a b : C} (r : a ⟶ b) :
    HEq (H.map r) (K.map r) := by cases h; rfl

/-- Identity transport retains the entire pair arrow. -/
theorem sigmaMap_map_id_heq (γ : Γ) {x y : sigmaFiber F γ B} (p : x ⟶ y) :
    HEq ((sigmaMap F B (𝟙 γ)).map p) p := by
  apply total_hom_hext (fiberRestriction F γ B) (sigmaMap_obj_id F B γ x)
    (sigmaMap_obj_id F B γ y)
  · exact functor_map_heq (F.map (𝟙 γ)) (StrictPseudofunctor.id (F.obj γ)) (F.map_id γ) p.base
  · apply HEq.trans (sigmaMap_map_fiber_heq F B (𝟙 γ) p)
    have h : (fiberInclusion F γ).obj ((F.map (𝟙 γ)).obj y.base) =
        (fiberInclusion F γ).obj y.base := congrArg ((fiberInclusion F γ).obj)
          (congrArg (fun H : F.obj γ ⟶ F.obj γ => H.obj y.base) (F.map_id γ))
    apply HEq.trans (family_map_arrow_heq B h (cartesianLift_id_heq F γ y.base) p.fiber)
    exact functor_map_heq _ _ (B.map_id ⟨γ,y.base⟩) p.fiber

private theorem family_map_cell_heq {C : Type*} [Bicategory C] [Strict C]
    (H : Family C) {x y y' : C} (hy : y = y') {p : x ⟶ y} {q : x ⟶ y'}
    (hp : HEq p q) {a b : H.obj x} {r t : a ⟶ b} (α : r ⟶ t) :
    HEq ((H.map p).map₂ α) ((H.map q).map₂ α) := by
  subst y'
  cases eq_of_heq hp
  rfl

private theorem functor_cell_heq {C D : Type*} [Bicategory C] [Bicategory D]
    (H K : StrictPseudofunctor C D) (h : H = K) {a b : C} {r t : a ⟶ b} (α : r ⟶ t) :
    HEq (H.map₂ α) (K.map₂ α) := by cases h; rfl

/-- Identity transport retains both genuine cell components. -/
theorem sigmaMap_cell_id_heq (γ : Γ) {x y : sigmaFiber F γ B} {p q : x ⟶ y}
    (α : p ⟶ q) : HEq ((sigmaMap F B (𝟙 γ)).map₂ α) α := by
  apply total_cell_hext (fiberRestriction F γ B) (sigmaMap_obj_id F B γ x)
    (sigmaMap_obj_id F B γ y) (sigmaMap_map_id_heq F B γ p) (sigmaMap_map_id_heq F B γ q)
  · exact functor_cell_heq _ _ (F.map_id γ) α.base
  · apply HEq.trans (sigmaMap_cell_fiber_heq F B (𝟙 γ) α)
    have h : (fiberInclusion F γ).obj ((F.map (𝟙 γ)).obj y.base) =
        (fiberInclusion F γ).obj y.base := congrArg ((fiberInclusion F γ).obj)
          (congrArg (fun H : F.obj γ ⟶ F.obj γ => H.obj y.base) (F.map_id γ))
    apply HEq.trans (family_map_cell_heq B h (cartesianLift_id_heq F γ y.base) α.fiber)
    exact functor_cell_heq _ _ (B.map_id ⟨γ,y.base⟩) α.fiber

/-- Identity base transport is the whole identity higher functor, including genuine cells. -/
theorem sigmaMap_id (γ : Γ) : sigmaMap F B (𝟙 γ) = StrictPseudofunctor.id (sigmaFiber F γ B) := by
  apply strictFunctorData_ext
  apply prelaxData_ext
  · exact sigmaMap_obj_id F B γ
  · exact fun p => sigmaMap_map_id_heq F B γ p
  · exact fun α => sigmaMap_cell_id_heq F B γ α

/-- The chosen lift of a composite is the composite of the chosen lifts. -/
theorem cartesianLift_comp_heq {γ δ ε : Γ} (f : γ ⟶ δ) (g : δ ⟶ ε) (a : F.obj γ) :
    HEq (cartesianLift F (f ≫ g) a)
      (cartesianLift F f a ≫ cartesianLift F g ((F.map f).obj a)) := by
  have h : (fiberInclusion F ε).obj ((F.map (f ≫ g)).obj a) =
      (fiberInclusion F ε).obj ((F.map g).obj ((F.map f).obj a)) :=
    congrArg ((fiberInclusion F ε).obj)
      (congrArg (fun H : F.obj γ ⟶ F.obj ε => H.obj a) (F.map_comp f g))
  apply total_hom_hext F rfl h
  · rfl
  · change HEq (𝟙 _) (eqToHom _ ≫ (F.map g).map (𝟙 _) ≫ 𝟙 _)
    rw [(F.map g).map_id, Category.id_comp, Category.comp_id]
    exact identity_heq_eqToHom
      (congrArg (fun H : F.obj γ ⟶ F.obj ε => H.obj a) (F.map_comp f g))

/-- Composite transport retains the same dependent pair object. -/
theorem sigmaMap_obj_comp {γ δ ε : Γ} (f : γ ⟶ δ) (g : δ ⟶ ε)
    (x : sigmaFiber F γ B) :
    (sigmaMap F B (f ≫ g)).obj x = (sigmaMap F B g).obj ((sigmaMap F B f).obj x) := by
  apply total_obj_hext (fiberRestriction F ε B)
  · change (F.map (f ≫ g)).obj x.base = (F.map g).obj ((F.map f).obj x.base)
    exact congrArg (fun H : F.obj γ ⟶ F.obj ε => H.obj x.base) (F.map_comp f g)
  · change HEq ((B.map (cartesianLift F (f ≫ g) x.base)).obj x.fiber)
      ((B.map (cartesianLift F g ((F.map f).obj x.base))).obj
        ((B.map (cartesianLift F f x.base)).obj x.fiber))
    have h : (fiberInclusion F ε).obj ((F.map (f ≫ g)).obj x.base) =
        (fiberInclusion F ε).obj ((F.map g).obj ((F.map f).obj x.base)) :=
      congrArg ((fiberInclusion F ε).obj)
        (congrArg (fun H : F.obj γ ⟶ F.obj ε => H.obj x.base) (F.map_comp f g))
    apply HEq.trans (family_map_obj_heq B h (cartesianLift_comp_heq F f g x.base) x.fiber)
    exact heq_of_eq (congrArg (fun H => H.obj x.fiber)
      (B.map_comp (cartesianLift F f x.base) (cartesianLift F g ((F.map f).obj x.base))))

private theorem map_left_cast_heq {C D : Type*} [Bicategory C] [Strict C] [Bicategory D]
    (H : StrictPseudofunctor C D) {a a' b : C} (e : a' = a) (p : a ⟶ b) :
    HEq (H.map (eqToHom e ≫ p)) (H.map p) := by
  cases e
  rw [eqToHom_refl, Category.id_comp]

/-- Composite transport retains the whole pair arrow, with its typed boundaries. -/
theorem sigmaMap_map_comp_heq {γ δ ε : Γ} (f : γ ⟶ δ) (g : δ ⟶ ε)
    {x y : sigmaFiber F γ B} (p : x ⟶ y) :
    HEq ((sigmaMap F B (f ≫ g)).map p) ((sigmaMap F B g).map ((sigmaMap F B f).map p)) := by
  apply total_hom_hext (fiberRestriction F ε B) (sigmaMap_obj_comp F B f g x)
    (sigmaMap_obj_comp F B f g y)
  · exact functor_map_heq _ _ (F.map_comp f g) p.base
  · apply HEq.trans (sigmaMap_map_fiber_heq F B (f ≫ g) p)
    have h : (fiberInclusion F ε).obj ((F.map (f ≫ g)).obj y.base) =
        (fiberInclusion F ε).obj ((F.map g).obj ((F.map f).obj y.base)) :=
      congrArg ((fiberInclusion F ε).obj)
        (congrArg (fun H : F.obj γ ⟶ F.obj ε => H.obj y.base) (F.map_comp f g))
    apply HEq.trans (family_map_arrow_heq B h (cartesianLift_comp_heq F f g y.base) p.fiber)
    apply HEq.trans (functor_map_heq _ _
      (B.map_comp (cartesianLift F f y.base) (cartesianLift F g ((F.map f).obj y.base))) p.fiber)
    symm
    apply HEq.trans (sigmaMap_map_fiber_heq F B g ((sigmaMap F B f).map p))
    change HEq ((B.map (cartesianLift F g ((F.map f).obj y.base))).map
      ((eqToHom ((sigmaTransportComparison F B f).naturality p.base).symm).app x.fiber ≫
        (B.map (cartesianLift F f y.base)).map p.fiber)) _
    rw [StrictTwoTransformation.Trans.eqToHom_app]
    exact map_left_cast_heq _ _ _

private theorem map_boundary_cell_heq {C D : Type*} [Bicategory C] [Strict C]
    [Bicategory D] [Strict D] (H : StrictPseudofunctor C D)
    {a a' b : C} (e : a' = a) {u v : a ⟶ b} (α : u ⟶ v)
    {t : a' ⟶ b} (h : eqToHom e ≫ v = t) :
    HEq (H.map₂ (eqToHom e ◁ α ≫ eqToHom h)) (H.map₂ α) := by
  cases e
  simp [Bicategory.id_whiskerLeft, Strict.leftUnitor_eqToIso,
    H.map₂_comp, H.map₂_eqToHom, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]

private theorem map_boundary_cell_heq' {C D : Type*} [Bicategory C] [Strict C]
    [Bicategory D] [Strict D] (H : StrictPseudofunctor C D)
    {a a' b : C} (e : a' = a) (d : a' ⟶ a) (hd : d = eqToHom e)
    {u v : a ⟶ b} (α : u ⟶ v) {t : a' ⟶ b} (h : d ≫ v = t) :
    HEq (H.map₂ (d ◁ α ≫ eqToHom h)) (H.map₂ α) := by
  subst d
  exact map_boundary_cell_heq H e α h

/-- Composite transport retains both genuine pair cell components. -/
theorem sigmaMap_cell_comp_heq {γ δ ε : Γ} (f : γ ⟶ δ) (g : δ ⟶ ε)
    {x y : sigmaFiber F γ B} {p q : x ⟶ y} (α : p ⟶ q) :
    HEq ((sigmaMap F B (f ≫ g)).map₂ α)
      ((sigmaMap F B g).map₂ ((sigmaMap F B f).map₂ α)) := by
  apply total_cell_hext (fiberRestriction F ε B) (sigmaMap_obj_comp F B f g x)
    (sigmaMap_obj_comp F B f g y) (sigmaMap_map_comp_heq F B f g p)
      (sigmaMap_map_comp_heq F B f g q)
  · exact functor_cell_heq _ _ (F.map_comp f g) α.base
  · apply HEq.trans (sigmaMap_cell_fiber_heq F B (f ≫ g) α)
    have h : (fiberInclusion F ε).obj ((F.map (f ≫ g)).obj y.base) =
        (fiberInclusion F ε).obj ((F.map g).obj ((F.map f).obj y.base)) :=
      congrArg ((fiberInclusion F ε).obj)
        (congrArg (fun H : F.obj γ ⟶ F.obj ε => H.obj y.base) (F.map_comp f g))
    apply HEq.trans (family_map_cell_heq B h (cartesianLift_comp_heq F f g y.base) α.fiber)
    apply HEq.trans (functor_cell_heq _ _
      (B.map_comp (cartesianLift F f y.base) (cartesianLift F g ((F.map f).obj y.base))) α.fiber)
    symm
    apply HEq.trans (sigmaMap_cell_fiber_heq F B g ((sigmaMap F B f).map₂ α))
    change HEq ((B.map (cartesianLift F g ((F.map f).obj y.base))).map₂
      ((eqToHom ((sigmaTransportComparison F B f).naturality p.base).symm).app x.fiber ◁
        (B.map (cartesianLift F f y.base)).map₂ α.fiber ≫ eqToHom _)) _
    exact map_boundary_cell_heq'
      (B.map (cartesianLift F g ((F.map f).obj y.base))) _
      ((eqToHom ((sigmaTransportComparison F B f).naturality p.base).symm).app x.fiber)
      (StrictTwoTransformation.Trans.eqToHom_app _ x.fiber)
      ((B.map (cartesianLift F f y.base)).map₂ α.fiber) _

/-- Sigma transport composes as whole higher functors, without erasing either cell component. -/
theorem sigmaMap_comp {γ δ ε : Γ} (f : γ ⟶ δ) (g : δ ⟶ ε) :
    sigmaMap F B (f ≫ g) = (sigmaMap F B f).comp (sigmaMap F B g) := by
  apply strictFunctorData_ext
  apply prelaxData_ext
  · exact sigmaMap_obj_comp F B f g
  · exact fun p => sigmaMap_map_comp_heq F B f g p
  · exact fun α => sigmaMap_cell_comp_heq F B f g α

/-- An identity comparison has the chosen cartesian arrow as its source. -/
theorem cartesianComparisonCell_id_source {γ δ : Γ} (f : γ ⟶ δ) (a : F.obj γ) :
    cartesianLift F f a ≫ (fiberInclusion F δ).map ((F.map₂ (𝟙 f)).app a) =
      cartesianLift F f a := by
  rw [F.map₂_id]
  change cartesianLift F f a ≫ (fiberInclusion F δ).map (𝟙 _) = _
  rw [(fiberInclusion F δ).map_id, Category.comp_id]

/-- An identity comparison is the canonical cast cell. -/
theorem cartesianComparisonCell_id {γ δ : Γ} (f : γ ⟶ δ) (a : F.obj γ) :
    cartesianComparisonCell F (𝟙 f) a = eqToHom (cartesianComparisonCell_id_source F f a) := by
  apply equalityFiber_ext F
  · rw [cartesianComparisonCell_base, total_eqToHom_base]
    simp
  · exact cartesianComparisonCell_equalityFiber F _ _
  · exact equalityFiber_cast F _

private theorem casts_heq {C : Type*} [Category C] {a b c : C}
    (h : a = c) (k : b = c) : HEq (eqToHom h) (eqToHom k) := by
  cases h
  cases k
  rfl

/-- Identity comparison acts as the identity on each dependent pair. -/
theorem sigmaCellComponent_id {γ δ : Γ} (f : γ ⟶ δ) (x : sigmaFiber F γ B) :
    sigmaCellComponent F B (𝟙 f) x = 𝟙 ((sigmaMap F B f).obj x) := by
  apply Pseudofunctor.CoGrothendieck.ext
  · change (F.map₂ (𝟙 f)).app x.base = 𝟙 _
    rw [F.map₂_id]
    rfl
  · apply HEq.trans (sigmaCellComponent_fiber_heq F B (𝟙 f) x)
    rw [cartesianComparisonCell_id, B.map₂_eqToHom, StrictTwoTransformation.Trans.eqToHom_app]
    exact casts_heq _ (congrArg (fun H => H.obj ((sigmaMap F B f).obj x).fiber)
      ((fiberRestriction F δ B).map_id ((sigmaMap F B f).obj x).base))

/-- Identity genuine cells induce identity transformations of Sigma transport. -/
theorem sigmaCell_id {γ δ : Γ} (f : γ ⟶ δ) :
    sigmaCell F B (𝟙 f) = StrictTwoTransformation.Trans.id (sigmaMap F B f) := by
  apply StrictTwoTransformation.Trans.ext
  exact sigmaCellComponent_id F B f

end SquareKit.Internal.PathTransport.TwoFamily
