import SquareKit.Internal.PathTransport.TwoFamilySigmaCellLaws

/-! Horizontal coherence and assembly of the actual dependent pair family. -/
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

private theorem comparisonTarget_comp {γ δ ε : Γ} (f : γ ⟶ δ) (g : δ ⟶ ε) (a : F.obj γ) :
    (fiberInclusion F ε).obj ((F.map (f ≫ g)).obj a) =
      (fiberInclusion F ε).obj ((F.map g).obj ((F.map f).obj a)) :=
  congrArg ((fiberInclusion F ε).obj)
    (congrArg (fun H : F.obj γ ⟶ F.obj ε => H.obj a) (F.map_comp f g))

theorem cartesianComparisonCell_left_source_heq {γ δ ε : Γ} (f : γ ⟶ δ)
    {g h : δ ⟶ ε} (α : g ⟶ h) (a : F.obj γ) :
    HEq (cartesianLift F (f ≫ g) a ≫ (fiberInclusion F ε).map ((F.map₂ (f ◁ α)).app a))
      (cartesianLift F f a ≫
        (cartesianLift F g ((F.map f).obj a) ≫
          (fiberInclusion F ε).map ((F.map₂ α).app ((F.map f).obj a)))) := by
  rw [cartesianLift_factorization F (x := ⟨γ,a⟩)
    (y := ⟨ε,(F.map (f ≫ h)).obj a⟩) ⟨f ≫ g,(F.map₂ (f ◁ α)).app a⟩]
  rw [cartesianLift_factorization F (x := ⟨δ,(F.map f).obj a⟩)
    (y := ⟨ε,(F.map h).obj ((F.map f).obj a)⟩) ⟨g,(F.map₂ α).app ((F.map f).obj a)⟩]
  apply total_hom_hext F rfl (comparisonTarget_comp F f h a)
  · rfl
  · change HEq ((F.map₂ (f ◁ α)).app a)
      (eqToHom _ ≫ (F.map g).map (𝟙 _) ≫ (F.map₂ α).app ((F.map f).obj a))
    rw [action_whiskerLeft, (F.map g).map_id, Category.id_comp]
    simp only [compBoundary, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff, heq_eqToHom_comp_iff]
    rfl

private theorem equalityFiber_hext {x x' y y' : Total F} (hx : x = x') (hy : y = y')
    {p q : x ⟶ y} {p' q' : x' ⟶ y'} (hp : HEq p p') (hq : HEq q q')
    (α : p ⟶ q) (β : p' ⟶ q') (hb : HEq α.base β.base)
    (hα : EqualityFiber F α) (hβ : EqualityFiber F β) : HEq α β := by
  subst x'
  subst y'
  cases eq_of_heq hp
  cases eq_of_heq hq
  exact heq_of_eq (equalityFiber_ext F (eq_of_heq hb) hα hβ)

theorem cartesianComparisonCell_left_heq {γ δ ε : Γ} (f : γ ⟶ δ)
    {g h : δ ⟶ ε} (α : g ⟶ h) (a : F.obj γ) :
    HEq (cartesianComparisonCell F (f ◁ α) a)
      (cartesianLift F f a ◁ cartesianComparisonCell F α ((F.map f).obj a)) := by
  apply equalityFiber_hext F rfl (comparisonTarget_comp F f h a)
    (cartesianComparisonCell_left_source_heq F f α a) (cartesianLift_comp_heq F f h a)
  · change HEq (cartesianComparisonCell F (f ◁ α) a).base
      (f ◁ (cartesianComparisonCell F α ((F.map f).obj a)).base)
    rw [cartesianComparisonCell_base, cartesianComparisonCell_base]
    simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom,
      eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
    rfl
  · exact cartesianComparisonCell_equalityFiber F _ _
  · exact equalityFiber_whiskerLeft F _ (cartesianComparisonCell_equalityFiber F _ _)

private theorem mapped_cell_heq {a b b' : Total F} (e : b = b')
    {p q : a ⟶ b} {p' q' : a ⟶ b'} (hp : HEq p p') (hq : HEq q q')
    {α : p ⟶ q} {β : p' ⟶ q'} (h : HEq α β) (x : B.obj a) :
    HEq ((B.map₂ α).app x) ((B.map₂ β).app x) := by
  subst b'
  cases eq_of_heq hp
  cases eq_of_heq hq
  cases eq_of_heq h
  rfl

theorem sigmaCellComponent_left_heq {γ δ ε : Γ} (f : γ ⟶ δ)
    {g h : δ ⟶ ε} (α : g ⟶ h) (x : sigmaFiber F γ B) :
    HEq (sigmaCellComponent F B (f ◁ α) x)
      (sigmaCellComponent F B α ((sigmaMap F B f).obj x)) := by
  apply total_hom_hext (fiberRestriction F ε B)
    (sigmaMap_obj_comp F B f g x) (sigmaMap_obj_comp F B f h x)
  · change HEq ((F.map₂ (f ◁ α)).app x.base) ((F.map₂ α).app ((F.map f).obj x.base))
    rw [action_whiskerLeft]
    simp only [compBoundary, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl
  · apply HEq.trans (sigmaCellComponent_fiber_heq F B (f ◁ α) x)
    have hmap := mapped_cell_heq F B (comparisonTarget_comp F f h x.base)
      (cartesianComparisonCell_left_source_heq F f α x.base)
      (cartesianLift_comp_heq F f h x.base)
      (cartesianComparisonCell_left_heq F f α x.base) x.fiber
    apply HEq.trans hmap
    rw [action_whiskerLeft]
    change HEq (eqToHom _ ≫ (B.map₂ (cartesianComparisonCell F α ((F.map f).obj x.base))).app
      ((B.map (cartesianLift F f x.base)).obj x.fiber) ≫ eqToHom _) _
    apply HEq.trans (eqToHom_comp_heq _ _)
    apply HEq.trans (comp_eqToHom_heq _ _)
    exact (sigmaCellComponent_fiber_heq F B α ((sigmaMap F B f).obj x)).symm

theorem sigmaCell_whiskerLeft {γ δ ε : Γ} (f : γ ⟶ δ)
    {g h : δ ⟶ ε} (α : g ⟶ h) :
    sigmaCell F B (f ◁ α) =
      eqToHom (sigmaMap_comp F B f g) ≫
        (StrictTwoTransformation.Trans.whiskerLeft (sigmaMap F B f) (sigmaCell F B α)) ≫
          eqToHom (sigmaMap_comp F B f h).symm := by
  apply StrictTwoTransformation.Trans.ext
  intro x
  apply eq_of_heq
  repeat rw [StrictTwoTransformation.Trans.comp_app]
  repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact sigmaCellComponent_left_heq F B f α x

theorem cartesianComparisonCell_right_source_heq {γ δ ε : Γ}
    {f g : γ ⟶ δ} (α : f ⟶ g) (h : δ ⟶ ε) (a : F.obj γ) :
    HEq (cartesianLift F (f ≫ h) a ≫ (fiberInclusion F ε).map ((F.map₂ (α ▷ h)).app a))
      ((cartesianLift F f a ≫ (fiberInclusion F δ).map ((F.map₂ α).app a)) ≫
        cartesianLift F h ((F.map g).obj a)) := by
  rw [Category.assoc, cartesianLift_naturality]
  rw [cartesianLift_factorization F (x := ⟨γ,a⟩)
    (y := ⟨ε,(F.map (g ≫ h)).obj a⟩) ⟨f ≫ h,(F.map₂ (α ▷ h)).app a⟩]
  rw [cartesianLift_factorization F (x := ⟨δ,(F.map f).obj a⟩)
    (y := ⟨ε,(F.map h).obj ((F.map g).obj a)⟩)
      ⟨h,(F.map h).map ((F.map₂ α).app a)⟩]
  apply total_hom_hext F rfl (comparisonTarget_comp F g h a)
  · rfl
  · change HEq ((F.map₂ (α ▷ h)).app a)
      (eqToHom _ ≫ (F.map h).map (𝟙 _) ≫ (F.map h).map ((F.map₂ α).app a))
    rw [action_whiskerRight, (F.map h).map_id, Category.id_comp]
    simp only [compBoundary, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff]
    rfl

theorem cartesianComparisonCell_right_heq {γ δ ε : Γ}
    {f g : γ ⟶ δ} (α : f ⟶ g) (h : δ ⟶ ε) (a : F.obj γ) :
    HEq (cartesianComparisonCell F (α ▷ h) a)
      (cartesianComparisonCell F α a ▷ cartesianLift F h ((F.map g).obj a)) := by
  apply equalityFiber_hext F rfl (comparisonTarget_comp F g h a)
    (cartesianComparisonCell_right_source_heq F α h a) (cartesianLift_comp_heq F g h a)
  · change HEq (cartesianComparisonCell F (α ▷ h) a).base
      ((cartesianComparisonCell F α a).base ▷ h)
    rw [cartesianComparisonCell_base, cartesianComparisonCell_base]
    simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight,
      eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
    rfl
  · exact cartesianComparisonCell_equalityFiber F _ _
  · exact equalityFiber_whiskerRight F (cartesianComparisonCell_equalityFiber F _ _) _

theorem sigmaCellComponent_right_heq {γ δ ε : Γ}
    {f g : γ ⟶ δ} (α : f ⟶ g) (h : δ ⟶ ε) (x : sigmaFiber F γ B) :
    HEq (sigmaCellComponent F B (α ▷ h) x)
      ((sigmaMap F B h).map (sigmaCellComponent F B α x)) := by
  apply total_hom_hext (fiberRestriction F ε B)
    (sigmaMap_obj_comp F B f h x) (sigmaMap_obj_comp F B g h x)
  · change HEq ((F.map₂ (α ▷ h)).app x.base) ((F.map h).map ((F.map₂ α).app x.base))
    rw [action_whiskerRight]
    simp only [compBoundary, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl
  · apply HEq.trans (sigmaCellComponent_fiber_heq F B (α ▷ h) x)
    have hmap := mapped_cell_heq F B (comparisonTarget_comp F g h x.base)
      (cartesianComparisonCell_right_source_heq F α h x.base)
      (cartesianLift_comp_heq F g h x.base)
      (cartesianComparisonCell_right_heq F α h x.base) x.fiber
    apply HEq.trans hmap
    rw [action_whiskerRight]
    change HEq (eqToHom _ ≫ (B.map (cartesianLift F h ((F.map g).obj x.base))).map
      ((B.map₂ (cartesianComparisonCell F α x.base)).app x.fiber) ≫ eqToHom _) _
    apply HEq.trans (eqToHom_comp_heq _ _)
    apply HEq.trans (comp_eqToHom_heq _ _)
    apply HEq.trans _ (sigmaMap_map_fiber_heq F B h (sigmaCellComponent F B α x)).symm
    change HEq ((B.map (cartesianLift F h ((F.map g).obj x.base))).map
      ((B.map₂ (cartesianComparisonCell F α x.base)).app x.fiber))
      ((B.map (cartesianLift F h ((F.map g).obj x.base))).map
        (eqToHom _ ≫ (B.map₂ (cartesianComparisonCell F α x.base)).app x.fiber))
    rw [(B.map (cartesianLift F h ((F.map g).obj x.base))).map_comp, StrongMap.map_eqToHom]
    simp only [heq_eqToHom_comp_iff]
    rfl

theorem sigmaCell_whiskerRight {γ δ ε : Γ}
    {f g : γ ⟶ δ} (α : f ⟶ g) (h : δ ⟶ ε) :
    sigmaCell F B (α ▷ h) =
      eqToHom (sigmaMap_comp F B f h) ≫
        StrictTwoTransformation.Trans.whiskerRight (sigmaCell F B α) (sigmaMap F B h) ≫
          eqToHom (sigmaMap_comp F B g h).symm := by
  apply StrictTwoTransformation.Trans.ext
  intro x
  apply eq_of_heq
  repeat rw [StrictTwoTransformation.Trans.comp_app]
  repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact sigmaCellComponent_right_heq F B α h x

/-- The actual dependent pair family retains objects, arrows, and genuine cells. -/
def sigmaFamily : Family Γ :=
  StrictPseudofunctor.mk'' {
    obj := fun γ => ⟨sigmaFiber F γ B⟩
    map := sigmaMap F B
    map₂ := sigmaCell F B
    map₂_id := sigmaCell_id F B
    map₂_comp := sigmaCell_comp F B
    map_id := sigmaMap_id F B
    map_comp := sigmaMap_comp F B
    map₂_whisker_left := fun f _ _ α => sigmaCell_whiskerLeft F B f α
    map₂_whisker_right := fun α h => sigmaCell_whiskerRight F B α h
  }

end SquareKit.Internal.PathTransport.TwoFamily
