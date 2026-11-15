import SquareKit.Internal.PathTransport.TwoFamilySigmaReindexData
import SquareKit.Internal.PathTransport.TwoFamilyHEq

/-! Exact substitution stability of the constructed dependent pair family, including
its action on arbitrary genuine cells. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (σ : StrictPseudofunctor Δ Γ)

private theorem strict_map_heq {C D : Type*} [Bicategory C] [Bicategory D]
    (H : StrictPseudofunctor C D) {x x' y y' : C} (hx : x = x') (hy : y = y')
    {p : x ⟶ y} {q : x' ⟶ y'} (hp : HEq p q) : HEq (H.map p) (H.map q) := by
  cases hx
  cases hy
  cases eq_of_heq hp
  rfl

variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))

theorem sigmaMap_reindex_obj {γ δ : Δ} (f : γ ⟶ δ)
    (x : sigmaFiber (reindex σ F) γ (reindex (reindexHigher F σ) B))
    (x' : sigmaFiber F (σ.obj γ) B) (hx : HEq x x') :
    HEq ((sigmaMap (reindex σ F) (reindex (reindexHigher F σ) B) f).obj x)
      ((sigmaMap F B (σ.map f)).obj x') := by
  rcases x with ⟨a,b⟩
  rcases x' with ⟨a',b'⟩
  have hb := total_obj_base_heq_family (fiberRestriction_reindex F σ B γ) hx
  have hf := total_obj_fiber_heq_family (fiberRestriction_reindex F σ B γ) hx
  change a = a' at hb
  cases hb
  change HEq b b' at hf
  cases eq_of_heq hf
  apply total_obj_hext_family (fiberRestriction_reindex F σ B δ)
  · rfl
  · rfl

theorem sigmaMap_reindex_map {γ δ : Δ} (f : γ ⟶ δ)
    {x y : sigmaFiber (reindex σ F) γ (reindex (reindexHigher F σ) B)}
    {x' y' : sigmaFiber F (σ.obj γ) B} (hx : HEq x x') (hy : HEq y y')
    {p : x ⟶ y} {q : x' ⟶ y'} (hp : HEq p q) :
    HEq ((sigmaMap (reindex σ F) (reindex (reindexHigher F σ) B) f).map p)
      ((sigmaMap F B (σ.map f)).map q) := by
  have ex := total_obj_base_heq_family (fiberRestriction_reindex F σ B γ) hx
  have ey := total_obj_base_heq_family (fiberRestriction_reindex F σ B γ) hy
  have hxf := total_obj_fiber_heq_family (fiberRestriction_reindex F σ B γ) hx
  have hyf := total_obj_fiber_heq_family (fiberRestriction_reindex F σ B γ) hy
  have hpb := total_hom_base_heq_family (fiberRestriction_reindex F σ B γ) hx hy hp
  have hpf := total_hom_fiber_heq_family (fiberRestriction_reindex F σ B γ) hx hy hp
  apply total_hom_hext_family (fiberRestriction_reindex F σ B δ)
    (sigmaMap_reindex_obj F σ B f x x' hx) (sigmaMap_reindex_obj F σ B f y y' hy)
  · exact strict_map_heq (F.map (σ.map f)) ex ey hpb
  · apply HEq.trans (sigmaMap_map_fiber_heq (reindex σ F) (reindex (reindexHigher F σ) B) f p)
    apply HEq.trans _ (sigmaMap_map_fiber_heq F B (σ.map f) q).symm
    have es := family_obj_action_heq (fiberRestriction_reindex F σ B γ) ex ey hpb hxf
    change HEq ((B.map ((reindexHigher F σ).map (cartesianLift (reindex σ F) f y.base))).map p.fiber)
      ((B.map (cartesianLift F (σ.map f) y'.base)).map q.fiber)
    rw [cartesianLift_reindex]
    have eob : (show Total F from ⟨σ.obj γ,y.base⟩) = ⟨σ.obj γ,y'.base⟩ := congrArg (fun a => (⟨σ.obj γ,a⟩ : Total F)) ey
    have eot : (show Total F from ⟨σ.obj δ,(F.map (σ.map f)).obj y.base⟩) =
        ⟨σ.obj δ,(F.map (σ.map f)).obj y'.base⟩ := congrArg (fun a => (⟨σ.obj δ,(F.map (σ.map f)).obj a⟩ : Total F)) ey
    have el : HEq (cartesianLift F (σ.map f) y.base) (cartesianLift F (σ.map f) y'.base) :=
      congr_arg_heq (cartesianLift F (σ.map f)) ey
    exact family_arrow_action_heq (F := B) rfl eob eot el es hyf hpf

theorem sigmaMap_reindex_cell {γ δ : Δ} (f : γ ⟶ δ)
    {x y : sigmaFiber (reindex σ F) γ (reindex (reindexHigher F σ) B)}
    {x' y' : sigmaFiber F (σ.obj γ) B} (hx : HEq x x') (hy : HEq y y')
    {p q : x ⟶ y} {p' q' : x' ⟶ y'} (hp : HEq p p') (hq : HEq q q')
    {α : p ⟶ q} {β : p' ⟶ q'} (hα : HEq α β) :
    HEq ((sigmaMap (reindex σ F) (reindex (reindexHigher F σ) B) f).map₂ α)
      ((sigmaMap F B (σ.map f)).map₂ β) := by
  have ex := total_obj_base_heq_family (fiberRestriction_reindex F σ B γ) hx
  have ey := total_obj_base_heq_family (fiberRestriction_reindex F σ B γ) hy
  have hxf := total_obj_fiber_heq_family (fiberRestriction_reindex F σ B γ) hx
  have hyf := total_obj_fiber_heq_family (fiberRestriction_reindex F σ B γ) hy
  have hpb := total_hom_base_heq_family (fiberRestriction_reindex F σ B γ) hx hy hp
  have hqb := total_hom_base_heq_family (fiberRestriction_reindex F σ B γ) hx hy hq
  have hpf := total_hom_fiber_heq_family (fiberRestriction_reindex F σ B γ) hx hy hp
  have hab := total_cell_base_heq_family (fiberRestriction_reindex F σ B γ) hx hy hp hq hα
  have haf := total_cell_fiber_heq_family (fiberRestriction_reindex F σ B γ) hx hy hp hq hα
  apply total_cell_hext_family (fiberRestriction_reindex F σ B δ)
    (sigmaMap_reindex_obj F σ B f x x' hx) (sigmaMap_reindex_obj F σ B f y y' hy)
    (sigmaMap_reindex_map F σ B f hx hy hp) (sigmaMap_reindex_map F σ B f hx hy hq)
  · exact family_cell_action_heq (F := F) rfl rfl rfl HEq.rfl
      (heq_of_eq ex) (heq_of_eq ey) hpb hqb hab
  · apply HEq.trans (sigmaMap_cell_fiber_heq (reindex σ F) (reindex (reindexHigher F σ) B) f α)
    apply HEq.trans _ (sigmaMap_cell_fiber_heq F B (σ.map f) β).symm
    have es := family_obj_action_heq (fiberRestriction_reindex F σ B γ) ex ey hpb hxf
    have eb := total_cell_boundary_heq_family (fiberRestriction_reindex F σ B γ) hx hy hp hq hα
    change HEq ((B.map ((reindexHigher F σ).map (cartesianLift (reindex σ F) f y.base))).map₂ α.fiber)
      ((B.map (cartesianLift F (σ.map f) y'.base)).map₂ β.fiber)
    rw [cartesianLift_reindex]
    exact family_cell_action_heq (F := B) rfl
      (congrArg (fun a => (⟨σ.obj γ,a⟩ : Total F)) ey)
      (congrArg (fun a => (⟨σ.obj δ,(F.map (σ.map f)).obj a⟩ : Total F)) ey)
      (congr_arg_heq (cartesianLift F (σ.map f)) ey) es hyf hpf eb haf

theorem sigmaMap_reindex {γ δ : Δ} (f : γ ⟶ δ) :
    HEq (sigmaMap (reindex σ F) (reindex (reindexHigher F σ) B) f)
      (sigmaMap F B (σ.map f)) := by
  apply total_functor_hext_family (fiberRestriction_reindex F σ B γ)
    (fiberRestriction_reindex F σ B δ)
  · exact sigmaMap_reindex_obj F σ B f
  · intro x y x' y' hx hy p q hp
    exact sigmaMap_reindex_map F σ B f hx hy hp
  · intro x y x' y' hx hy p q p' q' hp hq α β hα
    exact sigmaMap_reindex_cell F σ B f hx hy hp hq hα

theorem sigmaCellComponent_reindex {γ δ : Δ} {f g : γ ⟶ δ} (α : f ⟶ g)
    (x : sigmaFiber (reindex σ F) γ (reindex (reindexHigher F σ) B))
    (x' : sigmaFiber F (σ.obj γ) B) (hx : HEq x x') :
    HEq (sigmaCellComponent (reindex σ F) (reindex (reindexHigher F σ) B) α x)
      (sigmaCellComponent F B (σ.map₂ α) x') := by
  apply total_hom_hext_family (fiberRestriction_reindex F σ B δ)
    (sigmaMap_reindex_obj F σ B f x x' hx) (sigmaMap_reindex_obj F σ B g x x' hx)
  · have hb := total_obj_base_heq_family (fiberRestriction_reindex F σ B γ) hx
    exact congr_arg_heq (F.map₂ (σ.map₂ α)).app hb
  · apply HEq.trans (sigmaCellComponent_fiber_heq (reindex σ F)
      (reindex (reindexHigher F σ) B) α x)
    apply HEq.trans _ (sigmaCellComponent_fiber_heq F B (σ.map₂ α) x').symm
    rcases x with ⟨a,b⟩
    rcases x' with ⟨a',b'⟩
    have hb := total_obj_base_heq_family (fiberRestriction_reindex F σ B γ) hx
    have hf := total_obj_fiber_heq_family (fiberRestriction_reindex F σ B γ) hx
    change a = a' at hb
    cases hb
    change HEq b b' at hf
    cases eq_of_heq hf
    change HEq ((B.map₂ ((reindexHigher F σ).map₂
      (cartesianComparisonCell (reindex σ F) α a))).app b)
      ((B.map₂ (cartesianComparisonCell F (σ.map₂ α) a)).app b)
    rw [cartesianComparisonCell_reindex, B.map₂_comp, B.map₂_eqToHom,
      StrictTwoTransformation.Trans.comp_app, StrictTwoTransformation.Trans.eqToHom_app]
    exact eqToHom_comp_heq _ _

theorem sigmaCell_reindex {γ δ : Δ} {f g : γ ⟶ δ} (α : f ⟶ g) :
    HEq (sigmaCell (reindex σ F) (reindex (reindexHigher F σ) B) α)
      (sigmaCell F B (σ.map₂ α)) := by
  apply total_trans_hext_family (fiberRestriction_reindex F σ B γ)
    (fiberRestriction_reindex F σ B δ) (sigmaMap_reindex F σ B f) (sigmaMap_reindex F σ B g)
  exact sigmaCellComponent_reindex F σ B α

theorem sigmaFamily_reindex :
    sigmaFamily (reindex σ F) (reindex (reindexHigher F σ) B) =
      reindex σ (sigmaFamily F B) := by
  apply strictFunctorData_ext
  apply prelaxData_ext
  · intro γ
    exact congrArg (fun H : Family (F.obj (σ.obj γ)) => (⟨Total H⟩ : StrictTwoCategory))
      (fiberRestriction_reindex F σ B γ)
  · exact fun f => sigmaMap_reindex F σ B f
  · exact fun α => sigmaCell_reindex F σ B α

end SquareKit.Internal.PathTransport.TwoFamily
