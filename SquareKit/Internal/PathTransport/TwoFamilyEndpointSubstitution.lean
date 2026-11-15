import SquareKit.Internal.PathTransport.TwoFamilyEndpointSections
import SquareKit.Internal.PathTransport.TwoFamilyComprehension
/-! Pairing preserves the full dependent section under substitution. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe up vp u v w uΓ vΓ wΓ
private theorem prod_hext' {A C : Type up} {B D : Type vp} (p : A × B) (q : C × D)
    (h1 : HEq p.1 q.1) (h2 : HEq p.2 q.2) : HEq p q := by
  cases type_eq_of_heq h1
  cases type_eq_of_heq h2
  exact heq_of_eq (Prod.ext (eq_of_heq h1) (eq_of_heq h2))
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (s t : Section F)
theorem endpointPair_obj_fiber_heq (γ : Γ) :
    HEq (((endpointPair F s t).lift.obj γ).fiber)
      (((s.lift.obj γ).fiber), ((t.lift.obj γ).fiber)) := by
  apply prod_hext'
  · exact congr_arg_heq (fun a : Section F => (a.lift.obj γ).fiber) (s.normalized_eq F)
  · exact congr_arg_heq (fun a : Section F => (a.lift.obj γ).fiber) (t.normalized_eq F)

theorem endpointPair_map_fiber_heq {x y : Γ} (p : x ⟶ y) :
    HEq (((endpointPair F s t).lift.map p).fiber)
      (((s.lift.map p).fiber), ((t.lift.map p).fiber)) := by
  apply prod_hext'
  · exact congr_arg_heq (fun a : Section F => (a.lift.map p).fiber) (s.normalized_eq F)
  · exact congr_arg_heq (fun a : Section F => (a.lift.map p).fiber) (t.normalized_eq F)

theorem endpointPair_cell_fiber_heq {x y : Γ} {p q : x ⟶ y} (α : p ⟶ q) :
    HEq (((endpointPair F s t).lift.map₂ α).fiber)
      (((s.lift.map₂ α).fiber), ((t.lift.map₂ α).fiber)) := by
  apply prod_hext'
  · exact congr_arg_heq (fun a : Section F => (a.lift.map₂ α).fiber) (s.normalized_eq F)
  · exact congr_arg_heq (fun a : Section F => (a.lift.map₂ α).fiber) (t.normalized_eq F)

variable {Δ : Type*} [Bicategory Δ] [Strict Δ]
theorem endpointPair_reindex_heq (σ : StrictPseudofunctor Δ Γ) :
    HEq (endpointPair (reindex σ F) (s.reindex F σ) (t.reindex F σ))
      ((endpointPair F s t).reindex (endpointFamily F) σ) := by
  apply Section.hext_family (endpointFamily_reindex σ F)
  · intro x
    apply HEq.trans (endpointPair_obj_fiber_heq (reindex σ F) (s.reindex F σ) (t.reindex F σ) x)
    apply HEq.trans (prod_hext' _ ((s.lift.obj (σ.obj x)).fiber, (t.lift.obj (σ.obj x)).fiber) (s.reindex_obj_fiber F σ x) (t.reindex_obj_fiber F σ x))
    exact (((endpointPair F s t).reindex_obj_fiber (endpointFamily F) σ x).trans
      (endpointPair_obj_fiber_heq F s t (σ.obj x))).symm
  · intro x y p
    apply HEq.trans (endpointPair_map_fiber_heq (reindex σ F) (s.reindex F σ) (t.reindex F σ) p)
    apply HEq.trans (prod_hext' _ ((s.lift.map (σ.map p)).fiber, (t.lift.map (σ.map p)).fiber) (s.reindex_map_fiber F σ p) (t.reindex_map_fiber F σ p))
    exact (((endpointPair F s t).reindex_map_fiber (endpointFamily F) σ p).trans
      (endpointPair_map_fiber_heq F s t (σ.map p))).symm
  · intro x y p q α
    apply HEq.trans (endpointPair_cell_fiber_heq (reindex σ F) (s.reindex F σ) (t.reindex F σ) α)
    apply HEq.trans (prod_hext' _ ((s.lift.map₂ (σ.map₂ α)).fiber, (t.lift.map₂ (σ.map₂ α)).fiber) (s.reindex_cell_fiber F σ α) (t.reindex_cell_fiber F σ α))
    exact (((endpointPair F s t).reindex_cell_fiber (endpointFamily F) σ α).trans
      (endpointPair_cell_fiber_heq F s t (σ.map₂ α))).symm

theorem endpointPair_reindex (σ : StrictPseudofunctor Δ Γ) :
    Section.cast (endpointFamily_reindex σ F)
      (endpointPair (reindex σ F) (s.reindex F σ) (t.reindex F σ)) =
        (endpointPair F s t).reindex (endpointFamily F) σ :=
  eq_of_heq ((Section.cast_heq _ _).trans (endpointPair_reindex_heq F s t σ))
end SquareKit.Internal.PathTransport.TwoFamily
