import SquareKit.Internal.PathTransport.TwoFamilyTransportObjects
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
theorem Section.normalMap_fiber_heq (s : Section F) {a b : Γ} (f : a ⟶ b) :
 HEq (s.normalMap F f).fiber (s.lift.map f).fiber :=
 total_hom_fiber_heq_family rfl (heq_of_eq (s.normalObj_eq F a))
  (heq_of_eq (s.normalObj_eq F b)) (s.normalMap_heq F f)
theorem Section.map_fiber_id (s : Section F) (a : Γ) :
 HEq (s.lift.map (𝟙 a)).fiber (𝟙 (s.normalObj F a).fiber) := by
 rw [← s.normalized_eq F]
 have h := congr_arg_heq (fun p => p.fiber) ((s.normalized F).lift.map_id a)
 exact h.trans (eqToHom_heq_id_cod _ _ (congrArg (fun H : StrictPseudofunctor (F.obj a) (F.obj a) => H.obj (s.normalObj F a).fiber) (F.map_id a)))
theorem Section.map_fiber_vertical (s : Section F) {a b c : Γ}
 (ha : a = c) (hb : b = c) (f : a ⟶ b) (hf : HEq f (𝟙 c)) :
 HEq (s.lift.map f).fiber (𝟙 (s.normalObj F c).fiber) := by
 cases ha
 cases hb
 cases eq_of_heq hf
 exact s.map_fiber_id F _
theorem Section.reindex_normalMap_vertical (s : Section F) (σ : StrictPseudofunctor Δ Γ)
 {a b : Δ} (f : a ⟶ b) (c : Γ) (ha : σ.obj a = c) (hb : σ.obj b = c)
 (hf : HEq (σ.map f) (𝟙 c)) :
 HEq ((s.reindex F σ).normalMap (TwoFamily.reindex σ F) f).fiber (𝟙 (s.normalObj F c).fiber) :=
 ((s.reindex F σ).normalMap_fiber_heq _ f).trans
  ((s.reindex_map_fiber F σ f).trans (s.map_fiber_vertical F ha hb _ hf))
variable {Ξ : Type*} [Bicategory Ξ] [Strict Ξ]
theorem Section.doubleReindex_normalMap_vertical (s : Section F)
 (σ : StrictPseudofunctor Δ Γ) (τ : StrictPseudofunctor Ξ Δ)
 {a b : Ξ} (f : a ⟶ b) (c : Γ) (ha : σ.obj (τ.obj a) = c) (hb : σ.obj (τ.obj b) = c)
 (hf : HEq (σ.map (τ.map f)) (𝟙 c)) :
 HEq (((s.reindex F σ).reindex (TwoFamily.reindex σ F) τ).normalMap
  (TwoFamily.reindex τ (TwoFamily.reindex σ F)) f).fiber (𝟙 (s.normalObj F c).fiber) :=
 (((s.reindex F σ).reindex (TwoFamily.reindex σ F) τ).normalMap_fiber_heq _ f).trans
  (((s.reindex F σ).reindex_map_fiber (TwoFamily.reindex σ F) τ f).trans
   ((s.reindex_map_fiber F σ (τ.map f)).trans (s.map_fiber_vertical F ha hb _ hf)))
end SquareKit.Internal.PathTransport.TwoFamily
