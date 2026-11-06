import SquareKit.Internal.PathTransport.TwoFamilyIdentityFiber
import SquareKit.Internal.PathTransport.TwoFamilySectionVerticalMap
/-! Identify a section action on a vertical identity-fiber arrow with the
ordinary functor obtained by restricting that same section. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
universe u
variable {Γ Δ : Type u} [Bicategory.{u,u} Γ] [Strict Γ]
 [Bicategory.{u,u} Δ] [Strict Δ]
variable (F : Family.{u,u,u,u,u,u} Γ)
theorem Section.reindex_normalMap_heq (s : Section F) (σ : StrictPseudofunctor Δ Γ)
 {a b : Δ} (f : a ⟶ b) {c d : Γ} (g : c ⟶ d)
 (ha : σ.obj a = c) (hb : σ.obj b = d) (hf : HEq (σ.map f) g) :
 HEq ((s.reindex F σ).normalMap (TwoFamily.reindex σ F) f).fiber (s.lift.map g).fiber := by
 cases ha; cases hb
 have e := eq_of_heq hf
 exact ((s.reindex F σ).normalMap_fiber_heq _ f).trans
  ((s.reindex_map_fiber F σ f).trans (by rw [e]))
theorem fiberInclusion_map_heq {γ : Γ} {a b : F.obj γ}
 {c d : Total F} (f : c ⟶ d) (h : a ⟶ b)
 (hc : c = (fiberInclusion F γ).obj a) (hd : d = (fiberInclusion F γ).obj b)
 (hb : HEq f.base (𝟙 γ)) (hf : HEq f.fiber h) :
 HEq f ((fiberInclusion F γ).map h) := by
 apply total_hom_hext F hc hd f _ hb
 exact hf.trans (eqToHom_comp_heq h
  (congrArg (fun H : F.obj γ ⟶ F.obj γ => H.obj a) (F.map_id γ))).symm
end SquareKit.Internal.PathTransport.TwoFamily
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Context.{u}} (A : Family Γ) (x y : TwoFamily.Section A.data) (γ : Γ)
local notation "I" => A.identity x y
theorem identityFiberFunctor_map_fiber
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 {a b : (x.normalObj A.data γ).fiber ⟶ (y.normalObj A.data γ).fiber} (h : a ⟶ b) :
 HEq (s.lift.map ((fiberInclusion (I).data γ).map (show (⟨a⟩ : LocallyDiscrete _) ⟶ ⟨b⟩ from ⟨h⟩))).fiber
 (Discrete.mk ((identityFiberFunctor A x y γ s).map h)) := by
 have hh := (TwoFamily.Section.cast_map_fiber (variableFamily_fiber I γ)
   (s.reindex _ (fiberInclusion (I).data γ)) (show (⟨a⟩ : LocallyDiscrete _) ⟶ ⟨b⟩ from ⟨h⟩)).trans
  (s.reindex_map_fiber _ (fiberInclusion (I).data γ) (show (⟨a⟩ : LocallyDiscrete _) ⟶ ⟨b⟩ from ⟨h⟩))
 exact hh.symm
theorem identityFiberFunctor_reindex_normalMap
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 {Δ : Context.{u}} (σ : StrictPseudofunctor Δ (I).total)
 {d e : Δ} (f : d ⟶ e)
 {a b : (x.normalObj A.data γ).fiber ⟶ (y.normalObj A.data γ).fiber} (h : a ⟶ b)
 (ha : σ.obj d = (fiberInclusion (I).data γ).obj ⟨a⟩)
 (hb : σ.obj e = (fiberInclusion (I).data γ).obj ⟨b⟩)
 (hf : HEq (σ.map f) ((fiberInclusion (I).data γ).map (show (⟨a⟩ : LocallyDiscrete _) ⟶ ⟨b⟩ from ⟨h⟩))) :
 HEq ((s.reindex _ σ).normalMap _ f).fiber
 (Discrete.mk ((identityFiberFunctor A x y γ s).map h)) :=
 (s.reindex_normalMap_heq _ σ f _ ha hb hf).trans (identityFiberFunctor_map_fiber A x y γ s h)
end SquareKit.Internal.PathTransport.HigherInterpretation
