import SquareKit.Internal.PathTransport.TwoFamilyPathRetraction
import SquareKit.Internal.PathTransport.TwoFamilySectionLaws
import SquareKit.Internal.PathTransport.TwoFamilyReindexData
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Bicategory.Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (σ : StrictPseudofunctor Δ Γ)
/-- Explicit endpoint substitution data, before law transport. -/
def endpointReindexData : PrelaxFunctorStruct
    (Total (endpointFamily (reindex σ F))) (Total (endpointFamily F)) where
  obj x := ⟨σ.obj x.base, x.fiber⟩
  map p := ⟨σ.map p.base, p.fiber⟩
  map₂ α := ⟨σ.map₂ α.base, α.fiber⟩
/-- Endpoint substitution retains both components and derives its laws from reindexing. -/
def endpointReindex :
    StrictPseudofunctor (Total (endpointFamily (reindex σ F))) (Total (endpointFamily F)) :=
  reindexOfData (endpointFamily F) σ (endpointFamily_reindex σ F) (endpointReindexData F σ)
    (fun _ => rfl) (fun _ => HEq.rfl) (fun _ => HEq.rfl)
    (fun _ => HEq.rfl) (fun _ => HEq.rfl) (fun _ => HEq.rfl)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
/-- Open identity is stable under the constructed endpoint substitution in every dimension. -/
theorem openIdHigher_reindex : openIdHigher (reindex σ F) =
    reindex (endpointReindex F σ) (openIdHigher F) := by
  apply StrictTwoTransformation.functor_ext
  rfl
/-- Path-context substitution data retains the endpoint action and the chosen path. -/
noncomputable def pathReindexData :
    PrelaxFunctorStruct (PathContext (reindex σ F)) (PathContext F) where
  obj x := ⟨(endpointReindex F σ).obj x.base, x.fiber⟩
  map p := ⟨(endpointReindex F σ).map p.base, p.fiber⟩
  map₂ α := ⟨(endpointReindex F σ).map₂ α.base, α.fiber⟩

/-- The whole higher path context reindexes with no additional caller coherence laws. -/
noncomputable def pathReindex :
    StrictPseudofunctor (PathContext (reindex σ F)) (PathContext F) :=
  reindexOfData (openIdHigher F) (endpointReindex F σ) (openIdHigher_reindex F σ)
    (pathReindexData F σ) (fun _ => rfl) (fun _ => HEq.rfl) (fun _ => HEq.rfl)
    (fun _ => HEq.rfl) (fun _ => HEq.rfl) (fun _ => HEq.rfl)

/-- The path substitution preserves the actual endpoint projection. -/
theorem pathReindex_endpoints :
    (pathReindex F σ).comp (pathEndpoints F) =
      (pathEndpoints (reindex σ F)).comp (endpointReindex F σ) :=
  StrictTwoTransformation.functor_ext rfl

end SquareKit.Internal.PathTransport.TwoFamily
