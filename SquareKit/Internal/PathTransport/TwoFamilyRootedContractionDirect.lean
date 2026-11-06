import SquareKit.Internal.PathTransport.TwoFamilyRootedCompatibility
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)]
variable (x : Section F)
theorem rootedEndpoint_map_injective {a b : Total F} :
    Function.Injective ((rootedEndpoint F x).map (X := a) (Y := b)) :=
  inverseData_map_injective (rootedEndpoint F x) (endpointProjection F false).toPrelaxFunctorStruct
    (congrArg (fun K => K.toPrelaxFunctorStruct) (rootedEndpoint_second F x))
theorem rootedEndpoint_cell_injective {a b : Total F} {p q : a ⟶ b} :
    Function.Injective ((rootedEndpoint F x).map₂ (f := p) (g := q)) :=
  inverseData_cell_injective (rootedEndpoint F x) (endpointProjection F false).toPrelaxFunctorStruct
    (congrArg (fun K => K.toPrelaxFunctorStruct) (rootedEndpoint_second F x))
noncomputable def rootedContractionDirect : Pseudofunctor.StrongTrans
    (rootedDirectRetract F x).toPseudofunctor
    (StrictPseudofunctor.id (Total (rootedDirectFamily F x))).toPseudofunctor :=
  reindexStrongLift (openIdHigher F) (rootedEndpoint F x)
    (rootedBaseContraction F x) (rootedContractionMapped F x) (rootedContraction_compatibility F x)
    (fun {_ _ _ _} => rootedEndpoint_cell_injective F x)
theorem rootedContractionDirect_embedding :
    strongPostcomp (rootedContractionDirect F x) (rootedDirectEmbedding F x) = rootedContractionMapped F x :=
  reindexStrongLift_map _ _ _ _ _ _
end SquareKit.Internal.PathTransport.TwoFamily
