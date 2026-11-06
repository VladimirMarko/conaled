import SquareKit.Internal.PathTransport.TwoFamilyRootedContractionEmbedding
import SquareKit.Internal.PathTransport.TwoFamilySubstitutionFaithful
import SquareKit.Internal.PathTransport.TwoStrongFaithful
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
private theorem strongId_heq {A B : Type*} [Bicategory A] [Bicategory B]
    {H K : StrictPseudofunctor A B} (e : H = K) :
    HEq (Pseudofunctor.StrongTrans.id H.toPseudofunctor) (Pseudofunctor.StrongTrans.id K.toPseudofunctor) := by cases e; rfl

theorem rootedContraction_embedding_source :
    ((rootedRetraction F x).comp (rootedReflexivity F x)).comp (rootedPathEmbedding F x) =
      (rootedPathEmbedding F x).comp (contractionRetract F) := by
  change _ = (rootedPathEmbedding F x).comp ((pathFirst F).comp (pathReflexivity F))
  rw [strictFunctor_comp_assoc, rootedReflexivity_embedding, ← strictFunctor_comp_assoc,
    ← strictFunctor_comp_assoc, rootedPathEmbedding_first]
  rfl
theorem rootedContraction_embedding_target :
    (StrictPseudofunctor.id _).comp (rootedPathEmbedding F x) =
      (rootedPathEmbedding F x).comp (StrictPseudofunctor.id _) := by
  rw [strictFunctor_id_comp, strictFunctor_comp_id]

theorem rootedContraction_reflexive_mapped :
    HEq (strongPostcomp (strongPrecomp (rootedContraction F x) (rootedReflexivity F x))
      (rootedPathEmbedding F x))
      (strongPostcomp (Pseudofunctor.StrongTrans.id (rootedReflexivity F x).toPseudofunctor)
        (rootedPathEmbedding F x)) := by
  have h1 := strongPostcomp_precomp (rootedContraction F x) (rootedReflexivity F x) (rootedPathEmbedding F x)
  have h2 := strongPrecomp_heq (rootedContraction_embedding_source F x)
    (rootedContraction_embedding_target F x) _ _ (rootedContraction_embedding F x) (rootedReflexivity F x)
  have h3 := strongPrecomp_comp (pathContraction F) (rootedPathEmbedding F x) (rootedReflexivity F x)
  have h4 := strongPrecomp_functor_heq (pathContraction F) (rootedReflexivity_embedding F x)
  have h5 := (strongPrecomp_comp (pathContraction F) (pathReflexivity F) x.lift).symm
  have h6 := strongPrecomp_heq
    (contraction_reflexive_source (pathReflexivity F) (pathFirst F) (pathReflexivity_first F))
    (StrictTwoTransformation.functor_comp_id (pathReflexivity F))
    _ _ (pathContraction_reflexive F) x.lift
  have h7 := heq_of_eq (strongPrecomp_id (pathReflexivity F) x.lift)
  have h8 := strongId_heq (rootedReflexivity_embedding F x).symm
  have h9 := (heq_of_eq (strongPostcomp_id (rootedReflexivity F x) (rootedPathEmbedding F x))).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans (h8.trans h9)))))))

theorem rootedPathEmbedding_map_injective {a b : Total (rootedPathFamily F x)} :
    Function.Injective ((rootedPathEmbedding F x).map (X := a) (Y := b)) := by
  rw [← rootedPathEmbedding_direct]
  exact familySubstitution_map_injective (openIdHigher F) (rootedEndpoint F x)
    (rootedPathFamily_direct F x) (fun {_ _} => rootedEndpoint_map_injective F x)
theorem rootedPathEmbedding_cell_injective {a b : Total (rootedPathFamily F x)} {p q : a ⟶ b} :
    Function.Injective ((rootedPathEmbedding F x).map₂ (f := p) (g := q)) := by
  rw [← rootedPathEmbedding_direct]
  exact familySubstitution_cell_injective (openIdHigher F) (rootedEndpoint F x)
    (rootedPathFamily_direct F x) (fun {_ _ _ _} => rootedEndpoint_cell_injective F x)

theorem rootedContraction_reflexive :
    HEq (strongPrecomp (rootedContraction F x) (rootedReflexivity F x))
      (Pseudofunctor.StrongTrans.id (rootedReflexivity F x).toPseudofunctor) :=
  strongPostcomp_heq_reflect (rootedPathEmbedding F x)
    (fun {_ _} => rootedPathEmbedding_map_injective F x)
    (fun {_ _ _ _} => rootedPathEmbedding_cell_injective F x)
    (contraction_reflexive_source (rootedReflexivity F x) (rootedRetraction F x) (rootedReflexivity_retraction F x))
    (StrictTwoTransformation.functor_comp_id _) _ _ (rootedContraction_reflexive_mapped F x)
end SquareKit.Internal.PathTransport.TwoFamily
