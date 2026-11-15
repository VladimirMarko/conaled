import SquareKit.Internal.PathTransport.TwoFamilyPathContractionReindex
import SquareKit.Internal.PathTransport.TwoFamilyPathJSubstitution
import SquareKit.Internal.PathTransport.TwoStrongCongr
import SquareKit.Internal.PathTransport.TwoFamilySectionHEq
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ uE vE wE
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Bicategory.Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (σ : StrictPseudofunctor Δ Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
variable (E : Family.{_,_,_,uE,vE,wE} (PathContext F))
/-- The contraction's source motive commutes with substitution. -/
theorem pathJSource_reindex :
    reindex (contractionRetract (reindex σ F)) (reindex (pathReindex F σ) E) =
      reindex (pathReindex F σ) (reindex (contractionRetract F) E) :=
  (reindex_comp E (pathReindex F σ) (contractionRetract (reindex σ F))).trans
    ((congrArg (fun H => reindex H E) (pathReindex_retract F σ)).trans
      (reindex_comp E (contractionRetract F) (pathReindex F σ)).symm)
/-- The contraction's target motive commutes with substitution. -/
theorem pathJTarget_reindex :
    reindex (StrictPseudofunctor.id (PathContext (reindex σ F))) (reindex (pathReindex F σ) E) =
      reindex (pathReindex F σ) (reindex (StrictPseudofunctor.id (PathContext F)) E) :=
  (reindex_id (reindex (pathReindex F σ) E)).trans
    (congrArg (fun G => reindex (pathReindex F σ) G) (reindex_id E)).symm
variable [IsLocallyGroupoid Γ] [IsLocallyGroupoid Δ]
/-- The actual coherent contraction action on any motive is stable under substitution. -/
theorem pathJMotive_reindex :
    HEq (strongPostcomp (pathContraction (reindex σ F)) (reindex (pathReindex F σ) E))
      (strongPrecomp (strongPostcomp (pathContraction F) E) (pathReindex F σ)) := by
  have h1 := (strongPostcomp_comp (pathContraction (reindex σ F)) (pathReindex F σ) E).symm
  have h2 := strongPostcomp_heq (pathReindex_retract F σ)
    ((strictFunctor_id_comp (pathReindex F σ)).trans (strictFunctor_comp_id (pathReindex F σ)).symm)
    (strongPostcomp (pathContraction (reindex σ F)) (pathReindex F σ))
    (strongPrecomp (pathContraction F) (pathReindex F σ)) (pathContraction_reindex F σ) E
  have h3 := strongPostcomp_precomp (pathContraction F) (pathReindex F σ) E
  exact h1.trans (h2.trans h3)
end SquareKit.Internal.PathTransport.TwoFamily
