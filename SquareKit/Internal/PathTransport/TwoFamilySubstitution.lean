import SquareKit.Internal.PathTransport.TwoFamilyContractionNormalization
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
universe u v w uD vD wD uT vT wT uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable {Δ : Type uD} [Bicategory.{wD,vD} Δ] [Strict Δ]
variable {Θ : Type uT} [Bicategory.{wT,vT} Θ] [Strict Θ]
variable (E : Family.{u,v,w,uE,vE,wE} Γ)
variable {F : Family.{uD,vD,wD,uE,vE,wE} Δ} {G : Family.{uT,vT,wT,uE,vE,wE} Θ}
/-- The whole context substitution induced by a proved pullback-family equality. -/
def familySubstitution (σ : StrictPseudofunctor Δ Γ) (e : F = reindex σ E) :
    StrictPseudofunctor (Total F) (Total E) := (familyCast e).comp (reindexHigher E σ)

theorem familyCast_refl {F : Family.{u,v,w,uE,vE,wE} Γ} :
    familyCast (rfl : F = F) = StrictPseudofunctor.id (Total F) := rfl

theorem familySubstitution_reindex (σ : StrictPseudofunctor Δ Γ) :
    familySubstitution E σ rfl = reindexHigher E σ :=
  StrictTwoTransformation.functor_id_comp _

theorem familySubstitution_congr {σ τ : StrictPseudofunctor Δ Γ} (h : σ = τ)
    (e : F = reindex σ E) (e' : F = reindex τ E) :
    familySubstitution E σ e = familySubstitution E τ e' := by cases h; rfl

theorem familySubstitution_comp (σ : StrictPseudofunctor Δ Γ) (τ : StrictPseudofunctor Θ Δ)
    (e : F = reindex σ E) (e' : G = reindex τ F) :
    (familySubstitution F τ e').comp (familySubstitution E σ e) =
      familySubstitution E (τ.comp σ)
        (e'.trans ((congrArg (reindex τ) e).trans (reindex_comp E σ τ))) := by
  cases e
  cases e'
  simp only [familySubstitution_reindex]
  exact (familyCast_precomp_eq_of_heq (reindex_comp E σ τ)
    ((reindexHigher (reindex σ E) τ).comp (reindexHigher E σ))
    (reindexHigher E (τ.comp σ)) (reindexHigher_comp_heq E σ τ)).symm
end SquareKit.Internal.PathTransport.TwoFamily
