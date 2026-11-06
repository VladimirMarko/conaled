import SquareKit.Internal.PathTransport.TwoFamilyPairLiftReindex
import SquareKit.Internal.PathTransport.TwoFamilySubstitution
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
universe u v w uD vD wD uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable {Δ : Type uD} [Bicategory.{wD,vD} Δ] [Strict Δ]
variable (E : Family.{u,v,w,uE,vE,wE} Γ)
theorem pairLift_familySubstitution {F : Family.{uD,vD,wD,uE,vE,wE} Δ}
    (σ : StrictPseudofunctor Δ Γ) (e : F = reindex σ E)
    (h : reindex (projectionHigher F) F = reindex ((projectionHigher F).comp σ) E) :
    pairLift E ((projectionHigher F).comp σ) (Section.cast h (variableSection F)) =
      familySubstitution E σ e := by
  cases e
  exact (pairLift_reindex E σ).trans (familySubstitution_reindex E σ).symm
end SquareKit.Internal.PathTransport.TwoFamily
