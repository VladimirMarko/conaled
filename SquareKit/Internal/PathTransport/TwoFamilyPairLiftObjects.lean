import SquareKit.Internal.PathTransport.TwoFamilyComprehension
import SquareKit.Internal.PathTransport.TwoFamilyTransportObjects
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Strict Δ]
theorem pairLift_obj_fiber (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
    (σ : StrictPseudofunctor Δ Γ) (s : Section (reindex σ F)) (δ : Δ) :
    HEq ((pairLift F σ s).obj δ).fiber (s.normalObj (reindex σ F) δ).fiber :=
  (s.normalObj_fiber_heq (reindex σ F) δ).symm
def PairLiftFiberFormula (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
    (E : Family.{uΔ,vΔ,wΔ,u,v,w} Δ)
    (k : Section E → StrictPseudofunctor Δ (Total F)) : Prop :=
  ∀ s δ, HEq ((k s).obj δ).fiber (s.normalObj E δ).fiber

theorem pairLift_cast_formula (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
    (σ : StrictPseudofunctor Δ Γ) (E : Family.{uΔ,vΔ,wΔ,u,v,w} Δ)
    (e : E = reindex σ F) :
    PairLiftFiberFormula F E (fun s => pairLift F σ (Section.cast e s)) := by
  cases e
  exact fun s δ => pairLift_obj_fiber F σ s δ
end SquareKit.Internal.PathTransport.TwoFamily
