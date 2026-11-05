import SquareKit.Internal.PathTransport.TwoFamilyCoherence
import SquareKit.Internal.PathTransport.TwoFamilyReindex
/-! Higher projection and finite groupoid closure of context extension. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]
/-- The extension projection retains the full base action on 2-cells. -/
def projectionHigher (F : Family.{u,v,w,u',v',w'} Γ) : StrictPseudofunctor (Total F) Γ :=
  StrictPseudofunctor.mk'' {
    obj := fun x => x.base
    map := fun p => p.base
    map₂ := fun α => α.base
  }
/-- Invertible base and fiber 2-cells give invertible total 2-cells. -/
instance totalLocallyGroupoid (F : Family.{u,v,w,u',v',w'} Γ)
    [Bicategory.IsLocallyGroupoid Γ] [∀ x, Bicategory.IsLocallyGroupoid (F.obj x)] :
    Bicategory.IsLocallyGroupoid (Total F) := fun x y => homIsGroupoid F x y
instance reindexedFiberGroupoid {Δ : Type*} [Bicategory Δ] [Bicategory.Strict Δ]
    (σ : StrictPseudofunctor Δ Γ) (F : Family.{u,v,w,u',v',w'} Γ)
    [∀ γ, IsGroupoid (F.obj γ)] (δ : Δ) : IsGroupoid ((reindex σ F).obj δ) :=
  inferInstanceAs (IsGroupoid (F.obj (σ.obj δ)))

instance reindexedFiberLocallyGroupoid {Δ : Type*} [Bicategory Δ] [Bicategory.Strict Δ]
    (σ : StrictPseudofunctor Δ Γ) (F : Family.{u,v,w,u',v',w'} Γ)
    [∀ γ, Bicategory.IsLocallyGroupoid (F.obj γ)] (δ : Δ) :
    Bicategory.IsLocallyGroupoid ((reindex σ F).obj δ) :=
  inferInstanceAs (Bicategory.IsLocallyGroupoid (F.obj (σ.obj δ)))
end SquareKit.Internal.PathTransport.TwoFamily
