import SquareKit.Internal.PathTransport.TwoFamilyPathSubstitution
import SquareKit.Internal.PathTransport.TwoFamilyPathContractionStrong
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
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
private theorem pairWithComposite_heq {C : Type u} [Category.{v} C]
    {a a' b c : C} (ha : a = a') {p : a ⟶ b} {q : a' ⟶ b}
    (h : HEq p q) (r : b ⟶ c) : HEq (p, p ≫ r) (q, q ≫ r) := by
  cases ha
  cases eq_of_heq h
  rfl
/-- The canonical contraction endpoint is stable under context substitution. -/
theorem contractionEndpoint_reindex (x : PathContext (reindex σ F)) :
    (endpointReindex F σ).map (contractionEndpoint (reindex σ F) x) =
      contractionEndpoint F ((pathReindex F σ).obj x) := by
  apply Pseudofunctor.CoGrothendieck.ext
  · exact σ.map_id x.base.base
  · have h := congr_arg_heq (fun p => p.fiber)
      ((reindexHigher F σ).map_id ((pathFirst (reindex σ F)).obj x))
    exact pairWithComposite_heq
      (congrArg (fun H => H.obj x.base.fiber.1) (congrArg F.map (σ.map_id x.base.base)))
      h x.fiber.as
private theorem canonicalArrow_eq {C D : Type*} [Category C] [Bicategory D] [Strict D]
    (E : C ⥤ D) (b : D) {p q : C} (e : p = q) (h : E.obj p = b) (k : E.obj q = b) :
    TwoGroupoidHom.arrow E b p (eqToHom h) = TwoGroupoidHom.arrow E b q (eqToHom k) := by
  cases e
  rfl
/-- Substitution retains the actual component of the path contraction. -/
theorem contractionComponent_reindex (x : PathContext (reindex σ F)) :
    (pathReindex F σ).map (contractionComponent (reindex σ F) x) =
      contractionComponent F ((pathReindex F σ).obj x) := by
  exact canonicalArrow_eq (evaluation (openIdHigher F)
    (pathReflexivityObj F ((pathFirst F).obj ((pathReindex F σ).obj x))).fiber)
    ((pathReindex F σ).obj x).fiber (contractionEndpoint_reindex F σ x)
      (congrArg LocallyDiscrete.mk (contractionBoundary (reindex σ F) x))
      (congrArg LocallyDiscrete.mk (contractionBoundary F ((pathReindex F σ).obj x)))
end SquareKit.Internal.PathTransport.TwoFamily
