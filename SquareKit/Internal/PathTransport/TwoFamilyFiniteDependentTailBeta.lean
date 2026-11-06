import SquareKit.Internal.PathTransport.TwoFamilyFiniteDependentTail
import SquareKit.Internal.PathTransport.TwoFamilyContractionHomotopyNormalization
namespace SquareKit.Internal.PathTransport.TwoFamily.FiniteDependentTail
open CategoryTheory Bicategory
universe u v w uM vM wM
variable {Γ Δ : StrictTwoCategory.{u,v,w}} [IsLocallyGroupoid Γ] [IsGroupoid Γ]
def ContractionPresentation.Normalized {C : StrictTwoCategory.{u,v,w}}
    (c : ContractionPresentation C) : Prop :=
  c.inclusion.comp c.retraction = StrictPseudofunctor.id c.source ∧
    HEq (strongPrecomp c.homotopy c.inclusion)
      (Pseudofunctor.StrongTrans.id c.inclusion.toPseudofunctor)

theorem liftSplit_normalized {n} (tail : FiniteDependentTail Γ n Δ)
    (c : ContractionPresentation Γ) (hc : c.Normalized) : (tail.liftSplit c).Normalized := by
  induction tail with
  | nil => exact hc
  | @snoc n Δ tail E objects cells ih =>
    letI : IsLocallyGroupoid Δ := tail.locallyGroupoid
    letI : IsGroupoid Δ := tail.groupoid
    letI : ∀x, IsGroupoid (E.obj x) := objects
    letI : ∀x, IsLocallyGroupoid (E.obj x) := cells
    let d := tail.liftSplit c
    letI : IsGroupoid d.source := d.sourceObjects
    letI : IsLocallyGroupoid d.source := d.sourceCells
    letI : ∀x, IsIso (d.homotopy.app x) := fun x => IsGroupoid.all_isIso _
    exact ⟨contractionRetraction_reflexive d.inclusion d.retraction d.homotopy ih.1 ih.2 E,
      contractionRetractionHomotopy_reflexive E d.inclusion d.retraction d.homotopy ih.1 ih.2⟩

/-- Every finite dependent extension preserves whole-section reflexive computation. -/
theorem eliminate_beta {n} (tail : FiniteDependentTail Γ n Δ)
    (c : ContractionPresentation Γ) (hc : c.Normalized)
    (E : Family.{u,v,w,uM,vM,wM} Δ)
    (d : Section (reindex (tail.liftSplit c).inclusion E)) :
    (tail.eliminate c E d).reindex E (tail.liftSplit c).inclusion = d :=
  retractionJ_beta _ _ _ (liftSplit_normalized tail c hc).1 (liftSplit_normalized tail c hc).2 E d
end SquareKit.Internal.PathTransport.TwoFamily.FiniteDependentTail
