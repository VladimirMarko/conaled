import SquareKit.Internal.PathTransport.TwoFamilyContractionRetraction
import SquareKit.Internal.PathTransport.TwoFamilyRetractionJ
import SquareKit.Internal.PathTransport.TwoFamilyContractionLift
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
universe u v w
inductive FiniteDependentTail (Γ : StrictTwoCategory.{u,v,w}) :
    Nat → StrictTwoCategory.{u,v,w} → Type (max (u+1) (v+1) (w+1)) where
  | nil : FiniteDependentTail Γ 0 Γ
  | snoc {n Δ} (tail : FiniteDependentTail Γ n Δ)
      (E : Family.{u,v,w,u,v,w} Δ)
      (objects : ∀x, IsGroupoid (E.obj x))
      (cells : ∀x, IsLocallyGroupoid (E.obj x)) :
      FiniteDependentTail Γ (n+1) ⟨Total E⟩

namespace FiniteDependentTail
variable {Γ Δ : StrictTwoCategory.{u,v,w}} [IsLocallyGroupoid Γ]
theorem locallyGroupoid {n} (tail : FiniteDependentTail Γ n Δ) : IsLocallyGroupoid Δ := by
  induction tail with
  | nil => infer_instance
  | @snoc n Δ tail E objects cells ih =>
    letI : IsLocallyGroupoid Δ := ih
    letI : ∀x, IsLocallyGroupoid (E.obj x) := cells
    exact inferInstanceAs (IsLocallyGroupoid (Total E))

theorem groupoid [IsGroupoid Γ] {n} (tail : FiniteDependentTail Γ n Δ) : IsGroupoid Δ := by
  induction tail with
  | nil => infer_instance
  | @snoc n Δ tail E objects cells ih =>
    letI : IsGroupoid Δ := ih
    letI : ∀x, IsGroupoid (E.obj x) := objects
    exact inferInstanceAs (IsGroupoid (Total E))


/-- Chosen branch domain and coherent contraction; reflexive normalization is a separate property. -/
structure ContractionPresentation (C : StrictTwoCategory.{u,v,w}) where
  source : StrictTwoCategory.{u,v,w}
  sourceObjects : IsGroupoid source
  sourceCells : IsLocallyGroupoid source
  inclusion : StrictPseudofunctor source C
  retraction : StrictPseudofunctor C source
  homotopy : Pseudofunctor.StrongTrans (retraction.comp inclusion).toPseudofunctor
    (StrictPseudofunctor.id C).toPseudofunctor

noncomputable def liftSplit [IsGroupoid Γ] {n} (tail : FiniteDependentTail Γ n Δ)
    (c : ContractionPresentation Γ) : ContractionPresentation Δ := by
  induction tail with
  | nil => exact c
  | @snoc n Δ tail E objects cells ih =>
    letI : IsLocallyGroupoid Δ := tail.locallyGroupoid
    letI : IsGroupoid Δ := tail.groupoid
    letI : ∀x, IsGroupoid (E.obj x) := objects
    letI : ∀x, IsLocallyGroupoid (E.obj x) := cells
    letI : ∀x, IsIso (ih.homotopy.app x) := fun x => IsGroupoid.all_isIso _
    letI : IsGroupoid ih.source := ih.sourceObjects
    letI : IsLocallyGroupoid ih.source := ih.sourceCells
    letI : ∀x, IsGroupoid ((reindex ih.inclusion E).obj x) :=
      fun x => objects (ih.inclusion.obj x)
    letI : ∀x, IsLocallyGroupoid ((reindex ih.inclusion E).obj x) :=
      fun x => cells (ih.inclusion.obj x)
    exact {
      source := ⟨Total (reindex ih.inclusion E)⟩
      sourceObjects := inferInstance
      sourceCells := inferInstance
      inclusion := reindexHigher E ih.inclusion
      retraction := contractionRetraction ih.inclusion ih.retraction ih.homotopy E
      homotopy := contractionRetractionHomotopy ih.inclusion ih.retraction ih.homotopy E }

universe uM vM wM
/-- Eliminate into any higher motive after an arbitrary finite dependent tail. -/
noncomputable def eliminate [IsGroupoid Γ] {n} (tail : FiniteDependentTail Γ n Δ)
    (c : ContractionPresentation Γ) (E : Family.{u,v,w,uM,vM,wM} Δ)
    (d : Section (reindex (tail.liftSplit c).inclusion E)) : Section E :=
  retractionJ (tail.liftSplit c).inclusion (tail.liftSplit c).retraction
    (tail.liftSplit c).homotopy E d

end FiniteDependentTail
end SquareKit.Internal.PathTransport.TwoFamily
