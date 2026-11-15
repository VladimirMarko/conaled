import SquareKit.Internal.PathTransport.TwoFamilyFiniteDependentTail
namespace SquareKit.Internal.PathTransport.TwoFamily.FiniteDependentTail
open CategoryTheory Bicategory
universe u v w
structure Reindexed {Γ : StrictTwoCategory.{u,v,w}} {n Θ}
    (tail : FiniteDependentTail Γ n Θ) (Δ : StrictTwoCategory.{u,v,w}) where
  target : StrictTwoCategory.{u,v,w}
  tail : FiniteDependentTail Δ n target
  substitution : StrictPseudofunctor target Θ

variable {Γ Θ Δ : StrictTwoCategory.{u,v,w}}
noncomputable def reindexTail {n} (tail : FiniteDependentTail Γ n Θ) (σ : StrictPseudofunctor Δ Γ) :
    Reindexed tail Δ := by
  induction tail with
  | nil => exact ⟨Δ, .nil, σ⟩
  | @snoc n Θ tail E objects cells ih =>
    exact ⟨⟨Total (reindex ih.substitution E)⟩,
      ih.tail.snoc (reindex ih.substitution E)
        (fun x => objects (ih.substitution.obj x)) (fun x => cells (ih.substitution.obj x)),
      reindexHigher E ih.substitution⟩
end SquareKit.Internal.PathTransport.TwoFamily.FiniteDependentTail
