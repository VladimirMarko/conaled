import SquareKit.Internal.PathTransport.TwoFamilyFiniteDependentTailReindex
import SquareKit.Internal.PathTransport.TwoFamilyContractionHomotopySubstitution
namespace SquareKit.Internal.PathTransport.TwoFamily.FiniteDependentTail
open CategoryTheory Bicategory
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {Γ Δ : StrictTwoCategory.{u,v,w}}
structure ContractionMap (c : ContractionPresentation Γ) (d : ContractionPresentation Δ)
    (σ : StrictPseudofunctor Δ Γ) where
  branch : StrictPseudofunctor d.source c.source
structure ContractionMap.Lawful {c : ContractionPresentation Γ} {d : ContractionPresentation Δ}
    {σ : StrictPseudofunctor Δ Γ} (m : ContractionMap c d σ) : Prop where
  inclusion : d.inclusion.comp σ = m.branch.comp c.inclusion
  retraction : d.retraction.comp m.branch = σ.comp c.retraction
  homotopy : HEq (strongPostcomp d.homotopy σ) (strongPrecomp c.homotopy σ)

variable [IsGroupoid Γ] [IsLocallyGroupoid Γ] [IsGroupoid Δ] [IsLocallyGroupoid Δ]
variable {Θ : StrictTwoCategory.{u,v,w}}
noncomputable def liftMap {n} (tail : FiniteDependentTail Γ n Θ)
    (c : ContractionPresentation Γ) (d : ContractionPresentation Δ)
    (σ : StrictPseudofunctor Δ Γ) (m : ContractionMap c d σ) (hm : m.Lawful) :
    {m' : ContractionMap (tail.liftSplit c) ((tail.reindexTail σ).tail.liftSplit d)
      (tail.reindexTail σ).substitution // m'.Lawful} := by
  induction tail with
  | nil => exact ⟨m, hm⟩
  | @snoc n Θ tail E objects cells ih =>
    let c₀ := tail.liftSplit c
    let d₀ := (tail.reindexTail σ).tail.liftSplit d
    let σ₁ := (tail.reindexTail σ).substitution
    letI : IsGroupoid Θ := tail.groupoid
    letI : IsLocallyGroupoid Θ := tail.locallyGroupoid
    letI : IsGroupoid (tail.reindexTail σ).target := (tail.reindexTail σ).tail.groupoid
    letI : IsLocallyGroupoid (tail.reindexTail σ).target := (tail.reindexTail σ).tail.locallyGroupoid
    letI : ∀x, IsGroupoid (E.obj x) := objects
    letI : ∀x, IsLocallyGroupoid (E.obj x) := cells
    letI : ∀x, IsIso (c₀.homotopy.app x) := fun _ => IsGroupoid.all_isIso _
    letI : ∀x, IsIso (d₀.homotopy.app x) := fun _ => IsGroupoid.all_isIso _
    refine ⟨⟨contractionBranchSubstitution c₀.inclusion d₀.inclusion σ₁ ih.val.branch
      ih.property.inclusion E⟩, ?_⟩
    constructor
    · exact contractionInclusion_reindex c₀.inclusion d₀.inclusion σ₁ ih.val.branch ih.property.inclusion E
    · exact contractionRetraction_reindex c₀.inclusion c₀.retraction d₀.inclusion d₀.retraction
        σ₁ ih.val.branch ih.property.inclusion ih.property.retraction
        c₀.homotopy d₀.homotopy ih.property.homotopy E
    · exact contractionRetractionHomotopy_reindex c₀.inclusion c₀.retraction d₀.inclusion d₀.retraction
        σ₁ ih.val.branch ih.property.inclusion ih.property.retraction
        c₀.homotopy d₀.homotopy ih.property.homotopy E

universe uE vE wE
noncomputable def reindexBranch {n} (tail : FiniteDependentTail Γ n Θ)
    (c : ContractionPresentation Γ) (c' : ContractionPresentation Δ)
    (σ : StrictPseudofunctor Δ Γ) (m : ContractionMap c c' σ) (hm : m.Lawful)
    (E : Family.{u,v,w,uE,vE,wE} Θ)
    (d : Section (reindex (tail.liftSplit c).inclusion E)) :
    Section (reindex ((tail.reindexTail σ).tail.liftSplit c').inclusion
      (reindex (tail.reindexTail σ).substitution E)) :=
  retractionBranchReindex (tail.liftSplit c).inclusion
    ((tail.reindexTail σ).tail.liftSplit c').inclusion (tail.reindexTail σ).substitution
    (tail.liftMap c c' σ m hm).val.branch (tail.liftMap c c' σ m hm).property.inclusion E d

/-- Every finite dependent extension preserves elimination under the constructed substitution. -/
theorem eliminate_reindex {n} (tail : FiniteDependentTail Γ n Θ)
    (c : ContractionPresentation Γ) (c' : ContractionPresentation Δ)
    (σ : StrictPseudofunctor Δ Γ) (m : ContractionMap c c' σ) (hm : m.Lawful)
    (E : Family.{u,v,w,uE,vE,wE} Θ)
    (d : Section (reindex (tail.liftSplit c).inclusion E)) :
    (tail.eliminate c E d).reindex E (tail.reindexTail σ).substitution =
      (tail.reindexTail σ).tail.eliminate c' (reindex (tail.reindexTail σ).substitution E)
        (tail.reindexBranch c c' σ m hm E d) :=
  retractionJ_reindex _ _ _ _ _ _ (tail.liftMap c c' σ m hm).property.inclusion
    (tail.liftMap c c' σ m hm).property.retraction _ _
    (tail.liftMap c c' σ m hm).property.homotopy E d
end SquareKit.Internal.PathTransport.TwoFamily.FiniteDependentTail
