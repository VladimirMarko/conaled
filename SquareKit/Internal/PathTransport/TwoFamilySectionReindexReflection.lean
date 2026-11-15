import SquareKit.Internal.PathTransport.TwoFamilyComprehension
/-! Recombination through two pullbacks reflects the whole selected section, including its genuine cells. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
variable {C A A' D : Type*}
variable [Bicategory C] [Strict C] [Bicategory A] [Strict A]
variable [Bicategory A'] [Strict A'] [Bicategory D] [Strict D]
variable (B : Family C)
theorem Section.reindex_lifts_hext
    (σ : StrictPseudofunctor A C) (τ : StrictPseudofunctor D A)
    (σ' : StrictPseudofunctor A' C) (τ' : StrictPseudofunctor D A')
    (s : Section (TwoFamily.reindex τ (TwoFamily.reindex σ B)))
    (t : Section (TwoFamily.reindex τ' (TwoFamily.reindex σ' B)))
    (e : TwoFamily.reindex τ (TwoFamily.reindex σ B) = TwoFamily.reindex τ' (TwoFamily.reindex σ' B))
    (h : (s.lift.comp (reindexHigher (TwoFamily.reindex σ B) τ)).comp (reindexHigher B σ) =
      (t.lift.comp (reindexHigher (TwoFamily.reindex σ' B) τ')).comp (reindexHigher B σ')) :
    HEq s t := by
  apply Section.hext_family e
  · intro x
    exact congr_arg_heq (fun H : StrictPseudofunctor D (Total B) => (H.obj x).fiber) h
  · intro x y p
    exact congr_arg_heq (fun H : StrictPseudofunctor D (Total B) => (H.map p).fiber) h
  · intro x y p q α
    exact congr_arg_heq (fun H : StrictPseudofunctor D (Total B) => (H.map₂ α).fiber) h
end SquareKit.Internal.PathTransport.TwoFamily
