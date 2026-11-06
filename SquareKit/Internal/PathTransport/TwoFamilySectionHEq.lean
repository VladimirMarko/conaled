import SquareKit.Internal.PathTransport.TwoFamilySectionMapReindex
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w u' v' w' uΔ vΔ wΔ uΘ vΘ wΘ
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Bicategory.Strict Δ]
variable {Θ : Type uΘ} [Bicategory.{wΘ,vΘ} Θ] [Bicategory.Strict Θ]
variable {F G F' G' : Family.{u,v,w,u',v',w'} Γ}
/-- Family casts retain the full section as dependent data. -/
theorem Section.cast_heq (e : F = G) (s : Section F) : HEq (Section.cast e s) s := by
  cases e
  rfl
/-- Reindexing respects actual section equality across a family boundary. -/
theorem Section.reindex_heq (e : F = G) (s : Section F) (t : Section G)
    (h : HEq s t) (σ : StrictPseudofunctor Δ Γ) :
    HEq (s.reindex F σ) (t.reindex G σ) := by
  cases e
  cases eq_of_heq h
  rfl
/-- Equal substitutions act identically on the full dependent section. -/
theorem Section.reindex_functor_heq (s : Section F) {σ τ : StrictPseudofunctor Δ Γ}
    (h : σ = τ) : HEq (s.reindex F σ) (s.reindex F τ) := by
  cases h
  rfl
/-- Successive section substitution agrees with its composite before family casts. -/
theorem Section.reindex_comp_heq (s : Section F) (σ : StrictPseudofunctor Δ Γ)
    (τ : StrictPseudofunctor Θ Δ) :
    HEq ((s.reindex F σ).reindex _ τ) (s.reindex F (τ.comp σ)) :=
  (Section.cast_heq (TwoFamily.reindex_comp F σ τ) ((s.reindex F σ).reindex _ τ)).symm.trans
    (heq_of_eq (s.reindex_comp F σ τ))
/-- Equal coherent maps and equal input sections give equal output sections. -/
theorem Section.map_heq (eF : F = F') (eG : G = G')
    (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
    (θ : Pseudofunctor.StrongTrans F'.toPseudofunctor G'.toPseudofunctor)
    (hη : HEq η θ) (s : Section F) (t : Section F') (hs : HEq s t) :
    HEq (s.map η) (t.map θ) := by
  cases eF
  cases eG
  cases eq_of_heq hη
  cases eq_of_heq hs
  rfl
end SquareKit.Internal.PathTransport.TwoFamily
