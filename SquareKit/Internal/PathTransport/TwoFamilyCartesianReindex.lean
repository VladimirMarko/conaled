import SquareKit.Internal.PathTransport.TwoFamilyCartesianStrong
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uD vD wD uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable {Δ : Type uD} [Bicategory.{wD,vD} Δ] [Strict Δ]
variable (E : Family.{u,v,w,uE,vE,wE} Γ) (σ : StrictPseudofunctor Δ Γ)
private theorem total_comp_base {x y : Total E} {p q r : x ⟶ y}
    (α : p ⟶ q) (β : q ⟶ r) : (α ≫ β).base = α.base ≫ β.base := rfl
theorem equalityHomFiber_reindex {x y : Total (reindex σ E)} (p : x ⟶ y)
    (h : EqualityHomFiber (reindex σ E) p) : EqualityHomFiber E ((reindexHigher E σ).map p) := h

theorem equalityFiber_reindex_map {x y : Total (reindex σ E)} {p q : x ⟶ y} (α : p ⟶ q)
    (h : EqualityFiber (reindex σ E) α) : EqualityFiber E ((reindexHigher E σ).map₂ α) := h

variable {X : Type*} [Bicategory X] [Strict X]
variable {F G : StrictPseudofunctor X (Total (reindex σ E))}
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
theorem postcompReindex_equalityFiber {x y : X} (p : x ⟶ y)
    (h : EqualityFiber (reindex σ E) (η.naturality p).hom) :
    EqualityFiber E ((strongPostcomp η (reindexHigher E σ)).naturality p).hom := by
  simp only [strongPostcomp, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    StrictPseudofunctor.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv]
  exact equalityFiber_comp E (equalityFiber_cast E _)
    (equalityFiber_comp E (equalityFiber_reindex_map E σ _ h) (equalityFiber_cast E _))

theorem postcompReindex_comparison_base {x y : X} (p : x ⟶ y) :
    HEq (((strongPostcomp η (reindexHigher E σ)).naturality p).hom).base
      (σ.map₂ ((η.naturality p).hom).base) := by
  simp only [strongPostcomp, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    StrictPseudofunctor.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv]
  simp only [total_comp_base]
  erw [total_eqToHom_base E, total_eqToHom_base E]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)
end SquareKit.Internal.PathTransport.TwoFamily
