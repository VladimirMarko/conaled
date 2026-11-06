import SquareKit.Internal.PathTransport.TwoFamilyHEq
import SquareKit.Internal.PathTransport.TwoFamilySectionLaws
/-! Whole higher reindexing laws across proved family equalities. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
private theorem functor_map_heq {A B : Type*} [Bicategory A] [Bicategory B]
    (K : StrictPseudofunctor A B) {x y x' y' : A} (hx : x = x') (hy : y = y')
    {p : x ⟶ y} {q : x' ⟶ y'} (hp : HEq p q) : HEq (K.map p) (K.map q) := by
  cases hx
  cases hy
  cases eq_of_heq hp
  rfl
private theorem functor_cell_heq {A B : Type*} [Bicategory A] [Bicategory B]
    (K : StrictPseudofunctor A B) {x y x' y' : A} (hx : x = x') (hy : y = y')
    {p q : x ⟶ y} {p' q' : x' ⟶ y'} (hp : HEq p p') (hq : HEq q q')
    {α : p ⟶ q} {β : p' ⟶ q'} (hα : HEq α β) : HEq (K.map₂ α) (K.map₂ β) := by
  cases hx
  cases hy
  cases eq_of_heq hp
  cases eq_of_heq hq
  cases eq_of_heq hα
  rfl
universe u v w uf vf wf
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable {Δ Θ : Type*} [Bicategory Δ] [Strict Δ] [Bicategory Θ] [Strict Θ]
variable (F : Family.{u,v,w,uf,vf,wf} Γ)
variable (σ : StrictPseudofunctor Δ Γ) (τ : StrictPseudofunctor Θ Δ)
theorem reindexHigher_comp_heq :
    HEq ((reindexHigher (reindex σ F) τ).comp (reindexHigher F σ))
      (reindexHigher F (τ.comp σ)) := by
  let e := reindex_comp F σ τ
  have ho : ∀ x : Total (reindex τ (reindex σ F)),
      ∀ x' : Total (reindex (τ.comp σ) F), HEq x x' →
      ((reindexHigher (reindex σ F) τ).comp (reindexHigher F σ)).obj x =
        (reindexHigher F (τ.comp σ)).obj x' := by
    intro x x' hx
    apply total_obj_hext F
    · exact congrArg (fun a => σ.obj (τ.obj a)) (total_obj_base_heq_family e hx)
    · exact total_obj_fiber_heq_family e hx
  have hm : ∀ {x y : Total (reindex τ (reindex σ F))}
      {x' y' : Total (reindex (τ.comp σ) F)} (hx : HEq x x') (hy : HEq y y')
      (p : x ⟶ y) (q : x' ⟶ y'), HEq p q →
      HEq (((reindexHigher (reindex σ F) τ).comp (reindexHigher F σ)).map p)
        ((reindexHigher F (τ.comp σ)).map q) := by
    intro x y x' y' hx hy p q hp
    apply total_hom_hext F (ho x x' hx) (ho y y' hy)
    · exact functor_map_heq (τ.comp σ) (total_obj_base_heq_family e hx)
        (total_obj_base_heq_family e hy) (total_hom_base_heq_family e hx hy hp)
    · exact total_hom_fiber_heq_family e hx hy hp
  apply total_functor_hext_family e rfl
  · intro x x' hx; exact heq_of_eq (ho x x' hx)
  · exact hm
  · intro x y x' y' hx hy p q p' q' hp hq α β hα
    apply total_cell_hext F (ho x x' hx) (ho y y' hy)
      (hm hx hy p p' hp) (hm hx hy q q' hq)
    · exact functor_cell_heq (τ.comp σ) (total_obj_base_heq_family e hx)
        (total_obj_base_heq_family e hy) (total_hom_base_heq_family e hx hy hp)
        (total_hom_base_heq_family e hx hy hq)
        (total_cell_base_heq_family e hx hy hp hq hα)
    · exact total_cell_fiber_heq_family e hx hy hp hq hα

section Identity
variable (E : Family.{u,v,w,uf,vf,wf} Γ)
theorem reindexHigher_id_heq : HEq (reindexHigher E (StrictPseudofunctor.id Γ))
    (StrictPseudofunctor.id (Total E)) := by
  have e := StrictTwoTransformation.functor_id_comp E
  apply total_functor_hext_family e rfl
  · intro x x' hx
    exact heq_of_eq (total_obj_hext E (total_obj_base_heq_family e hx)
      (total_obj_fiber_heq_family e hx))
  · intro x y x' y' hx hy p q hp
    apply total_hom_hext E
      (total_obj_hext E (total_obj_base_heq_family e hx) (total_obj_fiber_heq_family e hx))
      (total_obj_hext E (total_obj_base_heq_family e hy) (total_obj_fiber_heq_family e hy))
    · exact total_hom_base_heq_family e hx hy hp
    · exact total_hom_fiber_heq_family e hx hy hp
  · intro x y x' y' hx hy p q p' q' hp hq α β hα
    apply total_cell_hext E
      (total_obj_hext E (total_obj_base_heq_family e hx) (total_obj_fiber_heq_family e hx))
      (total_obj_hext E (total_obj_base_heq_family e hy) (total_obj_fiber_heq_family e hy))
    · exact total_hom_hext E
        (total_obj_hext E (total_obj_base_heq_family e hx) (total_obj_fiber_heq_family e hx))
        (total_obj_hext E (total_obj_base_heq_family e hy) (total_obj_fiber_heq_family e hy))
        _ _ (total_hom_base_heq_family e hx hy hp) (total_hom_fiber_heq_family e hx hy hp)
    · exact total_hom_hext E
        (total_obj_hext E (total_obj_base_heq_family e hx) (total_obj_fiber_heq_family e hx))
        (total_obj_hext E (total_obj_base_heq_family e hy) (total_obj_fiber_heq_family e hy))
        _ _ (total_hom_base_heq_family e hx hy hq) (total_hom_fiber_heq_family e hx hy hq)
    · exact total_cell_base_heq_family e hx hy hp hq hα
    · exact total_cell_fiber_heq_family e hx hy hp hq hα

end Identity

section EqualityTransport
variable {F G H : Family.{u,v,w,uf,vf,wf} Γ}
/-- Equality transport retains all three dimensions of total contexts. -/
def familyCast (e : F = G) : StrictPseudofunctor (Total F) (Total G) := by
  cases e
  exact StrictPseudofunctor.id (Total F)

theorem familyCast_heq (e : F = G) :
    HEq (familyCast e) (StrictPseudofunctor.id (Total F)) := by cases e; rfl

theorem familyCast_comp (e : F = G) (e' : G = H) :
    (familyCast e).comp (familyCast e') = familyCast (e.trans e') := by
  cases e
  cases e'
  exact StrictTwoTransformation.functor_ext rfl

variable {D : Type*} [Bicategory D] [Strict D]
theorem familyCast_precomp_heq (e : F = G) (K : StrictPseudofunctor (Total G) D) :
    HEq ((familyCast e).comp K) K := by
  cases e
  exact heq_of_eq (StrictTwoTransformation.functor_id_comp K)

theorem familyCast_postcomp_heq (e : F = G) (K : StrictPseudofunctor D (Total F)) :
    HEq (K.comp (familyCast e)) K := by
  cases e
  exact heq_of_eq (StrictTwoTransformation.functor_comp_id K)

theorem familyCast_precomp_eq_of_heq (e : F = G)
    (K : StrictPseudofunctor (Total F) D) (L : StrictPseudofunctor (Total G) D)
    (h : HEq K L) : (familyCast e).comp L = K := by
  exact eq_of_heq ((familyCast_precomp_heq e L).trans h.symm)

end EqualityTransport

/-- Two extension substitutions compose after the proved family equality. -/
theorem reindexHigher_comp_cast :
    (familyCast (reindex_comp F σ τ).symm).comp
      ((reindexHigher (reindex σ F) τ).comp (reindexHigher F σ)) =
        reindexHigher F (τ.comp σ) :=
  familyCast_precomp_eq_of_heq (reindex_comp F σ τ).symm _ _
    (reindexHigher_comp_heq F σ τ).symm
end SquareKit.Internal.PathTransport.TwoFamily
