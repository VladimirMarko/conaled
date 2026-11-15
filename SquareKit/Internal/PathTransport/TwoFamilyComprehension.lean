import SquareKit.Internal.PathTransport.TwoFamilySectionHEq
import SquareKit.Internal.PathTransport.TwoFamilyHEq
/-! Context extension pairs a substitution with its selected section. Projection,
variable recovery, and reconstruction retain all higher data. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Strict Δ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable (σ : StrictPseudofunctor Δ Γ) (s : Section (TwoFamily.reindex σ F))

def pairLift : StrictPseudofunctor Δ (Total F) := s.lift.comp (reindexHigher F σ)

theorem pairLift_projection : (pairLift F σ s).comp (projectionHigher F) = σ := by
  calc
    (s.lift.comp (reindexHigher F σ)).comp (projectionHigher F) =
        s.lift.comp ((reindexHigher F σ).comp (projectionHigher F)) :=
      StrictTwoTransformation.functor_ext rfl
    _ = s.lift.comp ((projectionHigher (reindex σ F)).comp σ) :=
      congrArg (fun H => s.lift.comp H) (reindexHigher_projection F σ)
    _ = (s.lift.comp (projectionHigher (reindex σ F))).comp σ :=
      StrictTwoTransformation.functor_ext rfl
    _ = (StrictPseudofunctor.id Δ).comp σ := congrArg (fun H => H.comp σ) s.over
    _ = σ := StrictTwoTransformation.functor_id_comp σ

theorem pairLift_variable_family :
    reindex (pairLift F σ s) (reindex (projectionHigher F) F) = reindex σ F := by
  rw [reindex_comp, pairLift_projection]

theorem Section.hext_family {A B : Family.{uΔ,vΔ,wΔ,u,v,w} Δ} (e : A = B)
    (a : Section A) (b : Section B)
    (ho : ∀ x, HEq (a.lift.obj x).fiber (b.lift.obj x).fiber)
    (hm : ∀ {x y} (p : x ⟶ y), HEq (a.lift.map p).fiber (b.lift.map p).fiber)
    (hc : ∀ {x y} {p q : x ⟶ y} (α : p ⟶ q), HEq (a.lift.map₂ α).fiber (b.lift.map₂ α).fiber) :
    HEq a b := by
  cases e
  exact heq_of_eq (Section.ext_fiber _ _ _ ho (fun p => hm p) (fun α => hc α))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem pairLift_variable :
    Section.cast (pairLift_variable_family F σ s)
      ((variableSection F).reindex _ (pairLift F σ s)) = s := by
  apply eq_of_heq
  apply HEq.trans (Section.cast_heq (pairLift_variable_family F σ s) _)
  change HEq (Section.cast _ (sectionOfLift _ ((pairLift F σ s).comp (variableSection F).lift))) s
  apply HEq.trans (Section.cast_heq _ _)
  apply Section.hext_family
    ((congrArg (fun k => reindex k (reindex (projectionHigher F) F))
      ((variableSection F).reindex_base _ (pairLift F σ s))).trans
      (pairLift_variable_family F σ s))
  · intro x; rfl
  · intro x y p; rfl
  · intro x y p q α; rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem variable_reindex_eq_sectionOfLift (h : StrictPseudofunctor Δ (Total F)) :
    Section.cast (reindex_comp F (projectionHigher F) h)
      ((variableSection F).reindex _ h) = sectionOfLift F h := by
  apply eq_of_heq
  apply HEq.trans (Section.cast_heq (reindex_comp F (projectionHigher F) h) _)
  change HEq (Section.cast _ (sectionOfLift _ (h.comp (variableSection F).lift))) (sectionOfLift F h)
  apply HEq.trans (Section.cast_heq _ _)
  apply Section.hext_family
    ((congrArg (fun k => reindex k (reindex (projectionHigher F) F))
      ((variableSection F).reindex_base _ h)).trans (reindex_comp F (projectionHigher F) h))
  · intro x; rfl
  · intro x y p; rfl
  · intro x y p q α; rfl

theorem pairLift_eta (h : StrictPseudofunctor Δ (Total F)) :
    pairLift F (h.comp (projectionHigher F))
      (Section.cast (reindex_comp F (projectionHigher F) h)
        ((variableSection F).reindex _ h)) = h := by
  rw [variable_reindex_eq_sectionOfLift]
  exact factorHigher_reindex F h
end SquareKit.Internal.PathTransport.TwoFamily
