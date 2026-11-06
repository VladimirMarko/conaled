import Examples.CubicalFrozenActionParallel
import Examples.CubicalFrozenHigherObservation

/-! The original frozen path operands under the concrete cubical assignment. -/
noncomputable section
namespace Examples.CubicalFrozenActionInputs
set_option maxHeartbeats 800000
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SquareKit.Cubical.CategoryCocycles
open Examples.CubicalCocycleAssignment Examples.FrozenMemoStages
open Examples.FrozenOrdinaryAction

private theorem cast_section_reindex {Γ Δ : Context.{0}} {A B : LawfulFamily Γ}
    (e : A = B) (t : ULift.{1} (Term A.family)) (σ : Δ ⟶ Γ) :
    HEq (((cast (congrArg (fun C : LawfulFamily Γ => ULift.{1} (Term C.family)) e) t).down).reindex σ)
      (t.down.reindex σ) := by cases e; rfl

private theorem cast_down {Γ : Context.{0}} {A B : LawfulFamily Γ}
    (e : A = B) (t : ULift.{1} (Term A.family)) :
    HEq ((cast (congrArg (fun C : LawfulFamily Γ => ULift.{1} (Term C.family)) e) t).down)
      t.down := by cases e; rfl

theorem assigned_h : HEq (reindexedH cocycleModel cocycleBase cocycleRootedFamily ⟨assignInput⟩).down
    selectedNormalizedHomotopy := by
  apply HEq.trans _ (heq_of_eq selectedNormalizedHomotopy_eq.symm)
  apply (cast_down (reindexedHType_eq cocycleModel cocycleBase cocycleRootedFamily ⟨assignInput⟩) _).trans
  have h₁ := cast_section_reindex
    ((parallelPoints.addH.reindex (CM.weaken afterHomotopy.context (qFamily CM cocycleBase cocycleRootedFamily))).toParallel.identity_reindex
      (CM.weaken afterQ.context (uFamily CM cocycleBase cocycleRootedFamily)))
    (CM.subTm (parallelPoints.addH.reindex (CM.weaken afterHomotopy.context (qFamily CM cocycleBase cocycleRootedFamily))).h
      (CM.weaken afterQ.context (uFamily CM cocycleBase cocycleRootedFamily))) assignInput
  apply h₁.trans
  have h₂ := cast_section_reindex
    (parallelPoints.addH.toParallel.identity_reindex (CM.weaken afterHomotopy.context (qFamily CM cocycleBase cocycleRootedFamily)))
    (CM.subTm parallelPoints.addH.h (CM.weaken afterHomotopy.context (qFamily CM cocycleBase cocycleRootedFamily))) assignQ
  apply h₂.trans
  have h₃ := cast_section_reindex
    (parallelPoints.identity_reindex (CM.weaken parallelPoints.context parallelPoints.identity))
    (CM.genericVariable parallelPoints.context parallelPoints.identity) assignHomotopy
  exact h₃.trans (Term.convert_heq homotopy_at_assignment.symm (secondIdentity terminal))

end Examples.CubicalFrozenActionInputs
