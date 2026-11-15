import Examples.FrozenOrdinaryActionReindex
import Examples.CubicalFrozenHigherObservation

/-! The original frozen path operands under the concrete cubical assignment. -/
noncomputable section
namespace Examples.CubicalFrozenActionInputs
set_option maxHeartbeats 800000
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SquareKit.Cubical.CategoryCocycles
open Examples.CubicalCocycleAssignment Examples.FrozenMemoStages
open Examples.FrozenOrdinaryAction

abbrev assignedType := reindexedType cocycleModel cocycleBase cocycleRootedFamily ⟨assignInput⟩
example : assignedType.family = FirstIdentityFamily terminal.{0} := rfl

private theorem cast_section_reindex {Γ Δ : Context.{0}} {A B : LawfulFamily Γ}
    (e : A = B) (t : ULift.{1} (Term A.family)) (σ : Δ ⟶ Γ) :
    HEq (((cast (congrArg (fun C : LawfulFamily Γ => ULift.{1} (Term C.family)) e) t).down).reindex σ)
      (t.down.reindex σ) := by cases e; rfl

private theorem cast_down {Γ : Context.{0}} {A B : LawfulFamily Γ}
    (e : A = B) (t : ULift.{1} (Term A.family)) :
    HEq ((cast (congrArg (fun C : LawfulFamily Γ => ULift.{1} (Term C.family)) e) t).down)
      t.down := by cases e; rfl

theorem assigned_p : (reindexedP cocycleModel cocycleBase cocycleRootedFamily ⟨assignInput⟩).down =
    FirstIdentityPoint terminal.{0} := by
  apply eq_of_heq
  apply (cast_down (reindexedType_eq cocycleModel cocycleBase cocycleRootedFamily ⟨assignInput⟩) _).trans
  have h₁ := cast_section_reindex
    (CM.identity_sub (parallelPoints.addH.reindex (CM.weaken afterHomotopy.context (qFamily CM cocycleBase cocycleRootedFamily))).family
      (parallelPoints.addH.reindex (CM.weaken afterHomotopy.context (qFamily CM cocycleBase cocycleRootedFamily))).x
      (parallelPoints.addH.reindex (CM.weaken afterHomotopy.context (qFamily CM cocycleBase cocycleRootedFamily))).y
      (CM.weaken afterQ.context (uFamily CM cocycleBase cocycleRootedFamily)))
    (CM.subTm (parallelPoints.addH.reindex (CM.weaken afterHomotopy.context (qFamily CM cocycleBase cocycleRootedFamily))).p
      (CM.weaken afterQ.context (uFamily CM cocycleBase cocycleRootedFamily))) assignInput
  apply h₁.trans
  have h₂ := cast_section_reindex
    (CM.identity_sub parallelPoints.addH.family parallelPoints.addH.x parallelPoints.addH.y
      (CM.weaken afterHomotopy.context (qFamily CM cocycleBase cocycleRootedFamily)))
    (CM.subTm parallelPoints.addH.p (CM.weaken afterHomotopy.context (qFamily CM cocycleBase cocycleRootedFamily))) assignQ
  apply h₂.trans
  have h₃ := cast_section_reindex
    (CM.identity_sub parallelPoints.family parallelPoints.x parallelPoints.y
      (CM.weaken parallelPoints.context parallelPoints.identity))
    (CM.subTm parallelPoints.p (CM.weaken parallelPoints.context parallelPoints.identity)) assignHomotopy
  exact h₃.trans selected_p

end Examples.CubicalFrozenActionInputs
