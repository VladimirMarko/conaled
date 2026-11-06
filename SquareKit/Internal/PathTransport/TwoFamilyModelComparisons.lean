import SquareKit.Internal.PathTransport.TwoFamilyStructuralModel
import SquareKit.Internal.PathTransport.TwoFamilyPairLiftReindex
import SquareKit.Internal.PathTransport.Comprehension
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u})
local notation "M" => structuralModel C D
theorem sectionCast_down {Γ : Context.{u}} {A B : Family Γ} (e : A = B)
    (t : ULift.{u+1} (TwoFamily.Section A.data)) :
    (cast (congrArg (fun X : Family Γ => ULift.{u+1} (TwoFamily.Section X.data)) e) t).down =
      TwoFamily.Section.cast (congrArg Family.data e) t.down := by cases e; rfl

theorem lift_eq_reindexHigher {Γ Δ : Context.{u}} (A : Family Γ) (σ : StrictPseudofunctor Δ Γ) :
    ((M).lift A ⟨σ⟩).down = TwoFamily.reindexHigher A.data σ := by
  unfold Typed.StructuralModel.lift
  dsimp only [structuralModel]
  have hc := sectionCast_down (A.reindex_comp (Θ := (A.reindex σ).total) σ (TwoFamily.projectionHigher (A.reindex σ).data))
    (ULift.up (TwoFamily.variableSection (A.reindex σ).data))
  have hp := congrArg (fun t => TwoFamily.pairLift A.data
    ((TwoFamily.projectionHigher (A.reindex σ).data).comp σ) t) hc
  exact hp.trans (TwoFamily.pairLift_reindex A.data σ)

theorem lift_down_eq_reindexHigher {Γ Δ : Context.{u}} (A : Family Γ)
    (σ : ULift.{u+1} (StrictPseudofunctor Δ Γ)) :
    ((M).lift A σ).down = TwoFamily.reindexHigher A.data σ.down := by
  cases σ with
  | up σ => exact lift_eq_reindexHigher C D A σ

theorem familyComparison_eq_familyCast {Γ : Context.{u}} {A B : Family Γ} (e : A = B) :
    ((M).familyComparison e).down = TwoFamily.familyCast (congrArg Family.data e) := by
  cases e
  rfl
end SquareKit.Internal.PathTransport.HigherInterpretation
