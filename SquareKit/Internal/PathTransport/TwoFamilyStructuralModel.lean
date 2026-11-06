import SquareKit.Internal.PathTransport.TwoFamilyModelData
import SquareKit.Internal.PathTransport.TwoFamilyClosedReflexivitySubstitution
import SquareKit.Internal.PathTransport.TwoFamilyComprehension
import SquareKit.Internal.PathTransport.Model
/-! A constructed higher structural interpretation. All small strict two-groupoidal
families are admitted. The designated base and primitive fiber types are constant
parameters; family declarations may still denote arbitrary dependent families. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ Δ : Context.{u}}
noncomputable def Family.identity (A : Family Γ) (x y : TwoFamily.Section A.data) : Family Γ where
  data := TwoFamily.closedId A.data x y
  groupoid := inferInstance
  locallyGroupoid := inferInstance

theorem Family.identity_reindex (A : Family Γ) (x y : TwoFamily.Section A.data)
    (σ : StrictPseudofunctor Δ Γ) :
    (A.identity x y).reindex σ = (A.reindex σ).identity (x.reindex A.data σ) (y.reindex A.data σ) :=
  Family.ext (TwoFamily.closedId_reindex A.data σ x y)

private theorem lift_heq {A B : Type u} {a : A} {b : B} (h : HEq a b) :
    HEq (ULift.up.{u+1} a) (ULift.up.{u+1} b) := by cases h; rfl

private theorem family_cast_down {Γ : Context.{u}} {A B : Family Γ} (e : A = B)
    (t : ULift.{u+1} (TwoFamily.Section A.data)) :
    (cast (congrArg (fun X : Family Γ => ULift.{u+1} (TwoFamily.Section X.data)) e) t).down =
      TwoFamily.Section.cast (congrArg Family.data e) t.down := by cases e; rfl

noncomputable def structuralModel (C D : Context.{u}) : Typed.StructuralModel.{u+1} where
  Context := Context.{u}
  Family := Family
  Section _ A := ULift.{u+1} (TwoFamily.Section A.data)
  Substitution Δ Γ := ULift.{u+1} (StrictPseudofunctor Δ Γ)
  empty := Context.empty
  extend _ A := A.total
  idSub Γ := ⟨StrictPseudofunctor.id Γ⟩
  compSub σ τ := ⟨τ.down.comp σ.down⟩
  subTy A σ := A.reindex σ.down
  subTm t σ := ⟨t.down.reindex _ σ.down⟩
  weaken _ A := ⟨TwoFamily.projectionHigher A.data⟩
  genericVariable _ A := ⟨TwoFamily.variableSection A.data⟩
  pairSub A σ t := ⟨TwoFamily.pairLift A.data σ.down t.down⟩
  base Γ := Family.constant Γ C
  fiber {_} _ := Family.constant _ D
  identity A x y := A.identity x.down y.down
  reflexivity A x := ⟨TwoFamily.closedReflexivity A.data x.down⟩
  comp_id_left σ := ULift.ext (StrictTwoTransformation.functor_comp_id σ.down)
  comp_id_right σ := ULift.ext (StrictTwoTransformation.functor_id_comp σ.down)
  comp_assoc σ τ υ := ULift.ext (StrictTwoTransformation.functor_ext rfl)
  subTy_id A := A.reindex_id
  subTy_comp A σ τ := A.reindex_comp σ.down τ.down
  subTm_id t := by
    apply lift_heq
    exact (TwoFamily.Section.cast_heq _ _).symm.trans
      (heq_of_eq (TwoFamily.Section.reindex_id _ t.down))
  subTm_comp t σ τ := lift_heq (TwoFamily.Section.reindex_comp_heq t.down σ.down τ.down)
  base_sub σ := Family.constant_reindex C σ.down
  fiber_sub _ σ := Family.constant_reindex D σ.down
  identity_sub A x y σ := A.identity_reindex x.down y.down σ.down
  refl_sub A x σ := lift_heq (TwoFamily.closedReflexivity_reindex_heq A.data σ.down x.down)
  weaken_pair A σ t := ULift.ext (TwoFamily.pairLift_projection A.data σ.down t.down)
  variable_pair A σ t := by
    apply lift_heq
    exact (TwoFamily.Section.cast_heq _ _).symm.trans
      (heq_of_eq (TwoFamily.pairLift_variable A.data σ.down t.down))
  pair_eta A σ := by
    apply ULift.ext
    rw [family_cast_down (A.reindex_comp (TwoFamily.projectionHigher A.data) σ.down)]
    exact TwoFamily.pairLift_eta A.data σ.down
end SquareKit.Internal.PathTransport.HigherInterpretation
