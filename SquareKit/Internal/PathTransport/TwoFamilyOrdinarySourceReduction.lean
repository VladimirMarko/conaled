import SquareKit.Internal.PathTransport.TwoFamilyOrdinaryIdentityReduction
import SquareKit.Internal.PathTransport.TwoFamilyOrdinaryLeftIdentity
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u})
local notation "M" => fullModel C D
theorem branchArrowIdentity_of_sourceValues {Γ Δ : Context.{u}}
 (F : Family Γ) (s t : ULift.{u+1} (TwoFamily.Section F.data))
 (σ : ULift.{u+1} (StrictPseudofunctor Δ Γ))
 (d : ULift.{u+1} (TwoFamily.Section (reindex σ.down (closedId F.data s.down t.down))))
 (B : Family Δ) [∀δ, Subsingleton (B.data.obj δ)]
 (v : ULift.{u+1} (TwoFamily.Section B.data))
 (e : (M).subTy F σ = B)
 (h : SectionIdentityValues ((M).subTy ((M).identity F s t) σ) B d v) :
 SourceContraction.BranchArrowIdentity F σ.down s.down t.down d.down :=
 SourceContraction.branchArrowIdentity_of_values F σ.down s.down t.down d.down B v.down e h
variable {Γ : Context.{u}} (A B : Family Γ)
variable (t : ULift.{u+1} (TwoFamily.Section (reindex (projectionHigher A.data) B.data)))
variable (x : ULift.{u+1} (TwoFamily.Section A.data))
theorem ordinaryApCodomain_root :
 (motive M A ((M).subTy B ((M).weaken Γ A)) x).reindex ((M).toStructuralModel.rootSub A x).down = B :=
 (motive_root M A _ x).trans ((M).toStructuralModel.weaken_section_type A x B)
variable [∀γ, Subsingleton (B.data.obj γ)]
set_option linter.defProp false
def ordinaryApBranch_arrow_identity :=
 branchArrowIdentity_of_sourceValues C D
 (motive M A ((M).subTy B ((M).weaken Γ A)) x)
 (ordinaryApLeft M A B t x) (ordinaryApRight M A B t x)
 ((M).toStructuralModel.rootSub A x)
 (ordinaryApBranch M A B t x) B
 (ordinaryApply M A B t x) (ordinaryApCodomain_root C D A B x)
 (ordinaryApBranch_identity C D A B t x)
def ordinaryApLeft_arrow_identity := by
 letI : ∀z, Subsingleton ((motive M A ((M).subTy B ((M).weaken Γ A)) x).data.obj z) :=
  fun z => inferInstanceAs (Subsingleton (B.data.obj z.base.base))
 have f := SourceContraction.leftArrowIdentity_of_values (rootContraction C D A x).val
  (motive M A ((M).subTy B ((M).weaken Γ A)) x)
  (ordinaryApLeft M A B t x).down
  (fun z => ((ordinaryApply M A B t x).down.normalObj B.data z.base.base).fiber)
 have h := ordinaryApLeft_identity C D A B t x
 run_tac Lean.Elab.Tactic.withMainContext do
  let f ← Lean.Meta.getLocalDeclFromUserName `f
  let h ← Lean.Meta.getLocalDeclFromUserName `h
  let e := Lean.mkApp f.toExpr h.toExpr
  let ty ← Lean.Meta.inferType e
  let goal ← Lean.Elab.Tactic.getMainGoal
  unless ← Lean.Meta.isDefEq (← goal.getType) ty do
   throwError "result type mismatch"
  goal.assign e
  Lean.Elab.Tactic.replaceMainGoal []

variable (y : ULift.{u+1} (TwoFamily.Section A.data))
variable (p : ULift.{u+1} (TwoFamily.Section (closedId A.data x.down y.down)))
def ordinaryApValue_reduced := by
 letI : ∀z, Subsingleton ((motive M A ((M).subTy B ((M).weaken Γ A)) x).data.obj z) :=
  fun z => inferInstanceAs (Subsingleton (B.data.obj z.base.base))
 exact SourceContraction.reduce_identity_endpoint (rootContraction C D A x).val
  (motive M A ((M).subTy B ((M).weaken Γ A)) x)
  (ordinaryApLeft M A B t x).down (ordinaryApRight M A B t x).down
  (ordinaryApBranch M A B t x).down
  (ordinaryApLeft_arrow_identity C D A B t x)
  (ordinaryApBranch_arrow_identity C D A B t x)
  ((M).toStructuralModel.endpointSub A x y p).down
  ((M).identity B (ordinaryApply M A B t x) (ordinaryApply M A B t y))
  (ordinaryApValue M A B t x y p).down (ordinaryApValue_action C D A B t x y p)
end SquareKit.Internal.PathTransport.HigherInterpretation
