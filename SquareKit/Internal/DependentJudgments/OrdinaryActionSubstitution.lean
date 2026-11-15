import SquareKit.Internal.DependentJudgments.OrdinaryActionSemantics
/-! Substitution of ordinary action preserves the chosen J section.
The function and path casts come from comprehension and identity substitution. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (M : Model.{u})
variable {Γ Δ : M.Context} (A C : M.Family Γ)
variable (t : M.Section (M.extend Γ A) (M.subTy C (M.weaken Γ A)))
theorem ordinaryFunction_type (σ : M.Substitution Δ Γ) :
 M.subTy (M.subTy C (M.weaken Γ A)) (M.toStructuralModel.lift A σ) =
 M.subTy (M.subTy C σ) (M.weaken Δ (M.subTy A σ)) := by
 rw [M.subTy_comp, M.toStructuralModel.weaken_lift, M.subTy_comp]
def ordinaryFunctionSub (σ : M.Substitution Δ Γ) :=
 cast (congrArg (M.Section _) (ordinaryFunction_type M A C σ))
  (M.subTm t (M.toStructuralModel.lift A σ))
theorem ordinaryApply_sub (x : M.Section Γ A) (σ : M.Substitution Δ Γ) :
 HEq (M.subTm (ordinaryApply M A C t x) σ)
 (ordinaryApply M (M.subTy A σ) (M.subTy C σ) (ordinaryFunctionSub M A C t σ) (M.subTm x σ)) := by
 apply (M.toStructuralModel.subTm_congr (M.toStructuralModel.weaken_section_type A x C).symm (cast_heq _ _) σ).trans
 apply (M.subTm_comp _ _ _).trans
 apply HEq.trans _ (cast_heq _ _).symm
 apply HEq.trans _ (M.toStructuralModel.subTm_congr (ordinaryFunction_type M A C σ).symm (cast_heq _ _) _).symm
 apply HEq.trans _ (M.subTm_comp _ _ _).symm
 rw [M.toStructuralModel.section_lift]
theorem ordinaryApType_sub (x : M.Section Γ A) (σ : M.Substitution Δ Γ) :
 M.subTy (motive M A (M.subTy C (M.weaken Γ A)) x) (M.toStructuralModel.pathSub A x σ) =
 motive M (M.subTy A σ) (M.subTy (M.subTy C σ) (M.weaken Δ (M.subTy A σ))) (M.subTm x σ) := by
 unfold motive
 rw [M.subTy_comp, M.toStructuralModel.weaken_pathSub, ← M.subTy_comp, ordinaryFunction_type]
theorem ordinaryApRight_sub (x : M.Section Γ A) (σ : M.Substitution Δ Γ) :
 HEq (M.subTm (ordinaryApRight M A C t x) (M.toStructuralModel.pathSub A x σ))
 (ordinaryApRight M (M.subTy A σ) (M.subTy C σ) (ordinaryFunctionSub M A C t σ) (M.subTm x σ)) := by
 apply (M.subTm_comp _ _ _).trans
 rw [M.toStructuralModel.weaken_pathSub]
 apply (M.subTm_comp _ _ _).symm.trans
 exact (M.toStructuralModel.subTm_congr (ordinaryFunction_type M A C σ).symm (cast_heq _ _) _).symm
theorem ordinaryApLeft_sub (x : M.Section Γ A) (σ : M.Substitution Δ Γ) :
 HEq (M.subTm (ordinaryApLeft M A C t x) (M.toStructuralModel.pathSub A x σ))
 (ordinaryApLeft M (M.subTy A σ) (M.subTy C σ) (ordinaryFunctionSub M A C t σ) (M.subTm x σ)) := by
 apply (M.subTm_comp _ _ _).trans
 rw [M.toStructuralModel.weaken_pathSub]
 apply (M.subTm_comp _ _ _).symm.trans
 apply M.toStructuralModel.subTm_congr (ordinaryFunction_type M A C σ)
 apply (M.subTm_comp _ _ _).trans
 rw [M.toStructuralModel.weaken_lift]
 apply (M.subTm_comp _ _ _).symm.trans
 exact M.toStructuralModel.subTm_congr rfl (ordinaryApply_sub M A C t x σ) _
theorem ordinaryApMotive_sub (x : M.Section Γ A) (σ : M.Substitution Δ Γ) :
 M.subTy (ordinaryApMotive M A C t x) (M.toStructuralModel.pathSub A x σ) =
 ordinaryApMotive M (M.subTy A σ) (M.subTy C σ) (ordinaryFunctionSub M A C t σ) (M.subTm x σ) := by
 rw [ordinaryApMotive, M.identity_sub]
 exact M.toStructuralModel.identity_congr (ordinaryApType_sub M A C x σ)
  (ordinaryApLeft_sub M A C t x σ) (ordinaryApRight_sub M A C t x σ)
theorem ordinaryApBranch_sub (x : M.Section Γ A) (σ : M.Substitution Δ Γ) :
 HEq (M.toStructuralModel.reindexBranch A x .nil σ (ordinaryApMotive M A C t x) (ordinaryApBranch M A C t x))
 (ordinaryApBranch M (M.subTy A σ) (M.subTy C σ) (ordinaryFunctionSub M A C t σ) (M.subTm x σ)) := by
 apply (cast_heq _ _).trans
 have hb : M.toStructuralModel.branchMap A x .nil σ = σ := by
  simp [StructuralModel.branchMap, Telescope.square]
 rw [hb]
 apply (M.toStructuralModel.subTm_congr (ordinaryApMotive_root M A C t x) (cast_heq _ _) σ).trans
 apply (M.refl_sub C (ordinaryApply M A C t x) σ).trans
 apply HEq.trans _ (cast_heq _ _).symm
 have h := eq_of_heq (ordinaryApply_sub M A C t x σ)
 rw [h]
theorem ordinaryApSection_sub (x : M.Section Γ A) (σ : M.Substitution Δ Γ) :
 HEq (M.subTm (ordinaryApSection M A C t x) (M.toStructuralModel.pathSub A x σ))
 (ordinaryApSection M (M.subTy A σ) (M.subTy C σ) (ordinaryFunctionSub M A C t σ) (M.subTm x σ)) := by
 apply (M.j_sub A x .nil _ _ σ).trans
 exact M.j_heq rfl (HEq.refl _) (HEq.refl _) (HEq.refl _)
  (heq_of_eq (ordinaryApMotive_sub M A C t x σ)) (ordinaryApBranch_sub M A C t x σ)
def ordinaryPathSub (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y))
 (σ : M.Substitution Δ Γ) :=
 cast (congrArg (M.Section Δ) (M.identity_sub A x y σ)) (M.subTm p σ)
theorem ordinaryEndpoint_square (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y))
 (σ : M.Substitution Δ Γ) :
 M.compSub (M.toStructuralModel.pathSub A x σ)
  (M.toStructuralModel.endpointSub (M.subTy A σ) (M.subTm x σ) (M.subTm y σ) (ordinaryPathSub M A x y p σ)) =
 M.compSub (M.toStructuralModel.endpointSub A x y p) σ := by
 apply M.toStructuralModel.pair_ext (M.toStructuralModel.pathFamily A x)
 · rw [← M.comp_assoc, M.toStructuralModel.weaken_pathSub, M.comp_assoc]
   simp only [StructuralModel.endpointSub, M.weaken_pair]
   rw [M.toStructuralModel.section_lift, ← M.comp_assoc, M.weaken_pair]
 · apply (M.subTm_comp _ _ _).symm.trans
   apply (M.toStructuralModel.subTm_congr (M.toStructuralModel.variable_pathSub_type A x σ)
    (M.toStructuralModel.variable_pathSub A x σ) _).trans
   apply (M.variable_pair _ _ _).trans
   apply (cast_heq _ _).trans
   apply (cast_heq _ _).trans
   apply HEq.trans _ (M.subTm_comp _ _ _)
   symm
   apply M.toStructuralModel.subTm_congr
    ((M.subTy_comp _ _ _).trans ((congrArg (M.subTy _) (M.weaken_pair _ _ _)).trans (M.toStructuralModel.pathFamily_at A x y)))
   exact (M.variable_pair _ _ _).trans (cast_heq _ _)
theorem ordinaryApValue_sub (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y))
 (σ : M.Substitution Δ Γ) :
 HEq (M.subTm (ordinaryApValue M A C t x y p) σ)
 (ordinaryApValue M (M.subTy A σ) (M.subTy C σ) (ordinaryFunctionSub M A C t σ)
  (M.subTm x σ) (M.subTm y σ) (ordinaryPathSub M A x y p σ)) := by
 apply (M.toStructuralModel.subTm_congr (ordinaryApMotive_endpoint M A C t x y p).symm (cast_heq _ _) σ).trans
 apply (M.subTm_comp _ _ _).trans
 apply HEq.trans _ (cast_heq _ _).symm
 apply HEq.trans _ (M.toStructuralModel.subTm_congr (ordinaryApMotive_sub M A C t x σ)
  (ordinaryApSection_sub M A C t x σ) _)
 apply HEq.trans _ (M.subTm_comp _ _ _).symm
 rw [ordinaryEndpoint_square]
end SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
