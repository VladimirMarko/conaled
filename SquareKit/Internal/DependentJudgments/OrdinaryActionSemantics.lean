import SquareKit.Internal.DependentJudgments.DerivedPathSemantics
namespace SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (M : Model.{u})
variable {Γ : M.Context} (A C : M.Family Γ)
variable (t : M.Section (M.extend Γ A) (M.subTy C (M.weaken Γ A)))
def ordinaryApply (x : M.Section Γ A) : M.Section Γ C :=
 cast (congrArg (M.Section Γ) (M.toStructuralModel.weaken_section_type A x C))
  (M.subTm t (M.toStructuralModel.sectionSub A x))
def ordinaryApLeft (x : M.Section Γ A) :=
 M.subTm (M.subTm (ordinaryApply M A C t x) (M.weaken Γ A))
  (M.weaken _ (M.toStructuralModel.pathFamily A x))
def ordinaryApRight (x : M.Section Γ A) :=
 M.subTm t (M.weaken _ (M.toStructuralModel.pathFamily A x))
def ordinaryApMotive (x : M.Section Γ A) :=
 M.identity (motive M A (M.subTy C (M.weaken Γ A)) x)
  (ordinaryApLeft M A C t x) (ordinaryApRight M A C t x)
theorem ordinaryAp_type_endpoint (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y)) :
 M.subTy (motive M A (M.subTy C (M.weaken Γ A)) x)
  (M.toStructuralModel.endpointSub A x y p) = C :=
 (motive_endpoint M A _ x y p).trans (M.toStructuralModel.weaken_section_type A y C)
theorem ordinaryApLeft_endpoint (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y)) :
 HEq (M.subTm (ordinaryApLeft M A C t x) (M.toStructuralModel.endpointSub A x y p))
  (ordinaryApply M A C t x) := by
 apply (M.subTm_comp _ _ _).trans
 unfold StructuralModel.endpointSub
 rw [M.weaken_pair]
 exact M.toStructuralModel.weaken_section_term A y _
theorem ordinaryApRight_endpoint (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y)) :
 HEq (M.subTm (ordinaryApRight M A C t x) (M.toStructuralModel.endpointSub A x y p))
  (ordinaryApply M A C t y) := by
 apply (M.subTm_comp _ _ _).trans
 unfold StructuralModel.endpointSub
 rw [M.weaken_pair]
 exact (cast_heq _ _).symm
theorem ordinaryApMotive_endpoint (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y)) :
 M.subTy (ordinaryApMotive M A C t x) (M.toStructuralModel.endpointSub A x y p) =
 M.identity C (ordinaryApply M A C t x) (ordinaryApply M A C t y) := by
 rw [ordinaryApMotive, M.identity_sub]
 exact M.toStructuralModel.identity_congr (ordinaryAp_type_endpoint M A C x y p)
  (ordinaryApLeft_endpoint M A C t x y p) (ordinaryApRight_endpoint M A C t x y p)
theorem ordinaryApLeft_root (x : M.Section Γ A) :
 HEq (M.subTm (ordinaryApLeft M A C t x) (M.toStructuralModel.rootSub A x))
  (ordinaryApply M A C t x) := by
 apply (M.subTm_comp _ _ _).trans
 rw [M.toStructuralModel.weaken_root]
 exact M.toStructuralModel.weaken_section_term A x _
theorem ordinaryApRight_root (x : M.Section Γ A) :
 HEq (M.subTm (ordinaryApRight M A C t x) (M.toStructuralModel.rootSub A x))
  (ordinaryApply M A C t x) := by
 apply (M.subTm_comp _ _ _).trans
 rw [M.toStructuralModel.weaken_root]
 exact (cast_heq _ _).symm
theorem ordinaryApMotive_root (x : M.Section Γ A) :
 M.subTy (ordinaryApMotive M A C t x) (M.toStructuralModel.rootSub A x) =
 M.identity C (ordinaryApply M A C t x) (ordinaryApply M A C t x) := by
 rw [ordinaryApMotive, M.identity_sub]
 exact M.toStructuralModel.identity_congr
  ((motive_root M A _ x).trans (M.toStructuralModel.weaken_section_type A x C))
  (ordinaryApLeft_root M A C t x) (ordinaryApRight_root M A C t x)
def ordinaryApBranch (x : M.Section Γ A) :=
 cast (congrArg (M.Section Γ) (ordinaryApMotive_root M A C t x).symm)
  (M.reflexivity C (ordinaryApply M A C t x))
def ordinaryApSection (x : M.Section Γ A) :=
 M.j A x .nil (ordinaryApMotive M A C t x) (ordinaryApBranch M A C t x)
theorem ordinaryApSection_root (x : M.Section Γ A) :
 HEq (M.subTm (ordinaryApSection M A C t x) (M.toStructuralModel.rootSub A x))
  (M.reflexivity C (ordinaryApply M A C t x)) :=
 (M.j_beta A x .nil _ _).trans (cast_heq _ _)
def ordinaryApValue (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y)) :
 M.Section Γ (M.identity C (ordinaryApply M A C t x) (ordinaryApply M A C t y)) :=
 cast (congrArg (M.Section Γ) (ordinaryApMotive_endpoint M A C t x y p))
  (M.subTm (ordinaryApSection M A C t x) (M.toStructuralModel.endpointSub A x y p))
end SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
