import SquareKit.Internal.DependentJudgments.DerivedPathSemantics
namespace SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open GuardedTheory PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (M : PathTransport.Typed.Model.{u})
def apdBranchValue {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
 (x : M.Section Γ A) (t : M.Section (M.extend Γ A) B) :=
 cast (congrArg (M.Section Γ) (apdMotive_root M A B x t).symm)
  (M.reflexivity _ (M.subTm t (M.toStructuralModel.sectionSub A x)))
def apdSectionValue {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
 (x : M.Section Γ A) (t : M.Section (M.extend Γ A) B) :=
 M.j A x .nil (apdMotiveValue M A B x t) (apdBranchValue M A B x t)
theorem apdValue_section {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
 (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y))
 (t : M.Section (M.extend Γ A) B) :
 apdValue M A B x y p t =
 cast (congrArg (M.Section Γ) (apdMotive_endpoint M A B x y p t))
  (M.subTm (apdSectionValue M A B x t) (M.toStructuralModel.endpointSub A x y p)) := rfl
theorem apdSectionValue_root {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
 (x : M.Section Γ A) (t : M.Section (M.extend Γ A) B) :
 HEq (M.subTm (apdSectionValue M A B x t) (M.toStructuralModel.rootSub A x))
  (M.reflexivity _ (M.subTm t (M.toStructuralModel.sectionSub A x))) :=
 (M.j_beta A x .nil _ _).trans (cast_heq _ _)
end SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
