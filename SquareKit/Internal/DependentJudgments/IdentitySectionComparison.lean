import SquareKit.Internal.DependentJudgments.PathFamilyConjugationSemantics

/-! Sections over an identity singleton with the same selected root admit a typed comparison. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u
variable (M : Model.{u}) {Γ : M.Context} (A : M.Family Γ) (x : M.Section Γ A)
  (C : M.Family (M.toStructuralModel.pathContext A x))
  (s t : M.Section (M.toStructuralModel.pathContext A x) C)
  (d : M.Section Γ (M.subTy C (M.toStructuralModel.rootSub A x)))
  (hs : HEq (M.subTm s (M.toStructuralModel.rootSub A x)) d)
  (ht : HEq (M.subTm t (M.toStructuralModel.rootSub A x)) d)

include hs ht in
theorem sectionComparison_rootFamily :
    M.subTy (M.identity C s t) (M.toStructuralModel.rootSub A x) =
      M.identity (M.subTy C (M.toStructuralModel.rootSub A x)) d d :=
  (M.identity_sub C s t (M.toStructuralModel.rootSub A x)).trans
    (M.toStructuralModel.identity_congr rfl hs ht)

def sectionComparison :
    M.Section (M.toStructuralModel.pathContext A x) (M.identity C s t) :=
  M.j A x .nil (M.identity C s t)
    (cast (congrArg (M.Section Γ) (sectionComparison_rootFamily M A x C s t d hs ht).symm)
      (M.reflexivity (M.subTy C (M.toStructuralModel.rootSub A x)) d))

end SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
