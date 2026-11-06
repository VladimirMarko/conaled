import SquareKit.Internal.DependentJudgments.IdentitySectionComparison
import SquareKit.Internal.DependentJudgments.OrdinaryActionSemantics

/-! A typed comparison with ordinary action follows from its selected reflexive branch. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u
variable (M : Model.{u}) {Γ : M.Context} (A C : M.Family Γ)
  (t : M.Section (M.extend Γ A) (M.subTy C (M.weaken Γ A))) (x : M.Section Γ A)
  (q : M.Section (M.toStructuralModel.pathContext A x) (ordinaryApMotive M A C t x))
  (hq : HEq (M.subTm q (M.toStructuralModel.rootSub A x))
    (M.reflexivity C (ordinaryApply M A C t x)))

def ordinaryApComparison : M.Section (M.toStructuralModel.pathContext A x)
    (M.identity (ordinaryApMotive M A C t x) (ordinaryApSection M A C t x) q) :=
  sectionComparison M A x (ordinaryApMotive M A C t x) (ordinaryApSection M A C t x) q
    (ordinaryApBranch M A C t x)
    ((ordinaryApSection_root M A C t x).trans (cast_heq _ _).symm)
    (hq.trans (cast_heq _ _).symm)

end SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
