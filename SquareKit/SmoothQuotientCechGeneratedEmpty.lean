import SquareKit.SmoothQuotientCechGeneratedCone
import SquareKit.Internal.PathTransport.CechMatchingContractible

/-! The actual empty-context matching evaluation is an equivalence. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

instance matchingEvaluation_empty_equivalence :
    (matchingEvaluation a A Typed.CtxDeriv.empty).IsEquivalence := by
  apply CechMatching.restriction_equivalence_of_contractible
    (matchingEvaluation a A Typed.CtxDeriv.empty)
    (show (show Grpd.{1,1} from Typed.emptyCode (model a A)) from Discrete.mk PUnit.unit)
  · intro x y
    change Discrete PUnit at x y
    change x ⟶ y
    exact eqToHom (Subsingleton.elim x y)
  · intro x y
    change Discrete PUnit at x y
    change Subsingleton (x ⟶ y)
    infer_instance
  · intro x y
    change Discrete PUnit at x y
    change x ⟶ y
    exact eqToHom (Subsingleton.elim x y)
  · intro x y
    change Discrete PUnit at x y
    change Subsingleton (x ⟶ y)
    infer_instance
  · intro x y
    change Discrete PUnit at x y
    change Subsingleton (x ⟶ y)
    infer_instance

def emptyEvaluationEquivalence :
    (show Grpd.{1,1} from Typed.emptyCode (model a A)) ≌
      SmoothQuotientGeneratedMatching.Datum a Typed.CtxDeriv.empty A :=
  (matchingEvaluation a A Typed.CtxDeriv.empty).asEquivalence

end SquareKit.SmoothQuotientCechLocal
