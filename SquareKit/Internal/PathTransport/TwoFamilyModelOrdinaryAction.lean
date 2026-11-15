import SquareKit.Internal.DependentJudgments.OrdinaryActionSemantics
import SquareKit.Internal.PathTransport.TwoFamilyModelApdAction
import SquareKit.Internal.PathTransport.TwoFamilyModelApdRoot
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A B : Family Γ)
variable (t : ULift.{u+1} (TwoFamily.Section (reindex (projectionHigher A.data) B.data)))
variable (x y : ULift.{u+1} (TwoFamily.Section A.data))
variable (p : ULift.{u+1} (TwoFamily.Section (closedId A.data x.down y.down)))
local notation "M" => fullModel C D
theorem ordinaryApSection_objects :
 JValueFormula C D A x (ordinaryApMotive M A B t x)
  (ordinaryApBranch M A B t x) (ordinaryApSection M A B t x) :=
 j_value_objects C D A x (ordinaryApMotive M A B t x) (ordinaryApBranch M A B t x)
def OrdinaryApActionFormula : Prop :=
 IdentityActionFormula ((M).toStructuralModel.rootSub A x).down
  (rootContraction C D A x).val.retraction (rootContraction C D A x).val.homotopy
  (motive M A ((M).subTy B ((M).weaken Γ A)) x).data
  (ordinaryApLeft M A B t x).down (ordinaryApRight M A B t x).down
  (ordinaryApBranch M A B t x).down (ordinaryApSection M A B t x).down
theorem ordinaryApSection_action : OrdinaryApActionFormula C D A B t x :=
 SourceContraction.ValueFormula.identityAction (rootContraction C D A x).val
  (motive M A ((M).subTy B ((M).weaken Γ A)) x) _ _ _ _
  (ordinaryApSection_objects C D A B t x)
theorem ordinaryApSection_root_identity :
 SectionRootIdentity (ordinaryApMotive M A B t x) (ordinaryApSection M A B t x)
  ((M).toStructuralModel.rootSub A x).down B (ordinaryApply M A B t x) :=
 sectionRootIdentity_of_values _ _ _ _ _
  (sectionRootValues_of_beta _ _ _ _ _ (ordinaryApMotive_root M A B t x)
   (ordinaryApSection_root M A B t x))
theorem ordinaryApValue_objects :
 JReindexedValueFormula C D A x (ordinaryApMotive M A B t x)
  (ordinaryApBranch M A B t x) ((M).toStructuralModel.endpointSub A x y p)
  ((M).identity B (ordinaryApply M A B t x) (ordinaryApply M A B t y))
  (ordinaryApValue M A B t x y p) :=
 JValueFormula.reindex_cast C D A x (ordinaryApMotive M A B t x)
  (ordinaryApBranch M A B t x) (ordinaryApSection M A B t x)
  (ordinaryApSection_objects C D A B t x) ((M).toStructuralModel.endpointSub A x y p)
  _ (ordinaryApMotive_endpoint M A B t x y p)
end SquareKit.Internal.PathTransport.HigherInterpretation
