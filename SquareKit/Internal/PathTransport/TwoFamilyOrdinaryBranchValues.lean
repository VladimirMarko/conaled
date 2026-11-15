import SquareKit.Internal.PathTransport.TwoFamilyModelOrdinaryAction
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Context.{u}}
def SectionIdentityValues (E F : Family Γ) (s : ULift.{u+1} (TwoFamily.Section E.data))
 (t : ULift.{u+1} (TwoFamily.Section F.data)) : Prop :=
 ∀ γ, HEq (sectionValue E s γ)
  (show LocallyDiscrete (sectionValue F t γ ⟶ sectionValue F t γ) from ⟨𝟙 _⟩)
theorem castReflexivity_identityValues (E F : Family Γ)
 (t : ULift.{u+1} (TwoFamily.Section F.data)) (e : E = F.identity t.down t.down) :
 SectionIdentityValues E F
  (cast (congrArg (fun H => ULift.{u+1} (TwoFamily.Section H.data)) e.symm)
   (ULift.up (closedReflexivity F.data t.down))) t := by
 intro γ
 exact (sectionValue_cast e.symm ⟨closedReflexivity F.data t.down⟩ γ).trans
  (heq_of_eq (closedReflexivity_normalObj F.data t.down γ))
variable (C D : Context.{u}) (A B : Family Γ)
variable (t : ULift.{u+1} (TwoFamily.Section (reindex (projectionHigher A.data) B.data)))
variable (x : ULift.{u+1} (TwoFamily.Section A.data))
local notation "M" => fullModel C D
theorem ordinaryApBranch_identity :
 SectionIdentityValues ((M).subTy (ordinaryApMotive M A B t x) ((M).toStructuralModel.rootSub A x)) B
  (ordinaryApBranch M A B t x) (ordinaryApply M A B t x) :=
 castReflexivity_identityValues _ _ _ (ordinaryApMotive_root M A B t x)
end SquareKit.Internal.PathTransport.HigherInterpretation
