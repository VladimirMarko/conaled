import SquareKit.Internal.PathTransport.TwoFamilyModelApdComparison
import SquareKit.Internal.PathTransport.TwoFamilySectionValues
import SquareKit.Internal.PathTransport.TwoFamilyReflexivityObjects
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ Δ : Context.{u}}
theorem sectionValue_heq {A B : Family Γ} (e : A = B)
 (s : ULift.{u+1} (TwoFamily.Section A.data)) (t : ULift.{u+1} (TwoFamily.Section B.data))
 (h : HEq s t) (γ : Γ) : HEq (sectionValue A s γ) (sectionValue B t γ) := by
 cases e
 cases eq_of_heq h
 rfl
def SectionRootValues (E : Family Γ) (s : ULift.{u+1} (TwoFamily.Section E.data))
 (σ : StrictPseudofunctor Δ Γ) (F : Family Δ) (t : ULift.{u+1} (TwoFamily.Section F.data)) : Prop :=
 ∀ δ, HEq (sectionValue E s (σ.obj δ)) (sectionValue F t δ)
theorem sectionRootValues_of_beta (E : Family Γ) (s : ULift.{u+1} (TwoFamily.Section E.data))
 (σ : StrictPseudofunctor Δ Γ) (F : Family Δ) (t : ULift.{u+1} (TwoFamily.Section F.data))
 (e : E.reindex σ = F) (h : HEq (ULift.up (s.down.reindex E.data σ) : ULift.{u+1} _) t) :
 SectionRootValues E s σ F t := by
 intro δ
 exact (heq_of_eq (sectionValue_reindex E s σ δ).symm).trans
  (sectionValue_heq e ⟨s.down.reindex E.data σ⟩ t h δ)
def SectionRootIdentity (E : Family Γ) (s : ULift.{u+1} (TwoFamily.Section E.data))
 (σ : StrictPseudofunctor Δ Γ) (F : Family Δ) (t : ULift.{u+1} (TwoFamily.Section F.data)) : Prop :=
 ∀ δ, HEq (sectionValue E s (σ.obj δ))
  (show LocallyDiscrete (sectionValue F t δ ⟶ sectionValue F t δ) from ⟨𝟙 _⟩)
theorem sectionRootIdentity_of_values (E : Family Γ) (s : ULift.{u+1} (TwoFamily.Section E.data))
 (σ : StrictPseudofunctor Δ Γ) (F : Family Δ) (t : ULift.{u+1} (TwoFamily.Section F.data))
 (h : SectionRootValues E s σ (F.identity t.down t.down) ⟨closedReflexivity F.data t.down⟩) :
 SectionRootIdentity E s σ F t := by
 intro δ
 exact (h δ).trans (heq_of_eq (closedReflexivity_normalObj F.data t.down δ))
variable (C D : Context.{u}) (A : Family Γ) (B : Family A.total)
variable (x : ULift.{u+1} (TwoFamily.Section A.data)) (t : ULift.{u+1} (TwoFamily.Section B.data))
local notation "M" => fullModel C D
theorem apdSection_root_values :
 SectionRootValues (apdMotiveValue M A B x t) (apdSectionValue M A B x t)
  ((M).toStructuralModel.rootSub A x).down
  ((M).identity ((M).subTy B ((M).toStructuralModel.sectionSub A x))
   ((M).subTm t ((M).toStructuralModel.sectionSub A x)) ((M).subTm t ((M).toStructuralModel.sectionSub A x)))
  ((M).reflexivity _ ((M).subTm t ((M).toStructuralModel.sectionSub A x))) :=
 sectionRootValues_of_beta _ _ _ _ _ (apdMotive_root M A B x t) (apdSectionValue_root M A B x t)
theorem apdSection_root_identity :
 SectionRootIdentity (apdMotiveValue M A B x t) (apdSectionValue M A B x t)
  ((M).toStructuralModel.rootSub A x).down
  ((M).subTy B ((M).toStructuralModel.sectionSub A x))
  ((M).subTm t ((M).toStructuralModel.sectionSub A x)) :=
 sectionRootIdentity_of_values _ _ _ _ _ (apdSection_root_values C D A B x t)
end SquareKit.Internal.PathTransport.HigherInterpretation
