import SquareKit.Internal.PathTransport.GeneratedSectionLift
import SquareKit.Internal.PathTransport.Endpoints

/-! Generated term sections are actual generated simultaneous substitutions. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.Typed
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem sectionCode_lift (C : Grpd.{u,u}) (P : C ⥤ Type u)
    {γ : CtxCode.{u+1}} (b : TyCode γ) (ξ : TmCode γ b) :
    ((sectionCode b ξ) (GroupoidModel.Instance.fullModel C P)).down =
      (ξ (GroupoidModel.Instance.fullModel C P)).down.lift := by
  have ht := castCode_eval (subTyId_code b).symm ξ (GroupoidModel.Instance.fullModel C P)
  change GroupoidModel.pair _ (𝟭 _) ((castCode (subTyId_code b).symm ξ)
    (GroupoidModel.Instance.fullModel C P)).down = _
  rw [eq_of_heq ht]
  rfl

universe v w

theorem sectionCode_universeLift (C : Type u) [Groupoid.{v} C] (P : C ⥤ Type w)
    {γ : CtxCode.{max u v w + 1}} (b : TyCode γ) (ξ : TmCode γ b) :
    ((sectionCode b ξ) (GroupoidModel.Instance.universeModel C P)).down =
      (ξ (GroupoidModel.Instance.universeModel C P)).down.lift :=
  sectionCode_lift (Grpd.of (AsSmall.{w} C)) (GroupoidModel.Instance.liftedFamily C P) b ξ

end SquareKit.Internal.PathTransport.Typed
