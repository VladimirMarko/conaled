import SquareKit.Internal.PathTransport.TwoFamilyModelOrdinaryAction
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SourceContraction
variable {Γ Δ Θ : Context.{u}} {i : StrictPseudofunctor Δ Γ} (c : SourceContraction i)
variable (F : Family Γ) (s t : TwoFamily.Section F.data)
variable (d : TwoFamily.Section (reindex i (closedId F.data s t)))
variable (σ : StrictPseudofunctor Θ Γ) (G : Family Θ) (p : TwoFamily.Section G.data)
def IdentityEndpointActionFormula : Prop :=
 ∀ z, HEq (p.normalObj G.data z).fiber
  (show LocallyDiscrete _ from ⟨inv (s.normalMap F.data (c.homotopy.app (σ.obj z))).fiber ≫
   (F.data.map (c.homotopy.app (σ.obj z))).map
    (d.normalObj (reindex i (closedId F.data s t)) (c.retraction.obj (σ.obj z))).fiber.as ≫
   (t.normalMap F.data (c.homotopy.app (σ.obj z))).fiber⟩)
theorem ReindexedValueFormula.identityAction
 (h : c.ReindexedValueFormula (F.identity s t) d σ G p) :
 c.IdentityEndpointActionFormula F s t d σ G p := by
 intro z
 have hm := closedId_map_obj F.data s t (c.homotopy.app (σ.obj z))
  (d.normalObj (reindex i (closedId F.data s t)) (c.retraction.obj (σ.obj z))).fiber
 exact (h z).trans (heq_of_eq (congrArg LocallyDiscrete.mk hm))
end SourceContraction
variable (C D : Context.{u}) {Γ : Context.{u}} (A B : Family Γ)
variable (t : ULift.{u+1} (TwoFamily.Section (reindex (projectionHigher A.data) B.data)))
variable (x y : ULift.{u+1} (TwoFamily.Section A.data))
variable (p : ULift.{u+1} (TwoFamily.Section (closedId A.data x.down y.down)))
local notation "M" => fullModel C D
def OrdinaryApEndpointActionFormula : Prop :=
 (rootContraction C D A x).val.IdentityEndpointActionFormula
  (motive M A ((M).subTy B ((M).weaken Γ A)) x)
  (ordinaryApLeft M A B t x).down (ordinaryApRight M A B t x).down
  (ordinaryApBranch M A B t x).down ((M).toStructuralModel.endpointSub A x y p).down
  ((M).identity B (ordinaryApply M A B t x) (ordinaryApply M A B t y))
  (ordinaryApValue M A B t x y p).down
theorem ordinaryApValue_action : OrdinaryApEndpointActionFormula C D A B t x y p :=
 SourceContraction.ReindexedValueFormula.identityAction (rootContraction C D A x).val
  (motive M A ((M).subTy B ((M).weaken Γ A)) x) _ _ _ _ _ _
  (ordinaryApValue_objects C D A B t x y p)
end SquareKit.Internal.PathTransport.HigherInterpretation
