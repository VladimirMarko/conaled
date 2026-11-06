import SquareKit.Internal.PathTransport.TwoFamilyModelRootComponentFormula
/-! A family pulled back from the base has identity action along the rooted contraction. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Type u} [Bicategory.{u,u} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F B : Family.{u,u,u,u,u,u} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)] (x : Section F)
def RootedFamilyActionFormula {H K : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor) : Prop :=
 ∀ z, HEq ((reindex (projectionHigher (rootedPathFamily F x)) (reindex (projectionHigher F) B)).map (η.app z))
  (StrictPseudofunctor.id (B.obj z.base.base))
omit [Strict Γ] [IsLocallyGroupoid Γ] in
private theorem map_heq_id {a b γ : Γ} (ha : a = γ) (hb : b = γ)
 (f : a ⟶ b) (hf : HEq f (𝟙 γ)) : HEq (B.map f) (StrictPseudofunctor.id (B.obj γ)) := by
 cases ha; cases hb; cases eq_of_heq hf
 exact heq_of_eq (B.map_id _)
omit [IsLocallyGroupoid Γ] in
theorem rootedFamily_action_of_base
 {H K : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor)
 (hs : H.comp (rootedRetraction F x) = rootedRetraction F x)
 (ht : K.comp (rootedRetraction F x) = rootedRetraction F x)
 (hb : RootedBaseFormula F x η) : RootedFamilyActionFormula F B x η := by
 intro z
 exact map_heq_id B (congrArg (fun L => L.obj z) hs) (congrArg (fun L => L.obj z) ht)
  _ (hb z)
theorem rootedFamily_action : RootedFamilyActionFormula F B x (rootedContraction F x) := by
 apply rootedFamily_action_of_base F B x (rootedContraction F x)
 · rw [strictFunctor_comp_assoc, rootedReflexivity_retraction, strictFunctor_comp_id]
 · exact strictFunctor_id_comp _
 · exact rootedContraction_base F x
omit [IsLocallyGroupoid Γ] in
theorem RootedFamilyActionFormula.congr
 {H K H' K' : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (eH : H = H') (eK : K = K')
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor)
 (θ : Pseudofunctor.StrongTrans H'.toPseudofunctor K'.toPseudofunctor)
 (h : HEq η θ) (hf : RootedFamilyActionFormula F B x θ) : RootedFamilyActionFormula F B x η := by
 cases eH; cases eK; cases eq_of_heq h; exact hf
end SquareKit.Internal.PathTransport.TwoFamily
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A B : Family Γ)
 (x : ULift.{u+1} (TwoFamily.Section A.data))
theorem rootContraction_family_action :
 RootedFamilyActionFormula A.data B.data x.down (rootContraction C D A x).val.homotopy := by
 have hH := congrArg₂ StrictPseudofunctor.comp (rootContraction_retraction C D A x) (rootSub_down_eq C D A x)
 exact RootedFamilyActionFormula.congr A.data B.data x.down hH rfl
  (rootContraction C D A x).val.homotopy (rootedContraction A.data x.down)
  (rootContraction_homotopy C D A x) (rootedFamily_action A.data B.data x.down)
end SquareKit.Internal.PathTransport.HigherInterpretation
