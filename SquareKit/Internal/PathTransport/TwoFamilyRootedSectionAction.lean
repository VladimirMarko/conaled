import SquareKit.Internal.PathTransport.TwoFamilySectionVerticalMap
import SquareKit.Internal.PathTransport.TwoFamilyModelRootComponentFormula
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Type u} [Bicategory.{u,u} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F B : Family.{u,u,u,u,u,u} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)] (x : Section F) (s : Section B)
def RootedSectionActionFormula {H K : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor) : Prop :=
 ∀ z, HEq ((((s.reindex B (projectionHigher F)).reindex (reindex (projectionHigher F) B)
   (projectionHigher (rootedPathFamily F x))).normalMap
   (reindex (projectionHigher (rootedPathFamily F x)) (reindex (projectionHigher F) B)) (η.app z)).fiber)
  (𝟙 (s.normalObj B z.base.base).fiber)
theorem rootedSection_action_of_base
 {H K : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor)
 (hs : H.comp (rootedRetraction F x) = rootedRetraction F x)
 (ht : K.comp (rootedRetraction F x) = rootedRetraction F x)
 (hb : RootedBaseFormula F x η) : RootedSectionActionFormula F B x s η := by
 intro z
 exact s.doubleReindex_normalMap_vertical B (projectionHigher F) (projectionHigher (rootedPathFamily F x))
  (η.app z) z.base.base (congrArg (fun L => L.obj z) hs) (congrArg (fun L => L.obj z) ht) (hb z)
theorem rootedSection_action : RootedSectionActionFormula F B x s (rootedContraction F x) := by
 apply rootedSection_action_of_base F B x s (rootedContraction F x)
 · rw [strictFunctor_comp_assoc, rootedReflexivity_retraction, strictFunctor_comp_id]
 · exact strictFunctor_id_comp _
 · exact rootedContraction_base F x
omit [IsLocallyGroupoid Γ] in
theorem RootedSectionActionFormula.congr
 {H K H' K' : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (eH : H = H') (eK : K = K')
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor)
 (θ : Pseudofunctor.StrongTrans H'.toPseudofunctor K'.toPseudofunctor)
 (h : HEq η θ) (hf : RootedSectionActionFormula F B x s θ) : RootedSectionActionFormula F B x s η := by
 cases eH; cases eK; cases eq_of_heq h; exact hf
end SquareKit.Internal.PathTransport.TwoFamily
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A B : Family Γ)
 (x : ULift.{u+1} (TwoFamily.Section A.data)) (s : TwoFamily.Section B.data)
theorem rootContraction_section_action :
 RootedSectionActionFormula A.data B.data x.down s (rootContraction C D A x).val.homotopy := by
 have hH := congrArg₂ StrictPseudofunctor.comp (rootContraction_retraction C D A x) (rootSub_down_eq C D A x)
 exact RootedSectionActionFormula.congr A.data B.data x.down s hH rfl
  (rootContraction C D A x).val.homotopy (rootedContraction A.data x.down)
  (rootContraction_homotopy C D A x) (rootedSection_action A.data B.data x.down s)
end SquareKit.Internal.PathTransport.HigherInterpretation
