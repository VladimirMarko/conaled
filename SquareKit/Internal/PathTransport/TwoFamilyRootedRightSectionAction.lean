import SquareKit.Internal.PathTransport.TwoFamilyOrdinaryRightSource
import SquareKit.Internal.PathTransport.TwoFamilyRootedComponentFormula
import SquareKit.Internal.PathTransport.TwoFamilyModelRootComponent
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Type u} [Bicategory.{u,u} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F : Family.{u,u,u,u,u,u} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)] (x : Section F)
variable (s : Section (TwoFamily.reindex (projectionHigher F) F))
def RootedRightSectionFormula {H K : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor) : Prop :=
 ∀ z, HEq ((s.reindex _ (projectionHigher (rootedPathFamily F x))).normalMap _ (η.app z)).fiber
  (s.lift.map ((fiberInclusion F z.base.base).map z.fiber.as)).fiber
def RootedRightSourceEndpoint (H : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))) : Prop :=
 H.comp (projectionHigher (rootedPathFamily F x)) = (rootedRetraction F x).comp x.lift
def RootedRightTargetEndpoint (K : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))) : Prop :=
 ∀ z, (projectionHigher (rootedPathFamily F x)).obj (K.obj z) =
 (fiberInclusion F z.base.base).obj ((variableSection F).normalObj (reindex (projectionHigher F) F) z.base).fiber
omit [IsLocallyGroupoid Γ] in
theorem rootedRightSection_of_vertical
 {H K : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor)
 (hs : RootedRightSourceEndpoint F x H) (ht : RootedRightTargetEndpoint F x K)
 (hv : RootedVerticalFormula F x η) : RootedRightSectionFormula F x s η := by
 intro z
 have hs1 := congrArg (fun K => K.obj z) hs
 have hs2 := (reindexNormalObj_total F x z.base).symm
 have hs3 := hs1.trans hs2
 exact s.reindex_normalMap_heq _ (projectionHigher (rootedPathFamily F x)) (η.app z)
  ((fiberInclusion F z.base.base).map z.fiber.as) hs3 (ht z) (hv z)
omit [IsLocallyGroupoid Γ] in
theorem rootedRight_source_endpoint : RootedRightSourceEndpoint F x
 ((rootedRetraction F x).comp (rootedReflexivity F x)) := by
 unfold RootedRightSourceEndpoint
 rw [strictFunctor_comp_assoc, rootedReflexivity_projection]
omit [IsLocallyGroupoid Γ] in
theorem rootedRight_target_endpoint : RootedRightTargetEndpoint F x (StrictPseudofunctor.id _) := by
 intro z
 exact (variableNormalObj_total F z.base).symm
theorem rootedRightSection_action : RootedRightSectionFormula F x s (rootedContraction F x) :=
 rootedRightSection_of_vertical F x s (rootedContraction F x)
  (rootedRight_source_endpoint F x) (rootedRight_target_endpoint F x) (rootedContraction_vertical F x)
omit [IsLocallyGroupoid Γ] in
theorem RootedRightSectionFormula.congr
 {H K H' K' : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (eH : H = H') (eK : K = K')
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor)
 (θ : Pseudofunctor.StrongTrans H'.toPseudofunctor K'.toPseudofunctor)
 (h : HEq η θ) (hf : RootedRightSectionFormula F x s θ) : RootedRightSectionFormula F x s η := by
 cases eH; cases eK; cases eq_of_heq h; exact hf
end SquareKit.Internal.PathTransport.TwoFamily
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) {Γ : Context.{u}} (A : Family Γ)
 (x : ULift.{u+1} (TwoFamily.Section A.data))
 (s : TwoFamily.Section (reindex (projectionHigher A.data) A.data))
theorem rootContraction_right_section_action :
 RootedRightSectionFormula A.data x.down s (rootContraction C D A x).val.homotopy := by
 have hH := congrArg₂ StrictPseudofunctor.comp (rootContraction_retraction C D A x) (rootSub_down_eq C D A x)
 exact RootedRightSectionFormula.congr A.data x.down s hH rfl
  (rootContraction C D A x).val.homotopy (rootedContraction A.data x.down)
  (rootContraction_homotopy C D A x) (rootedRightSection_action A.data x.down s)
end SquareKit.Internal.PathTransport.HigherInterpretation
