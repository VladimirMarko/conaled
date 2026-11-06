import SquareKit.Internal.PathTransport.TwoFamilyOrdinaryRightAction
import SquareKit.Internal.PathTransport.TwoFamilyRootedComponentFormula
/-! The rooted contraction projects to the fiber inclusion of its selected path.
Normalized endpoint equations support later evaluation of section actions. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Type u} [Bicategory.{u,u} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F : Family.{u,u,u,u,u,u} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)] (x : Section F)
omit [IsLocallyGroupoid Γ] [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)] in
theorem reindexNormalObj_total (z : Total F) :
 (⟨z.base, ((x.reindex F (projectionHigher F)).normalObj (reindex (projectionHigher F) F) z).fiber⟩ : Total F) = x.lift.obj z.base :=
 (congrArg (fun a => (⟨z.base, a⟩ : Total F)) (x.reindex_normalObj F (projectionHigher F) z)).trans (x.normalObj_eq F z.base)
omit [IsLocallyGroupoid Γ] [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)] in
theorem variableNormalObj_total (z : Total F) :
 (⟨z.base, ((variableSection F).normalObj (reindex (projectionHigher F) F) z).fiber⟩ : Total F) = z :=
 congrArg (fun a => (⟨z.base, a⟩ : Total F)) (eq_of_heq ((variableSection F).normalObj_fiber_heq _ z))
theorem pathContraction_second_vertical (w : PathContext F) :
 HEq ((pathSecond F).map ((pathContraction F).app w))
 ((fiberInclusion F w.base.base).map w.fiber.as) := by
 apply total_hom_hext F rfl rfl
 · rfl
 · rw [pathSecond_map_fiber]
   rfl
theorem rootedContraction_vertical (z : Total (rootedPathFamily F x)) :
 HEq ((projectionHigher (rootedPathFamily F x)).map ((rootedContraction F x).app z))
 ((fiberInclusion F z.base.base).map z.fiber.as) := by
 have h1 := rootedContraction_app_projection F x z
 have h2 := pathContraction_second_vertical F ((rootedPathEmbedding F x).obj z)
 exact h1.trans h2
def RootedVerticalFormula {H K : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor) : Prop :=
 ∀ z, HEq ((projectionHigher (rootedPathFamily F x)).map (η.app z))
  ((fiberInclusion F z.base.base).map z.fiber.as)
omit [IsLocallyGroupoid Γ] in
theorem RootedVerticalFormula.congr
 {H K H' K' : StrictPseudofunctor (Total (rootedPathFamily F x)) (Total (rootedPathFamily F x))}
 (eH : H = H') (eK : K = K')
 (η : Pseudofunctor.StrongTrans H.toPseudofunctor K.toPseudofunctor)
 (θ : Pseudofunctor.StrongTrans H'.toPseudofunctor K'.toPseudofunctor)
 (h : HEq η θ) (hf : RootedVerticalFormula F x θ) : RootedVerticalFormula F x η := by
 cases eH; cases eK; cases eq_of_heq h; exact hf
end SquareKit.Internal.PathTransport.TwoFamily
