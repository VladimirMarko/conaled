import SquareKit.Internal.PathTransport.TwoFamilyRootedNormalization
/-! The rooted contraction moves its second endpoint along the selected path.
These observations preserve the chosen path through the embedding and family casts. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ] [IsLocallyGroupoid Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀γ, IsGroupoid (F.obj γ)] [∀γ, IsLocallyGroupoid (F.obj γ)]
variable (x : Section F)
theorem rootedContraction_app_embedding (z : Total (rootedPathFamily F x)) :
 HEq ((rootedPathEmbedding F x).map ((rootedContraction F x).app z))
  ((pathContraction F).app ((rootedPathEmbedding F x).obj z)) := by
 have h := strongTrans_app_heq (rootedContraction_embedding_source F x)
  (rootedContraction_embedding_target F x)
  (strongPostcomp (rootedContraction F x) (rootedPathEmbedding F x))
  (strongPrecomp (pathContraction F) (rootedPathEmbedding F x))
  (rootedContraction_embedding F x) z
 -- Reuse checked terms without repeating dependent endpoint elaboration.
 run_tac Lean.Elab.Tactic.withMainContext do
  let d ← Lean.Meta.getLocalDeclFromUserName `h
  (← Lean.Elab.Tactic.getMainGoal).assign d.toExpr
  Lean.Elab.Tactic.replaceMainGoal []

private theorem strong_map_app_heq {A B C : Type*} [Bicategory A] [Bicategory B] [Bicategory C]
 {F G F' G' : StrictPseudofunctor A B} (K : StrictPseudofunctor B C)
 (eF : F = F') (eG : G = G')
 (α : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
 (β : Pseudofunctor.StrongTrans F'.toPseudofunctor G'.toPseudofunctor)
 (h : HEq α β) (z : A) : HEq (K.map (α.app z)) (K.map (β.app z)) := by
 cases eF; cases eG; cases eq_of_heq h; rfl
theorem rootedContraction_app_projection (z : Total (rootedPathFamily F x)) :
 HEq ((projectionHigher (rootedPathFamily F x)).map ((rootedContraction F x).app z))
  ((pathSecond F).map ((pathContraction F).app ((rootedPathEmbedding F x).obj z))) := by
 have h := strong_map_app_heq (pathSecond F)
  (rootedContraction_embedding_source F x) (rootedContraction_embedding_target F x)
  (strongPostcomp (rootedContraction F x) (rootedPathEmbedding F x))
  (strongPrecomp (pathContraction F) (rootedPathEmbedding F x))
  (rootedContraction_embedding F x) z
 have hπ := congr_arg_heq (fun H => H.map ((rootedContraction F x).app z))
   (rootedPathEmbedding_second F x)
 -- Reuse checked terms without repeating dependent endpoint elaboration.
 run_tac Lean.Elab.Tactic.withMainContext do
  let a ← Lean.Meta.getLocalDeclFromUserName `hπ
  let b ← Lean.Meta.getLocalDeclFromUserName `h
  let ta ← Lean.Meta.whnf a.type
  let tb ← Lean.Meta.whnf b.type
  let #[α, left, β, mid] := ta.getAppArgs | throwError "expected HEq"
  let #[_, _, γ, right] := tb.getAppArgs | throwError "expected HEq"
  let .const _ [level] := ta.getAppFn | throwError "expected level"
  let symm := Lean.mkAppN (Lean.mkConst ``HEq.symm [level]) #[α, β, left, mid, a.toExpr]
  (← Lean.Elab.Tactic.getMainGoal).assign
   (Lean.mkAppN (Lean.mkConst ``HEq.trans [level]) #[β, α, γ, mid, left, right, symm, b.toExpr])
  Lean.Elab.Tactic.replaceMainGoal []

theorem rootedContraction_app_projection_fiber (z : Total (rootedPathFamily F x)) :
 HEq ((projectionHigher (rootedPathFamily F x)).map ((rootedContraction F x).app z)).fiber
  ((pathSecond F).map ((pathContraction F).app ((rootedPathEmbedding F x).obj z))).fiber := by
 have a := congrArg (fun H => H.obj (((rootedRetraction F x).comp (rootedReflexivity F x)).obj z))
  (rootedPathEmbedding_second F x)
 have b := congrArg (fun H => (pathSecond F).obj (H.obj z)) (rootedContraction_embedding_source F x)
 have hx := a.symm.trans b
 have hy := (congrArg (fun H => H.obj z) (rootedPathEmbedding_second F x)).symm
 exact total_hom_fiber_heq_family (F := F) (G := F) rfl (heq_of_eq hx) (heq_of_eq hy)
  (rootedContraction_app_projection F x z)

theorem pathContraction_app_second_fiber (w : PathContext F) :
 HEq ((pathSecond F).map ((pathContraction F).app w)).fiber w.fiber.as := by
 rw [pathSecond_map_fiber]
 change HEq ((identity F ((pathFirst F).obj w)).fiber ≫ w.fiber.as) w.fiber.as
 exact eqToHom_comp_heq w.fiber.as (congrArg (fun H : F.obj w.base.base ⟶ F.obj w.base.base => H.obj w.base.fiber.1)
   (F.map_id w.base.base))
omit [IsLocallyGroupoid Γ] in
theorem rootedPathEmbedding_obj_fiber (z : Total (rootedPathFamily F x)) :
 HEq ((rootedPathEmbedding F x).obj z).fiber.as z.fiber.as := by rfl
/-- The moving endpoint component has precisely the supplied path as its fiber arrow. -/
theorem rootedContraction_app_fiber (z : Total (rootedPathFamily F x)) :
 HEq ((projectionHigher (rootedPathFamily F x)).map ((rootedContraction F x).app z)).fiber
  z.fiber.as := by
 have h1 := rootedContraction_app_projection_fiber F x z
 have h2 := pathContraction_app_second_fiber F ((rootedPathEmbedding F x).obj z)
 have h3 := rootedPathEmbedding_obj_fiber F x z
 exact HEq.trans h1 (HEq.trans h2 h3)
theorem rootedContraction_app_projection_base (z : Total (rootedPathFamily F x)) :
 HEq ((projectionHigher (rootedPathFamily F x)).map ((rootedContraction F x).app z)).base
  ((pathSecond F).map ((pathContraction F).app ((rootedPathEmbedding F x).obj z))).base := by
 have a := congrArg (fun H => H.obj (((rootedRetraction F x).comp (rootedReflexivity F x)).obj z))
  (rootedPathEmbedding_second F x)
 have b := congrArg (fun H => (pathSecond F).obj (H.obj z)) (rootedContraction_embedding_source F x)
 have hx := a.symm.trans b
 have hy := (congrArg (fun H => H.obj z) (rootedPathEmbedding_second F x)).symm
 exact total_hom_base_heq_family (F := F) (G := F) rfl (heq_of_eq hx) (heq_of_eq hy)
  (rootedContraction_app_projection F x z)
theorem rootedContraction_app_base (z : Total (rootedPathFamily F x)) :
 HEq ((projectionHigher (rootedPathFamily F x)).map ((rootedContraction F x).app z)).base
  (𝟙 z.base.base) := by
 have h := rootedContraction_app_projection_base F x z
 exact h
end SquareKit.Internal.PathTransport.TwoFamily
