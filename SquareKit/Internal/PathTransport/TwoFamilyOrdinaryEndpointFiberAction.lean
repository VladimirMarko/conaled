import SquareKit.Internal.PathTransport.TwoFamilyOrdinaryRightAction
/-! A section restricted to an identity fiber acts on the exact higher arrow
retained by a rooted endpoint object. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ : Context.{u}} (A : Family Γ) (x y : TwoFamily.Section A.data)
local notation "I" => A.identity x y
private theorem inclusion_action_heq
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 {γ δ : Γ} {a b : (I).data.obj δ} {c d : (I).data.obj γ}
 (h : a ⟶ b) (k : c ⟶ d) (e : δ = γ) (ha : HEq a c) (hb : HEq b d) (hk : HEq h k) :
 HEq (s.lift.map ((fiberInclusion (I).data δ).map h)).fiber
 (s.lift.map ((fiberInclusion (I).data γ).map k)).fiber := by
 cases e
 cases eq_of_heq ha
 cases eq_of_heq hb
 cases eq_of_heq hk
 rfl
private theorem ld_as_heq {X Y : Type u} {a : LocallyDiscrete X} {b : LocallyDiscrete Y}
 (e : X = Y) (h : HEq a b) : HEq a.as b.as := by
 cases e
 cases eq_of_heq h
 rfl
theorem rooted_identity_fiber_action
 (p q : TwoFamily.Section (I).data)
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 (γ : Γ) (z : Total (rootedPathFamily (I).data p))
 (h : (p.normalObj (I).data γ).fiber ⟶ (q.normalObj (I).data γ).fiber)
 (hz : z.base = q.normalObj (I).data γ)
 (hh : HEq z.fiber (show LocallyDiscrete _ from ⟨h⟩)) :
 HEq (s.lift.map ((fiberInclusion (I).data z.base.base).map z.fiber.as)).fiber
 (Discrete.mk ((identityFiberFunctor A x y γ s).map h.as)) := by
 have hb : z.base.base = γ := congrArg Total.base hz
 have ha := p.reindex_normalObj (I).data (projectionHigher (I).data) z.base
 have ht : ((variableSection (I).data).normalObj (reindex (projectionHigher (I).data) (I).data) z.base).fiber = z.base.fiber := rfl
 have htarget : HEq z.base.fiber (q.normalObj (I).data γ).fiber := congr_arg_heq (fun w : Total (I).data => w.fiber) hz
 have hsource : HEq ((p.reindex (I).data (projectionHigher (I).data)).normalObj (reindex (projectionHigher (I).data) (I).data) z.base).fiber (p.normalObj (I).data γ).fiber := by
   exact (heq_of_eq ha).trans (congr_arg_heq (fun δ => (p.normalObj (I).data δ).fiber) hb)
 have harrow : HEq z.fiber.as h := by
   apply ld_as_heq _ hh
   cases hb
   exact congrArg₂ (fun a b : (I).data.obj z.base.base => a ⟶ b) (eq_of_heq hsource) (ht.trans (eq_of_heq htarget))
 have hm := inclusion_action_heq A x y s z.fiber.as h hb hsource ((heq_of_eq ht).trans htarget) harrow
 have hf := identityFiberFunctor_map_fiber A x y γ s h.as
 -- Assemble transitivity without expanding the identity-family instances.
 -- The resulting proof term is checked by the kernel.
 run_tac Lean.Elab.Tactic.withMainContext do
   let hm := (← Lean.Meta.getLocalDeclFromUserName `hm).toExpr
   let hf := (← Lean.Meta.getLocalDeclFromUserName `hf).toExpr
   let tm ← Lean.instantiateMVars (← Lean.Meta.inferType hm)
   let tf ← Lean.instantiateMVars (← Lean.Meta.inferType hf)
   let am := tm.getAppArgs
   let af := tf.getAppArgs
   let l := tm.getAppFn.constLevels!
   let proof := Lean.mkAppN (Lean.mkConst ``HEq.trans l) #[am[0]!, am[2]!, af[2]!, am[1]!, am[3]!, af[3]!, hm, hf]
   (← Lean.Elab.Tactic.getMainGoal).assign proof
   Lean.Elab.Tactic.replaceMainGoal []
end SquareKit.Internal.PathTransport.HigherInterpretation
