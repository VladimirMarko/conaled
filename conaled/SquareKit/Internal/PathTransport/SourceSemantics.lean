import SquareKit.Internal.PathTransport.Derived
import SquareKit.Internal.PathTransport.DerivedSemantics
import SquareKit.Internal.PathTransport.GroupoidSoundness

/-!
# Meaning of source-derived transport

The generated source operation is compared with the primitive functor action.
Its generic J section has the specified reflexive restriction by beta, and
discrete uniqueness identifies it with canonical transport. Endpoint
instantiation then gives the pointwise formula. The interpretation theorem
connects the actual generated derivation through `interpretTm_agrees`.
-/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.SourceSemantics
open CategoryTheory Typed Typed.Authoring
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => Instance.fullModel C B
variable {Γ Δ : RawCtx} {γ δ : CtxCode.{u+1}}

theorem base_reindex_eval (x : BasePoint Γ γ) {σ : RawSub} {s : SubCode δ γ}
    (hs : SubDeriv Δ δ Γ γ σ s) :
    (x.reindex hs).code M = ⟨(x.code M).down.reindex (s M).down⟩ :=
  eq_of_heq (castCode_eval _ _ M)

theorem base_variable_eval (hΓ : CtxDeriv Γ γ) :
    (BasePoint.variable hΓ).code M = ⟨«variable» (constant C)⟩ :=
  eq_of_heq (castCode_eval _ _ M)

theorem moving_eval (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) :
    (moving hΓ x).code M = ⟨DerivedSemantics.endpoint (x.code M).down⟩ := by
  unfold moving
  rw [base_reindex_eval, base_variable_eval]
  rfl

theorem endpoint_obj (x y : BasePoint Γ γ) (p : Path x y) (g : ↥(show Grpd.{u,u} from γ M)) :
    (endpointCode (baseCode γ) x.code y.code p.code M).down.obj g =
      ⟨⟨g, (y.code M).down.obj g⟩, (p.code M).down.obj g⟩ := by
  rw [endpointCode_eval]
  rfl
end SquareKit.Internal.PathTransport.GroupoidModel.SourceSemantics

namespace SquareKit.Internal.PathTransport.GroupoidModel.SourceSemantics
open CategoryTheory Typed Typed.Authoring
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => Instance.fullModel C B
variable {Γ : RawCtx} {γ : CtxCode.{u+1}}

theorem j_motive_congr (N : Model) {Γ : N.Context} {n}
    (A : N.Family Γ) (x : N.Section Γ A)
    (T : StructuralModel.Telescope N.toStructuralModel (N.toStructuralModel.pathContext A x) n)
    {D D' : N.Family (StructuralModel.Telescope.total N.toStructuralModel T)}
    (hD : D = D')
    (d : N.Section _ (N.subTy D (N.toStructuralModel.rootTail A x T)))
    (d' : N.Section _ (N.subTy D' (N.toStructuralModel.rootTail A x T)))
    (hd : HEq d d') : HEq (N.j A x T D d) (N.j A x T D' d') := by
  cases hD
  cases eq_of_heq hd
  rfl

def transportJCode (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) (b : FiberElement x) :=
  jCode (baseCode γ) x.code (telNil (pathCode (baseCode γ) x.code))
    (fiberCode (moving hΓ x).code) (castCode (transportMotive_root hΓ x).symm b.code)

/-- The concrete contextual eliminator is determined by its primitive-fiber
reflexive branch. -/
theorem canonicalJ_transport {G : Grpd.{u,u}}
    (x : Section (constant (Γ := G) C)) (b : Section (primitiveFiber B x)) :
    (Instance.contextualJ C B (Γ := G) (constant C) ⟨x⟩ .nil
      (primitiveFiber B (DerivedSemantics.endpoint x)) ⟨b⟩).down =
      DerivedSemantics.transport B x b := by
  apply DerivedSemantics.transport_unique
  have hh := eliminateSection_beta
    (Instance.rootTailEquivalence C B (Γ := G) (constant C) x .nil)
    (primitiveFiber B (DerivedSemantics.endpoint x)) b
  apply Section.ext_discrete (A := primitiveFiber B x)
  intro g
  exact congrArg (fun s => s.obj g) hh

/-- Evaluate the source generic J, including its motive and branch annotations. -/
theorem transportJ_eval (hΓ : CtxDeriv Γ γ) (x : BasePoint Γ γ) (b : FiberElement x) :
    HEq (transportJCode hΓ x b M)
      (ULift.up.{u+1} (DerivedSemantics.transport B (x.code M).down (b.code M).down)) := by
  have hm : fiberCode (moving hΓ x).code M =
      primitiveFiber B (DerivedSemantics.endpoint (x.code M).down) := by
    change primitiveFiber B ((moving hΓ x).code M).down = _
    rw [moving_eval]
  have hj := j_motive_congr M (baseCode γ M) (x.code M)
    (telNil (pathCode (baseCode γ) x.code) M) hm
    (castCode (transportMotive_root hΓ x).symm b.code M)
    (b.code M) (castCode_eval _ _ M)
  have hc := canonicalJ_transport C B
    (G := show Grpd.{u,u} from γ M) (x.code M).down (b.code M).down
  have hu : (M).j (baseCode γ M) (x.code M)
      (telNil (pathCode (baseCode γ) x.code) M)
      (primitiveFiber B (DerivedSemantics.endpoint (x.code M).down)) (b.code M) =
      ULift.up.{u+1} (DerivedSemantics.transport B (x.code M).down (b.code M).down) := by
    apply ULift.ext
    exact hc
  exact hj.trans (heq_of_eq hu)
end SquareKit.Internal.PathTransport.GroupoidModel.SourceSemantics

namespace SquareKit.Internal.PathTransport.GroupoidModel.SourceSemantics
open CategoryTheory Typed Typed.Authoring
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => Instance.fullModel C B
variable {Γ : RawCtx} {γ : CtxCode.{u+1}}

/-- The actual derived source term is canonical transport at its endpoint substitution. -/
theorem transport_section (hΓ : CtxDeriv Γ γ) {x y : BasePoint Γ γ}
    (p : Path x y) (b : FiberElement x) :
    ((transport hΓ p b).code M).down =
      (DerivedSemantics.transport B (x.code M).down (b.code M).down).reindex
        ((M).toStructuralModel.endpointSub (baseCode γ M) (x.code M) (y.code M) (p.code M)).down := by
  have hraw := castCode_eval (transportMotive_at hΓ x y p)
    (subTmCode (transportJCode hΓ x b) (endpointCode (baseCode γ) x.code y.code p.code)) M
  have hm : fiberCode (moving hΓ x).code M =
      primitiveFiber B (DerivedSemantics.endpoint (x.code M).down) := by
    change primitiveFiber B ((moving hΓ x).code M).down = _
    rw [moving_eval]
  have hs := (M).toStructuralModel.subTm_congr hm (transportJ_eval C B hΓ x b)
    (endpointCode (baseCode γ) x.code y.code p.code M)
  have ht := hraw.trans hs
  rw [endpointCode_eval] at ht
  exact congrArg ULift.down (eq_of_heq ht)
end SquareKit.Internal.PathTransport.GroupoidModel.SourceSemantics

namespace SquareKit.Internal.PathTransport.GroupoidModel.SourceSemantics
open CategoryTheory Typed Typed.Authoring
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => Instance.fullModel C B
variable {Γ : RawCtx} {γ : CtxCode.{u+1}}

/-- Source transport acts by the given functor on the supplied path. -/
theorem transport_obj (hΓ : CtxDeriv Γ γ) {x y : BasePoint Γ γ}
    (p : Path x y) (b : FiberElement x) (g : ↥(show Grpd.{u,u} from γ M)) :
    (((transport hΓ p b).code M).down.obj g).as =
      B.map (((p.code M).down.obj g).as) (((b.code M).down.obj g).as) := by
  rw [transport_section]
  rfl

/-- The recursively interpreted generated derivation has the same functor action. -/
theorem interpret_transport_obj (hΓ : CtxDeriv Γ γ) {x y : BasePoint Γ γ}
    (p : Path x y) (b : FiberElement x) (g : ↥(show Grpd.{u,u} from γ M)) :
    ((interpretTm M (transport hΓ p b).deriv).down.obj g).as =
      B.map (((interpretTm M p.deriv).down.obj g).as)
        (((interpretTm M b.deriv).down.obj g).as) := by
  rw [interpretTm_agrees, interpretTm_agrees, interpretTm_agrees]
  exact transport_obj C B hΓ p b g
end SquareKit.Internal.PathTransport.GroupoidModel.SourceSemantics
