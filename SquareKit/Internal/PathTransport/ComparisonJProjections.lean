import SquareKit.Internal.PathTransport.ComparisonTelescope

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory ContextualElimination
universe u

theorem ContextualElimination.NormalizedEquivalence.changeFunctor_eq {D C : Cat.{u,u}}
    (e : NormalizedEquivalence D C) (F : D ⥤ C) (h : e.equiv.functor = F) :
    e.changeFunctor F h = e := by
  subst F
  cases e
  simp [NormalizedEquivalence.changeFunctor, Equivalence.changeFunctor_refl]

private theorem telescopeEquivalence_congr (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
    {Γ Δ : Grpd.{u,u}} {n} (T : Typed.StructuralModel.Telescope (Instance.structuralModel C B) Γ n)
    {e f : NormalizedEquivalence (Cat.of Δ) (Cat.of Γ)} (h : e = f) :
    HEq (Instance.telescopeEquivalence C B T e) (Instance.telescopeEquivalence C B T f) := by
  cases h
  rfl

private theorem eliminateSection_heq {C D C' D' : Grpd.{u,u}}
    (hC : C = C') (hD : D = D')
    {e : NormalizedEquivalence (Cat.of D) (Cat.of C)}
    {e' : NormalizedEquivalence (Cat.of D') (Cat.of C')} (he : HEq e e')
    {A : C ⥤ Grpd.{u,u}} {A' : C' ⥤ Grpd.{u,u}} (hA : HEq A A')
    {d : Section (e.equiv.functor ⋙ A)} {d' : Section (e'.equiv.functor ⋙ A')}
    (hd : HEq d d') : HEq (eliminateSection e A d) (eliminateSection e' A' d') := by
  cases hC; cases hD; cases eq_of_heq he; cases eq_of_heq hA; cases eq_of_heq hd; rfl

private theorem section_down_heq {C D : Grpd.{u,u}} (hC : C = D)
    {A : C ⥤ Grpd.{u,u}} {B : D ⥤ Grpd.{u,u}} (hA : HEq A B)
    {a : ULift.{u+1} (Section A)} {b : ULift.{u+1} (Section B)}
    (h : HEq a b) : HEq a.down b.down := by
  cases hC; cases eq_of_heq hA; cases eq_of_heq h; rfl

private theorem up_heq {α β : Type u} {a : α} {b : β} (h : HEq a b) :
    HEq (ULift.up.{u+1} a) (ULift.up.{u+1} b) := by cases h; rfl

namespace Comparison
open Typed Typed.StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (S : Signature.{u})
local notation "M" => structuralModel S

/-- The left contraction is the one already used by the direct model. -/
theorem telescope_left {Γ Δ : Context.{u}} {n}
    (T : Telescope M Γ n) (e : Contraction Δ Γ) :
    HEq (telescopeContraction S T e).left
      (Instance.telescopeEquivalence S.base.left S.leftFiber ((leftProjection S).telescope T) e.left) :=
  match T with
  | .nil => HEq.rfl
  | .cons A tail => by
    have he : (extendContraction S e A).left = e.left.extend (A.left ⋙ Grpd.forgetToCat) :=
      NormalizedEquivalence.changeFunctor_eq _ _ _
    change HEq (telescopeContraction S tail (extendContraction S e A)).left
      (Instance.telescopeEquivalence S.base.left S.leftFiber
        (Δ := (A.reindex e.forward).extend.left) ((leftProjection S).telescope tail)
        (e.left.extend (A.left ⋙ Grpd.forgetToCat)))
    exact (telescope_left tail (extendContraction S e A)).trans
      (telescopeEquivalence_congr S.base.left S.leftFiber
        (Δ := (A.reindex e.forward).extend.left) _ he)

termination_by sizeOf T

/-- The right contraction is the one already used by the direct model. -/
theorem telescope_right {Γ Δ : Context.{u}} {n}
    (T : Telescope M Γ n) (e : Contraction Δ Γ) :
    HEq (telescopeContraction S T e).right
      (Instance.telescopeEquivalence S.base.right S.rightFiber ((rightProjection S).telescope T) e.right) :=
  match T with
  | .nil => HEq.rfl
  | .cons A tail => by
    have he : (extendContraction S e A).right = e.right.extend (A.right ⋙ Grpd.forgetToCat) :=
      NormalizedEquivalence.changeFunctor_eq _ _ _
    change HEq (telescopeContraction S tail (extendContraction S e A)).right
      (Instance.telescopeEquivalence S.base.right S.rightFiber
        (Δ := (A.reindex e.forward).extend.right) ((rightProjection S).telescope tail)
        (e.right.extend (A.right ⋙ Grpd.forgetToCat)))
    exact (telescope_right tail (extendContraction S e A)).trans
      (telescopeEquivalence_congr S.base.right S.rightFiber
        (Δ := (A.reindex e.forward).extend.right) _ he)

termination_by sizeOf T

theorem rootTail_left {Γ : Context.{u}} {n} (A : Family Γ) (x : Section A)
    (T : Telescope M (StructuralModel.pathContext M A x) n) :
    HEq (rootTail S A x T).left
      (Instance.rootTailEquivalence S.base.left S.leftFiber A.left x.left
        ((leftProjection S).pathTelescope A x T)) := by
  have hr : (root S A x).left = Instance.rootEquivalence S.base.left S.leftFiber A.left x.left :=
    NormalizedEquivalence.changeFunctor_eq _ _ _
  apply (heq_of_eq (NormalizedEquivalence.changeFunctor_eq _ _ _)).trans
  apply (telescope_left S T (root S A x)).trans
  apply (telescopeEquivalence_congr S.base.left S.leftFiber
    (Δ := Γ.left) _ hr).trans
  exact (heq_of_eq (NormalizedEquivalence.changeFunctor_eq _ _ _)).symm

theorem rootTail_right {Γ : Context.{u}} {n} (A : Family Γ) (x : Section A)
    (T : Telescope M (StructuralModel.pathContext M A x) n) :
    HEq (rootTail S A x T).right
      (Instance.rootTailEquivalence S.base.right S.rightFiber A.right x.right
        ((rightProjection S).pathTelescope A x T)) := by
  have hr : (root S A x).right = Instance.rootEquivalence S.base.right S.rightFiber A.right x.right :=
    NormalizedEquivalence.changeFunctor_eq _ _ _
  apply (heq_of_eq (NormalizedEquivalence.changeFunctor_eq _ _ _)).trans
  apply (telescope_right S T (root S A x)).trans
  apply (telescopeEquivalence_congr S.base.right S.rightFiber
    (Δ := Γ.right) _ hr).trans
  exact (heq_of_eq (NormalizedEquivalence.changeFunctor_eq _ _ _)).symm


/-- Contextual elimination projects to the existing direct interpretation,
with its constructed telescope, motive and branch conversions. -/
theorem contextualJ_left {Γ : Context.{u}} {n} (A : Family Γ) (x : Section A)
    (T : Telescope M (StructuralModel.pathContext M A x) n)
    (D : Family (Telescope.total M T))
    (d : Section (D.reindex (StructuralModel.rootTail M A x T))) :
    HEq ((leftProjection S).mapTm (contextualJ S A x T D d))
      (Instance.contextualJ S.base.left S.leftFiber A.left ⟨x.left⟩
        ((leftProjection S).pathTelescope A x T) ((leftProjection S).jMotive A x T D)
        ((leftProjection S).jBranch A x T D d)) := by
  apply up_heq
  exact eliminateSection_heq
    ((leftProjection S).pathTelescope_total A x T)
    ((leftProjection S).rootTelescope_total A x T)
    (rootTail_left S A x T) (cast_heq _ _).symm
    (section_down_heq ((leftProjection S).rootTelescope_total A x T)
      ((leftProjection S).jBranch_type A x T D)
      ((leftProjection S).jBranch_heq A x T D d).symm)


/-- Contextual elimination projects to the existing direct interpretation,
with its constructed telescope, motive and branch conversions. -/
theorem contextualJ_right {Γ : Context.{u}} {n} (A : Family Γ) (x : Section A)
    (T : Telescope M (StructuralModel.pathContext M A x) n)
    (D : Family (Telescope.total M T))
    (d : Section (D.reindex (StructuralModel.rootTail M A x T))) :
    HEq ((rightProjection S).mapTm (contextualJ S A x T D d))
      (Instance.contextualJ S.base.right S.rightFiber A.right ⟨x.right⟩
        ((rightProjection S).pathTelescope A x T) ((rightProjection S).jMotive A x T D)
        ((rightProjection S).jBranch A x T D d)) := by
  apply up_heq
  exact eliminateSection_heq
    ((rightProjection S).pathTelescope_total A x T)
    ((rightProjection S).rootTelescope_total A x T)
    (rootTail_right S A x T) (cast_heq _ _).symm
    (section_down_heq ((rightProjection S).rootTelescope_total A x T)
      ((rightProjection S).jBranch_type A x T D)
      ((rightProjection S).jBranch_heq A x T D d).symm)


end Comparison
end SquareKit.Internal.PathTransport.GroupoidModel
