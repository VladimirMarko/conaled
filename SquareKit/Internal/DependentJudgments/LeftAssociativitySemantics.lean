import SquareKit.Internal.DependentJudgments.LeftAssociativity
import SquareKit.Internal.DependentJudgments.LeftConcatGroupoidSemantics

/-! Sound interpretation of the same general associativity derivation.
The evaluator retains the selected higher path; endpoint identification uses
composition of the interpreted left-path recipes. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u
variable {V : Type} {Ω : List (Judgment V)} {Γ A t : Expression V}
namespace Tm
/-- Soundness returns the value of the actual source term at its identified
semantic type. No alternative target proof is substituted for that value. -/
theorem evaluates (ht : Tm (Ω := Ω) Γ A t) (M : PathTransport.Typed.Model.{u})
    (ρ : V → Value M.toStructuralModel)
    (hρ : ∀ a ∈ Ω, a.eval (model M).toAlgebra ρ)
    (G : M.Context) (B : M.Family G)
    (hg : Γ.eval (algebra M) ρ = .context G) (ha : A.eval (algebra M) ρ = .family G B) :
    ∃ selected : M.Section G B, t.eval (algebra M) ρ = .term G B selected := by
  have h := Derivation.sound (model M) ht ρ hρ
  change ∃ G B selected, Γ.eval (algebra M) ρ = Value.context G ∧
    A.eval (algebra M) ρ = Value.family G B ∧ t.eval (algebra M) ρ = Value.term G B selected at h
  obtain ⟨G', B', selected, hg', ha', ht'⟩ := h
  rw [hg] at hg'
  cases Value.context.inj hg'
  rw [ha] at ha'
  have e : B = B' := by cases ha'; rfl
  subst B'
  exact ⟨selected, ht'⟩
end Tm
namespace LeftSemantics.Groupoid
open CategoryTheory PathTransport.GroupoidModel
variable (C : Grpd.{u,u}) (B : C ⥤ Type u)
variable (S : ThreePaths Ω Γ) (ρ : V → Value (Instance.fullModel C B).toStructuralModel)
  (G : Grpd.{u,u}) (x y z w : Section (constant (Γ := G) C))
  (p : Section (identityFamily (constant C) x y))
  (q : Section (identityFamily (constant C) y z))
  (r : Section (identityFamily (constant C) z w))
  (hg : Γ.eval (algebra (Instance.fullModel C B)) ρ = .context G)
  (ha : S.first.A.eval (algebra (Instance.fullModel C B)) ρ = .family G (constant C))
  (hx : S.first.x.eval (algebra (Instance.fullModel C B)) ρ = .term G (constant C) ⟨x⟩)
  (hy : S.first.y.eval (algebra (Instance.fullModel C B)) ρ = .term G (constant C) ⟨y⟩)
  (hz : S.z.eval (algebra (Instance.fullModel C B)) ρ = .term G (constant C) ⟨z⟩)
  (hw : S.w.eval (algebra (Instance.fullModel C B)) ρ = .term G (constant C) ⟨w⟩)
  (hp : S.first.p.eval (algebra (Instance.fullModel C B)) ρ = .term G (identityFamily (constant C) x y) ⟨p⟩)
  (hq : S.q.eval (algebra (Instance.fullModel C B)) ρ = .term G (identityFamily (constant C) y z) ⟨q⟩)
  (hr : S.r.eval (algebra (Instance.fullModel C B)) ρ = .term G (identityFamily (constant C) z w) ⟨r⟩)

abbrev leftComposite := PathTransport.GroupoidModel.DerivedSemantics.composePaths (constant C) x z w
  (PathTransport.GroupoidModel.DerivedSemantics.composePaths (constant C) x y z p q) r
abbrev rightComposite := PathTransport.GroupoidModel.DerivedSemantics.composePaths (constant C) x y w p
  (PathTransport.GroupoidModel.DerivedSemantics.composePaths (constant C) y z w q r)

include hg ha hx hy hz hw hp hq hr
theorem associativity_motive : S.motive.eval (algebra (Instance.fullModel C B)) ρ =
    .family G (identityFamily (identityFamily (constant C) x w)
      (leftComposite C G x y z w p q r) (rightComposite C G x y z w p q r)) := by
  have hmid := eval_composite C B ρ Γ S.first.A S.first.x S.first.y S.z S.first.p S.q G x y z p q hg ha hx hy hz hp hq
  have hlast := eval_composite C B ρ Γ S.first.A S.first.y S.z S.w S.q S.r G y z w q r hg ha hy hz hw hq hr
  have hl := eval_composite C B ρ Γ S.first.A S.first.x S.z S.w _ S.r G x z w _ r hg ha hx hz hw hmid hr
  have hh := eval_composite C B ρ Γ S.first.A S.first.x S.first.y S.w S.first.p _ G x y w p _ hg ha hx hy hw hp hlast
  exact DerivedSemantics.identity_eval (Instance.fullModel C B) ρ _ _ _ G _ _ _
    (DerivedSemantics.identity_eval (Instance.fullModel C B) ρ _ _ _ G _ _ _ ha hx hw) hl hh

/-- Arbitrary ordinary-groupoid inputs interpret the source associator itself
as a selected higher path between the two composite path sections. -/
theorem associator_evaluates (hρ : ∀ a ∈ Ω, a.eval (model (Instance.fullModel C B)).toAlgebra ρ) :
    ∃ selected : (Instance.fullModel C B).Section G (identityFamily (identityFamily (constant C) x w)
      (leftComposite C G x y z w p q r) (rightComposite C G x y z w p q r)),
      S.associator.eval (algebra (Instance.fullModel C B)) ρ = .term G _ selected :=
  S.associativity.evaluates (Instance.fullModel C B) ρ hρ G _ hg
    (associativity_motive C B S ρ G x y z w p q r hg ha hx hy hz hw hp hq hr)
end LeftSemantics.Groupoid
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
