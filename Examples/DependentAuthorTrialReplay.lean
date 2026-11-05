import Examples.DependentAuthorTrialCases

/-! Experimental acceptance probes for #320. The imported author modules are
byte-identical submissions; coordinator probes and cases are separate work.
The independently frozen selected recipe is compared at arbitrary source inputs.
This checks source selection and semantic annotations, not equality of arbitrary
proof objects. See docs/research/dependent-author-interface-trial.md. -/
namespace Examples.DependentAuthorTrialReplay
namespace Baseline
open SquareKit.Internal.PathTransport Typed Authoring
universe u
variable {Γ : RawCtx} {γ : CtxCode.{u}} {A x : Expr} {a : TyCode γ}
  {ξ : TmCode γ a} {n : Nat} {Ξ : RawCtx} {T : TelCode (pathCode a ξ) n}
  {Q p : Expr} {q : TyCode (telTotal T)} {π : TmCode (telTotal T) q}
variable (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
  (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Ξ T)
  (hQ : TyDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q)
  (hp : TmDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q p π)

local notation "cmd" => DependentAuthorTrial.Baseline.certificateCommand hΓ hA hx hT hQ hp
local notation "reference" => DependentAuthorReference.Baseline.certificateCommand hΓ hA hx hT hQ hp

theorem motive_raw : (cmd).motive.raw = Expr.identity Q p p := rfl
theorem branch_raw : (cmd).motive.branch =
    Expr.refl (p.sub (Expr.liftSubN n (reflexiveSub x))) := rfl
theorem motive_code : (cmd).motive.code = identityCode q π π := rfl
theorem branch_code : (cmd).motive.branchCode = (reference).motive.branchCode := rfl

/-- This checks the index of the author's derivation, including selected J code. -/
def selectedTyping : TmDeriv (Ξ ++ pathCtx Γ A x) (telTotal T)
    (Expr.identity Q p p) (identityCode q π π)
    (genericJRaw n A x (Expr.identity Q p p)
      (Expr.refl (p.sub (Expr.liftSubN n (reflexiveSub x)))))
    (jCode a ξ T (identityCode q π π) (reference).motive.branchCode) :=
  DependentAuthorTrial.Baseline.certificate hΓ hA hx hT hQ hp

theorem selected_interpretation (M : Model.{u}) :
    interpretTm M (selectedTyping hΓ hA hx hT hQ hp) =
      jCode a ξ T (identityCode q π π) (reference).motive.branchCode M :=
  interpretTm_agrees M _

end Baseline
namespace Candidate
open SquareKit.Internal.DependentJudgments.Contextual
variable {V : Type} {Ω : List (Judgment V)}
  {Γ A x T Q p : Expression V} {n : Nat}
  (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (path A x) T)
  (hp : Tm (Ω := Ω) (total T) Q p)

/-- Arbitrary tails and arbitrary dependent p select the exact frozen J recipe. -/
theorem selected_recipe : DependentAuthorTrial.Candidate.selected hx hT hp =
    (DependentAuthorReference.Candidate.certificateCommand hx hT hp).expression := rfl

theorem branch_recipe : (DependentAuthorTrial.Candidate.certificateCommand hx hT hp).branch =
    reflexivity (subTy Q (rootTail A x T)) (subTm p (rootTail A x T)) := rfl

/-- The original source typing survives the actual extension embedding. -/
noncomputable def selected_typing := DependentAuthorTrial.Candidate.extendedCertificate hx hT hp

end Candidate
end Examples.DependentAuthorTrialReplay
