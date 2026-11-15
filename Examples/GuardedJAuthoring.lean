import Examples.DependentAuthorCandidate
import Examples.DependentAuthorTrialCases

/-! Calibration of the repaired guarded J interface against the immutable #320
submission. This is public regression evidence, not a fresh author trial. -/
namespace Examples.GuardedJAuthoring
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.GuardedTheory
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ A x T Q p Δ Θ σ τ : Expression V} {n : Nat}
variable (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (path A x) T)
  (hp : Tm (Ω := Ω) (total T) Q p)

/-- The repaired command retains the exact selected source recipe from #320. -/
theorem selected_recipe : (Command.reflexivity hx hT hp).expression =
    j A x T (identity Q p p)
      (reflexivity (subTy Q (rootTail A x T)) (subTm p (rootTail A x T))) := rfl

/-- Comparing expressions leaves the frozen proof artifact unchanged. -/
theorem calibration_recipe : (Command.reflexivity hx hT hp).expression =
    (DependentAuthorTrial.Candidate.certificateCommand hx hT hp).expression := rfl

/-- Identity substitution still requires source type conversion; it is not a
host definitional simplification. This case uses the same branch helper. -/
def identityBranch : Tm (Ω := Ω) (total T)
    (subTy (identity Q p p) (identitySub (total T)))
    (reflexivity (subTy Q (identitySub (total T))) (subTm p (identitySub (total T)))) :=
  hp.reflexivitySub hp.family.context.identity

variable (hσ : Sub (Ω := Ω) Δ (total T) σ) (hτ : Sub (Ω := Ω) Θ Δ τ)

def twice : Tm (Ω := Ω) Θ (subTy (subTy (identity Q p p) σ) τ)
    (subTm (subTm (Command.reflexivity hx hT hp).expression σ) τ) :=
  ((Command.reflexivity hx hT hp).typing.substitute hσ).substitute hτ

def aligned : Tm (Ω := Ω) Θ (subTy (identity Q p p) (comp σ τ))
    (subTm (subTm (Command.reflexivity hx hT hp).expression σ) τ) :=
  (twice hx hT hp hσ hτ).convert ((hp.identity hp).subComp hσ hτ)

def comparison : Equal (Ω := Ω)
    (subTm (subTm (Command.reflexivity hx hT hp).expression σ) τ)
    (subTm (Command.reflexivity hx hT hp).expression (comp σ τ)) :=
  (Command.reflexivity hx hT hp).typing.subComp hσ hτ

/-- Actual dependent weakening arrows are constructed by the retained caller:
the second binder's family depends on the first generic witness. -/
def dependentWeakening := twice hx hT hp
  (DependentAuthorTrial.Candidate.firstWeakening hp)
  (DependentAuthorTrial.Candidate.secondWeakening hp)

universe u
variable (M : SquareKit.Internal.PathTransport.Typed.Model.{u})
  (S : SquareKit.Internal.DependentJudgments.Sigma.Stable M.toStructuralModel)
  (ρ : V → SquareKit.Internal.DependentJudgments.Value M.toStructuralModel)
  (hΩ : ∀ a ∈ Ω, a.eval (algebra M) ρ)

include hσ hτ hΩ in
theorem interpreted :
    (term Θ (subTy (identity Q p p) (comp σ τ))
      (subTm (subTm (Command.reflexivity hx hT hp).expression σ) τ)).eval (algebra M) ρ :=
  interpret (aligned hx hT hp hσ hτ) M ρ hΩ

include hσ hτ hΩ in
/-- Reuse the established Sigma embedding and exact-reduct theorem, retaining
the chosen expression and its full twice-substituted source type. -/
theorem extensionSelected :
    ((term Θ (subTy (subTy (identity Q p p) σ) τ)
      (subTm (subTm (Command.reflexivity hx hT hp).expression σ) τ)).inl
      SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval
      (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ ∧
    ((subTm (subTm (Command.reflexivity hx hT hp).expression σ) τ).inl
      SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval
      (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ =
      (subTm (subTm (Command.reflexivity hx hT hp).expression σ) τ).eval (algebra M) ρ :=
  DependentAuthorTrial.Candidate.extensionSelectedTwice hx hT hp hσ hτ M S ρ hΩ

end Examples.GuardedJAuthoring
