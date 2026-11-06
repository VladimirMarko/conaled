import SquareKit.Internal.DependentJudgments.Templates
import SquareKit.Internal.DependentJudgments.Sigma.Authoring
import SquareKit.Internal.DependentJudgments.Sigma.Stability
namespace GuardedJRetest.Candidate
open SquareKit.Internal.DependentJudgments.Contextual
variable {V : Type} {Ω : List (Judgment V)} {Γ A x T Q p : Expression V} {n : Nat}
variable (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (path A x) T)
variable (hp : Tm (Ω := Ω) (total T) Q p)
def calibration : Command Ω Γ A x := Command.reflexivity hx hT hp
def inner : Tm (Ω := Ω) (total T) (identity Q p p) (calibration hx hT hp).expression :=
  (calibration hx hT hp).typing
def rootMap : Sub (Ω := Ω) (total (pullback T (root A x))) (total T) (rootTail A x T) :=
  hx.rootTail hT
def calibrationBranch : Tm (Ω := Ω) (total (pullback T (root A x)))
    (subTy (identity Q p p) (rootTail A x T))
    (reflexivity (subTy Q (rootTail A x T)) (subTm p (rootTail A x T))) :=
  hp.reflexivitySub (rootMap hx hT)
theorem calibrationRecipe : (calibration hx hT hp).expression =
    j A x T (identity Q p p)
      (reflexivity (subTy Q (rootTail A x T)) (subTm p (rootTail A x T))) := rfl


def outer : Command Ω Γ A x := Command.reflexivity hx hT (inner hx hT hp)
theorem selectedRecipe : (outer hx hT hp).expression =
    j A x T (identity (identity Q p p) (calibration hx hT hp).expression
      (calibration hx hT hp).expression)
      (reflexivity (subTy (identity Q p p) (rootTail A x T))
        (subTm (calibration hx hT hp).expression (rootTail A x T))) := rfl

def outerTyping : Tm (Ω := Ω) (total T)
    (identity (identity Q p p) (calibration hx hT hp).expression (calibration hx hT hp).expression)
    (outer hx hT hp).expression := (outer hx hT hp).typing

def rootLeft : Tm (Ω := Ω) (total (pullback T (root A x)))
    (subTy (outer hx hT hp).motive (rootTail A x T))
    (subTm (outer hx hT hp).expression (rootTail A x T)) :=
  (outer hx hT hp).typing.substitute (rootMap hx hT)
def rootRight : Tm (Ω := Ω) (total (pullback T (root A x)))
    (subTy (outer hx hT hp).motive (rootTail A x T)) (outer hx hT hp).branch :=
  (outer hx hT hp).branchTyping
def rootBeta : Equal (Ω := Ω) (subTm (outer hx hT hp).expression (rootTail A x T))
    (outer hx hT hp).branch :=
  hx.jBeta hT (outer hx hT hp).motiveTyping (outer hx hT hp).branchTyping

variable {Δ σ : Expression V}
variable (hσ : Sub (Ω := Ω) Δ (total (pullback T (root A x))) σ)
def substitutedLeft : Tm (Ω := Ω) Δ
    (subTy (subTy (outer hx hT hp).motive (rootTail A x T)) σ)
    (subTm (subTm (outer hx hT hp).expression (rootTail A x T)) σ) :=
  (rootLeft hx hT hp).substitute hσ
def substitutedRight : Tm (Ω := Ω) Δ
    (subTy (subTy (outer hx hT hp).motive (rootTail A x T)) σ)
    (subTm (outer hx hT hp).branch σ) :=
  (rootRight hx hT hp).substitute hσ
-- Congruence acts on the selected syntax; it does not use semantic equality.
def substitutedBeta : Equal (Ω := Ω)
    (subTm (subTm (outer hx hT hp).expression (rootTail A x T)) σ)
    (subTm (outer hx hT hp).branch σ) :=
  SquareKit.GuardedTheory.Derivation.congruence (T := theory) (Sum.inl SquareKit.Internal.DependentJudgments.Operation.subTm)
    (Fin.cases (rootBeta hx hT hp)
      (Fin.cases (.reflexive σ) (fun i => nomatch i)))

def dependentWeakening : Sub (Ω := Ω)
    (extend (total (pullback T (root A x))) (subTy (identity Q p p) (rootTail A x T)))
    (total (pullback T (root A x)))
    (weaken (total (pullback T (root A x))) (subTy (identity Q p p) (rootTail A x T))) :=
  ((inner hx hT hp).substitute (rootMap hx hT)).family.weaken

def workedLeft := substitutedLeft hx hT hp (dependentWeakening hx hT hp)
def workedRight := substitutedRight hx hT hp (dependentWeakening hx hT hp)
def workedBeta := substitutedBeta (σ := weaken (total (pullback T (root A x)))
  (subTy (identity Q p p) (rootTail A x T))) hx hT hp


open SquareKit
open SquareKit.Internal.DependentJudgments (Value)
open SquareKit.GuardedTheory
universe u

abbrev selectedLeft := subTm (subTm (outer hx hT hp).expression (rootTail A x T)) σ
abbrev selectedRight := subTm (outer hx hT hp).branch σ
abbrev selectedFamily := subTy (subTy (outer hx hT hp).motive (rootTail A x T)) σ

def comparison : TypedEquality Ω Δ (selectedFamily (σ := σ) hx hT hp)
    (selectedLeft (σ := σ) hx hT hp) (selectedRight (σ := σ) hx hT hp) where
  left := substitutedLeft hx hT hp hσ
  right := substitutedRight hx hT hp hσ
  equality := substitutedBeta hx hT hp

include hσ in
theorem comparisonSound (M : Internal.PathTransport.Typed.Model.{u})
    (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ a ∈ Ω, a.eval (algebra M) ρ) :
    (term Δ (selectedFamily (σ := σ) hx hT hp) (selectedLeft (σ := σ) hx hT hp)).eval (algebra M) ρ ∧
    (term Δ (selectedFamily (σ := σ) hx hT hp) (selectedRight (σ := σ) hx hT hp)).eval (algebra M) ρ ∧
    (selectedLeft (σ := σ) hx hT hp).eval (algebra M) ρ =
      (selectedRight (σ := σ) hx hT hp).eval (algebra M) ρ :=
  ⟨interpret (substitutedLeft hx hT hp hσ) M ρ hΩ,
   interpret (substitutedRight hx hT hp hσ) M ρ hΩ,
   interpret (substitutedBeta (σ := σ) hx hT hp) M ρ hΩ⟩

noncomputable def extensionLeft : Derivation Internal.DependentJudgments.Sigma.theory
    (Ω.map (Atom.inl Internal.DependentJudgments.Sigma.extraSignature))
    ((term Δ (selectedFamily (σ := σ) hx hT hp)
      (selectedLeft (σ := σ) hx hT hp)).inl Internal.DependentJudgments.Sigma.extraSignature) :=
  Internal.DependentJudgments.Sigma.retain (substitutedLeft hx hT hp hσ)
noncomputable def extensionRight : Derivation Internal.DependentJudgments.Sigma.theory
    (Ω.map (Atom.inl Internal.DependentJudgments.Sigma.extraSignature))
    ((term Δ (selectedFamily (σ := σ) hx hT hp)
      (selectedRight (σ := σ) hx hT hp)).inl Internal.DependentJudgments.Sigma.extraSignature) :=
  Internal.DependentJudgments.Sigma.retain (substitutedRight hx hT hp hσ)
noncomputable def extensionBeta : Derivation Internal.DependentJudgments.Sigma.theory
    (Ω.map (Atom.inl Internal.DependentJudgments.Sigma.extraSignature))
    ((Atom.eq (selectedLeft (σ := σ) hx hT hp)
      (selectedRight (σ := σ) hx hT hp)).inl Internal.DependentJudgments.Sigma.extraSignature) :=
  Internal.DependentJudgments.Sigma.retain (substitutedBeta hx hT hp)

theorem extensionAssumptions (M : Internal.PathTransport.Typed.Model.{u})
    (S : Internal.DependentJudgments.Sigma.Stable M.toStructuralModel) (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ a ∈ Ω, a.eval (algebra M) ρ) :
    ∀ a ∈ Ω.map (Atom.inl Internal.DependentJudgments.Sigma.extraSignature), a.eval (Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ := by
  intro a ha
  rcases List.mem_map.mp ha with ⟨b, hb, rfl⟩
  rw [Internal.DependentJudgments.Sigma.eval_old_judgment]
  exact hΩ b hb

include hσ in
theorem extensionSelected (M : Internal.PathTransport.Typed.Model.{u})
    (S : Internal.DependentJudgments.Sigma.Stable M.toStructuralModel) (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ a ∈ Ω, a.eval (algebra M) ρ) :
    ((term Δ (selectedFamily (σ := σ) hx hT hp)
      (selectedLeft (σ := σ) hx hT hp)).inl Internal.DependentJudgments.Sigma.extraSignature).eval
        (Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ ∧
    ((term Δ (selectedFamily (σ := σ) hx hT hp)
      (selectedRight (σ := σ) hx hT hp)).inl Internal.DependentJudgments.Sigma.extraSignature).eval
        (Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ ∧
    ((selectedLeft (σ := σ) hx hT hp).inl Internal.DependentJudgments.Sigma.extraSignature).eval
      (Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ =
      ((selectedRight (σ := σ) hx hT hp).inl Internal.DependentJudgments.Sigma.extraSignature).eval
        (Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ ∧
    ((selectedLeft (σ := σ) hx hT hp).inl Internal.DependentJudgments.Sigma.extraSignature).eval
      (Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ = (selectedLeft (σ := σ) hx hT hp).eval (algebra M) ρ ∧
    ((selectedFamily (σ := σ) hx hT hp).inl Internal.DependentJudgments.Sigma.extraSignature).eval
      (Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ = (selectedFamily (σ := σ) hx hT hp).eval (algebra M) ρ ∧
    (Internal.DependentJudgments.Sigma.model M S.toCapability).restrictLeft = model M := by
  have h := extensionAssumptions M S ρ hΩ
  exact ⟨Internal.DependentJudgments.Sigma.interpret (extensionLeft hx hT hp hσ) M S.toCapability ρ h,
    Internal.DependentJudgments.Sigma.interpret (extensionRight hx hT hp hσ) M S.toCapability ρ h,
    Internal.DependentJudgments.Sigma.interpret (extensionBeta (σ := σ) hx hT hp) M S.toCapability ρ h,
    Internal.DependentJudgments.Sigma.eval_old M S.toCapability _ ρ, Internal.DependentJudgments.Sigma.eval_old M S.toCapability _ ρ,
    Internal.DependentJudgments.Sigma.reduct M S.toCapability⟩
end GuardedJRetest.Candidate
