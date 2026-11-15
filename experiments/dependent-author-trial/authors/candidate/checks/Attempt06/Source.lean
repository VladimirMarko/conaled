import SquareKit.Internal.DependentJudgments.Templates
import SquareKit.Internal.DependentJudgments.Sigma.Authoring
import SquareKit.Internal.DependentJudgments.Sigma.Stability

namespace DependentAuthorTrial.Candidate
open SquareKit.Internal.DependentJudgments.Contextual

variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A x σ : Expression V}

/-- One-step comparison retains both source operand derivations. -/
def calibration (c : Command Ω Γ A x) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    TypedEquality Ω (total (pathTail A x c.tail σ))
      (subTy c.motive (pathTailMap A x c.tail σ))
      (subTm c.expression (pathTailMap A x c.tail σ)) (c.fresh hσ).expression :=
  c.comparison hσ



open SquareKit.GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {Θ T Q p τ : Expression V} {n : Nat}

def applyExtra (a : Axiom) (args : Fin (rule a).parameterCount → Expression V)
    (h : ∀ i, Derivation theory Ω (((rule a).premise i).subst args)) :
    Derivation theory Ω ((rule a).conclusion.subst args) :=
  Derivation.rule (T := theory) (Sum.inr a) args h

-- The public theory has this rule, but Authoring has no named wrapper for it.
def rootTailTyping (hx : Tm (Ω := Ω) Γ A x)
    (hT : Tel (Ω := Ω) n (path A x) T) :
    Sub (Ω := Ω) (total (pullback T (root A x))) (total T) (rootTail A x T) := by
  have e := applyExtra (Ω := Ω) (Axiom.rootTail n)
    ![Γ, A, x, T]
    (Fin.cases (by simpa [rule] using hx)
      (Fin.cases (by simpa [rule] using hT) (fun i => nomatch i)))
  simpa [rule] using e

variable (hx : Tm (Ω := Ω) Γ A x) (hT : Tel (Ω := Ω) n (path A x) T)
  (hp : Tm (Ω := Ω) (total T) Q p)

def certificateCommand : Command Ω Γ A x where
  point := hx
  length := n
  tail := T
  tailTyping := hT
  motive := identity Q p p
  motiveTyping := hp.identity hp
  branch := reflexivity (subTy Q (rootTail A x T)) (subTm p (rootTail A x T))
  branchTyping := ((hp.substitute (rootTailTyping hx hT)).reflexivity).convert
    (Derivation.symmetric (hp.identitySub hp (rootTailTyping hx hT)))

abbrev selected : Expression V := (certificateCommand hx hT hp).expression

def certificate : Tm (Ω := Ω) (total T) (identity Q p p) (selected hx hT hp) :=
  (certificateCommand hx hT hp).typing

variable (hσ : Sub (Ω := Ω) Δ (total T) σ) (hτ : Sub (Ω := Ω) Θ Δ τ)

def valueTwice : Tm (Ω := Ω) Θ (subTy (subTy Q σ) τ) (subTm (subTm p σ) τ) :=
  (hp.substitute hσ).substitute hτ

def certificateTwice : Tm (Ω := Ω) Θ (subTy (subTy (identity Q p p) σ) τ)
    (subTm (subTm (selected hx hT hp) σ) τ) :=
  ((certificate hx hT hp).substitute hσ).substitute hτ

def valueTypeComparison : Equal (Ω := Ω) (subTy (subTy Q σ) τ) (subTy Q (comp σ τ)) :=
  hp.family.subComp hσ hτ

def certificateTypeComparison : Equal (Ω := Ω)
    (subTy (subTy (identity Q p p) σ) τ) (subTy (identity Q p p) (comp σ τ)) :=
  (hp.identity hp).subComp hσ hτ

def valueComparison : Equal (Ω := Ω) (subTm (subTm p σ) τ) (subTm p (comp σ τ)) :=
  hp.subComp hσ hτ

def certificateComparison : Equal (Ω := Ω)
    (subTm (subTm (selected hx hT hp) σ) τ) (subTm (selected hx hT hp) (comp σ τ)) :=
  (certificate hx hT hp).subComp hσ hτ

def certificateAligned : Tm (Ω := Ω) Θ (subTy (identity Q p p) (comp σ τ))
    (subTm (subTm (selected hx hT hp) σ) τ) :=
  (certificateTwice hx hT hp hσ hτ).convert (certificateTypeComparison hp hσ hτ)

abbrev firstContext := extend (total T) (identity Q p p)
abbrev firstMap := weaken (total T) (identity Q p p)
abbrev witness := generic (total T) (identity Q p p)
abbrev secondFamily := identity (subTy (identity Q p p) (firstMap (T := T) (Q := Q) (p := p)))
  (witness (T := T) (Q := Q) (p := p)) (witness (T := T) (Q := Q) (p := p))
abbrev secondContext := extend (firstContext (T := T) (Q := Q) (p := p))
  (secondFamily (T := T) (Q := Q) (p := p))
abbrev secondMap := weaken (firstContext (T := T) (Q := Q) (p := p))
  (secondFamily (T := T) (Q := Q) (p := p))

def firstWeakening : Sub (Ω := Ω) (firstContext (T := T) (Q := Q) (p := p))
    (total T) (firstMap (T := T) (Q := Q) (p := p)) :=
  (hp.identity hp).weaken

def witnessVariable : Tm (Ω := Ω) (firstContext (T := T) (Q := Q) (p := p))
    (subTy (identity Q p p) (firstMap (T := T) (Q := Q) (p := p)))
    (witness (T := T) (Q := Q) (p := p)) :=
  (hp.identity hp).generic

def secondWeakening : Sub (Ω := Ω) (secondContext (T := T) (Q := Q) (p := p))
    (firstContext (T := T) (Q := Q) (p := p)) (secondMap (T := T) (Q := Q) (p := p)) :=
  ((witnessVariable hp).identity (witnessVariable hp)).weaken

def dependentWeakeningCertificate :=
  certificateTwice hx hT hp (firstWeakening hp) (secondWeakening hp)

def dependentWeakeningComparison :=
  certificateComparison hx hT hp (firstWeakening hp) (secondWeakening hp)



-- The recipe is retained as source syntax; this is not a UIP claim.
theorem selectedRecipe : selected hx hT hp =
    j A x T (identity Q p p)
      (reflexivity (subTy Q (rootTail A x T)) (subTm p (rootTail A x T))) := rfl

def selectedRootComparison : Equal (Ω := Ω)
    (subTm (selected hx hT hp) (rootTail A x T))
    (reflexivity (subTy Q (rootTail A x T)) (subTm p (rootTail A x T))) :=
  hx.jBeta hT (hp.identity hp) (certificateCommand hx hT hp).branchTyping

def valueComposite := hp.substitute (hσ.comp hτ)
def certificateComposite := (certificate hx hT hp).substitute (hσ.comp hτ)
def dependentWeakeningAligned :=
  certificateAligned hx hT hp (firstWeakening hp) (secondWeakening hp)

universe u
variable (M : SquareKit.Internal.PathTransport.Typed.Model.{u})
  (S : SquareKit.Internal.DependentJudgments.Sigma.Stable M.toStructuralModel)
  (ρ : V → SquareKit.Internal.DependentJudgments.Value M.toStructuralModel)
  (hΩ : ∀ a ∈ Ω, a.eval (algebra M) ρ)

include hp hΩ in
theorem originalValueValidity : (term (total T) Q p).eval (algebra M) ρ :=
  interpret hp M ρ hΩ

include hΩ in
theorem originalCertificateValidity :
    (term (total T) (identity Q p p) (selected hx hT hp)).eval (algebra M) ρ :=
  interpret (certificate hx hT hp) M ρ hΩ

include hp hσ hτ hΩ in
theorem valueValidity :
    (term Θ (subTy (subTy Q σ) τ) (subTm (subTm p σ) τ)).eval (algebra M) ρ :=
  interpret (valueTwice hp hσ hτ) M ρ hΩ

include hσ hτ hΩ in
theorem certificateValidity :
    (term Θ (subTy (subTy (identity Q p p) σ) τ)
      (subTm (subTm (selected hx hT hp) σ) τ)).eval (algebra M) ρ :=
  interpret (certificateTwice hx hT hp hσ hτ) M ρ hΩ

include hp hσ hτ hΩ in
theorem certificateTypeValidity :
    (subTy (subTy (identity Q p p) σ) τ).eval (algebra M) ρ =
      (subTy (identity Q p p) (comp σ τ)).eval (algebra M) ρ :=
  interpret (certificateTypeComparison hp hσ hτ) M ρ hΩ

include hσ hτ hΩ in
theorem certificateComparisonValidity :
    (subTm (subTm (selected hx hT hp) σ) τ).eval (algebra M) ρ =
      (subTm (selected hx hT hp) (comp σ τ)).eval (algebra M) ρ :=
  interpret (certificateComparison hx hT hp hσ hτ) M ρ hΩ

noncomputable def extendedCertificate :
    Derivation SquareKit.Internal.DependentJudgments.Sigma.theory (Ω.map (Atom.inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature))
      ((term (total T) (identity Q p p) (selected hx hT hp)).inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature) :=
  SquareKit.Internal.DependentJudgments.Sigma.retain (certificate hx hT hp)

noncomputable def extendedCertificateTwice :=
  SquareKit.Internal.DependentJudgments.Sigma.retain (certificateTwice hx hT hp hσ hτ)
noncomputable def extendedCertificateAligned :=
  SquareKit.Internal.DependentJudgments.Sigma.retain (certificateAligned hx hT hp hσ hτ)
noncomputable def extendedValue := SquareKit.Internal.DependentJudgments.Sigma.retain hp
noncomputable def extendedType := SquareKit.Internal.DependentJudgments.Sigma.retain (certificateTypeComparison hp hσ hτ)

include hΩ in
theorem extendedAssumptions : ∀ a ∈ Ω.map (Atom.inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature),
    a.eval (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  simpa only [SquareKit.Internal.DependentJudgments.Sigma.eval_old_judgment] using hΩ b hb

include hΩ in
theorem extendedValidity :
    ((term (total T) (identity Q p p) (selected hx hT hp)).inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval
      (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ :=
  SquareKit.Internal.DependentJudgments.Sigma.interpret (extendedCertificate hx hT hp) M S.toCapability ρ
    (extendedAssumptions M S ρ hΩ)

include hσ hτ hΩ in
theorem extendedTwiceValidity :
    ((term Θ (subTy (subTy (identity Q p p) σ) τ)
      (subTm (subTm (selected hx hT hp) σ) τ)).inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval
      (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ :=
  SquareKit.Internal.DependentJudgments.Sigma.interpret (extendedCertificateTwice hx hT hp hσ hτ) M S.toCapability ρ
    (extendedAssumptions M S ρ hΩ)

-- Recovery includes validity, so malformed expressions cannot discharge it.
include hΩ in
theorem extensionSelected :
    ((term (total T) (identity Q p p) (selected hx hT hp)).inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval
      (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ ∧
    ((selected hx hT hp).inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ =
      (selected hx hT hp).eval (algebra M) ρ :=
  ⟨extendedValidity hx hT hp M S ρ hΩ, SquareKit.Internal.DependentJudgments.Sigma.eval_old M S.toCapability _ ρ⟩

include hp hΩ in
theorem extensionValue :
    ((term (total T) Q p).inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ ∧
    (p.inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ =
      p.eval (algebra M) ρ :=
  ⟨SquareKit.Internal.DependentJudgments.Sigma.interpret (extendedValue hp) M S.toCapability ρ (extendedAssumptions M S ρ hΩ),
    SquareKit.Internal.DependentJudgments.Sigma.eval_old M S.toCapability _ ρ⟩

include hp hσ hτ hΩ in
theorem extensionType :
    ((subTy (subTy (identity Q p p) σ) τ).inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval
      (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ =
      ((subTy (identity Q p p) (comp σ τ)).inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval
        (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ ∧
    ((subTy (identity Q p p) (comp σ τ)).inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval
      (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ =
      (subTy (identity Q p p) (comp σ τ)).eval (algebra M) ρ :=
  ⟨SquareKit.Internal.DependentJudgments.Sigma.interpret (extendedType hp hσ hτ) M S.toCapability ρ
    (extendedAssumptions M S ρ hΩ), SquareKit.Internal.DependentJudgments.Sigma.eval_old M S.toCapability _ ρ⟩

include hσ hτ hΩ in
theorem extensionSelectedTwice :
    ((term Θ (subTy (subTy (identity Q p p) σ) τ)
      (subTm (subTm (selected hx hT hp) σ) τ)).inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval
      (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ ∧
    ((subTm (subTm (selected hx hT hp) σ) τ).inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval
      (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ =
      (subTm (subTm (selected hx hT hp) σ) τ).eval (algebra M) ρ :=
  ⟨extendedTwiceValidity hx hT hp hσ hτ M S ρ hΩ, SquareKit.Internal.DependentJudgments.Sigma.eval_old M S.toCapability _ ρ⟩



include hp hσ hτ hΩ in
theorem extensionValueTwice :
    ((term Θ (subTy (subTy Q σ) τ) (subTm (subTm p σ) τ)).inl
      SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval
      (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ ∧
    ((subTm (subTm p σ) τ).inl SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval
      (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ =
      (subTm (subTm p σ) τ).eval (algebra M) ρ :=
  ⟨SquareKit.Internal.DependentJudgments.Sigma.interpret
    (SquareKit.Internal.DependentJudgments.Sigma.retain (valueTwice hp hσ hτ))
    M S.toCapability ρ (extendedAssumptions M S ρ hΩ),
    SquareKit.Internal.DependentJudgments.Sigma.eval_old M S.toCapability _ ρ⟩

include hσ hτ hΩ in
theorem extensionAlignedValidity :
    ((term Θ (subTy (identity Q p p) (comp σ τ))
      (subTm (subTm (selected hx hT hp) σ) τ)).inl
      SquareKit.Internal.DependentJudgments.Sigma.extraSignature).eval
      (SquareKit.Internal.DependentJudgments.Sigma.algebra M S.toCapability) ρ :=
  SquareKit.Internal.DependentJudgments.Sigma.interpret
    (extendedCertificateAligned hx hT hp hσ hτ) M S.toCapability ρ
    (extendedAssumptions M S ρ hΩ)

#check @calibration
#check @certificateCommand
#check @certificate
#check @valueTwice
#check @certificateTwice
#check @valueTypeComparison
#check @certificateTypeComparison
#check @certificateComparison
#check @certificateAligned
#check @firstWeakening
#check @witnessVariable
#check @secondWeakening
#check @dependentWeakeningCertificate
#check @dependentWeakeningComparison
#check @valueValidity
#check @certificateValidity
#check @certificateTypeValidity
#check @extendedCertificate
#check @extendedValidity
#check @extensionSelected
#check @extensionValue
#check @extensionType
#check @extensionValueTwice
#check @extensionAlignedValidity
#print axioms calibration
#print axioms applyExtra
#print axioms rootTailTyping
#print axioms certificateCommand
#print axioms selected
#print axioms certificate
#print axioms valueTwice
#print axioms certificateTwice
#print axioms valueTypeComparison
#print axioms certificateTypeComparison
#print axioms valueComparison
#print axioms certificateComparison
#print axioms certificateAligned
#print axioms firstContext
#print axioms firstMap
#print axioms witness
#print axioms secondFamily
#print axioms secondContext
#print axioms secondMap
#print axioms firstWeakening
#print axioms witnessVariable
#print axioms secondWeakening
#print axioms dependentWeakeningCertificate
#print axioms dependentWeakeningComparison
#print axioms selectedRecipe
#print axioms selectedRootComparison
#print axioms valueComposite
#print axioms certificateComposite
#print axioms dependentWeakeningAligned
#print axioms originalValueValidity
#print axioms originalCertificateValidity
#print axioms valueValidity
#print axioms certificateValidity
#print axioms certificateTypeValidity
#print axioms certificateComparisonValidity
#print axioms extendedCertificate
#print axioms extendedCertificateTwice
#print axioms extendedCertificateAligned
#print axioms extendedValue
#print axioms extendedType
#print axioms extendedAssumptions
#print axioms extendedValidity
#print axioms extendedTwiceValidity
#print axioms extensionSelected
#print axioms extensionValue
#print axioms extensionType
#print axioms extensionSelectedTwice
#print axioms extensionValueTwice
#print axioms extensionAlignedValidity
end DependentAuthorTrial.Candidate
