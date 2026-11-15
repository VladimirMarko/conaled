import SquareKit.Internal.DependentJudgments.Sigma.Composition

/-! Elimination eta already follows in the first, eta-strengthened Sigma theory.
The law-only closure extension does not supply an independent assumption here. -/
namespace SquareKit.Internal.DependentJudgments.Sigma
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ Θ A B C t σ τ : Expression V}

@[simp] private theorem inl_term (g a t : Contextual.Expression V) :
    (Contextual.term g a t).inl extraSignature = term (g.inl extraSignature) (a.inl extraSignature) (t.inl extraSignature) := by
  simp only [Atom.inl, term]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] private theorem inl_substitution (g a t : Contextual.Expression V) :
    (Contextual.substitution g a t).inl extraSignature = substitution (g.inl extraSignature) (a.inl extraSignature) (t.inl extraSignature) := by
  simp only [Atom.inl, substitution]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] private theorem inl_subTm (g a : Contextual.Expression V) :
    (Contextual.subTm g a).inl extraSignature = subTm (g.inl extraSignature) (a.inl extraSignature) := by
  simp only [Term.inl, subTm]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] private theorem inl_comp (g a : Contextual.Expression V) :
    (Contextual.comp g a).inl extraSignature = comp (g.inl extraSignature) (a.inl extraSignature) := by
  simp only [Term.inl, comp]
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] private theorem inl_identitySub (g : Contextual.Expression V) :
    (Contextual.identitySub g).inl extraSignature = identitySub (g.inl extraSignature) := by
  simp only [Term.inl, identitySub]
  congr 1
  funext i
  fin_cases i; rfl


@[simp] private theorem inl_variable (v : V) :
    (Term.var v : Contextual.Expression V).inl extraSignature = Term.var v := rfl

private def inherited (ax : Contextual.Axiom)
    (s : Fin (Contextual.rule ax).parameterCount → Expression V)
    (h : ∀ i, Derivation theory Ω
      ((((Contextual.rule ax).premise i).inl extraSignature).subst s)) :
    Derivation theory Ω (((Contextual.rule ax).conclusion.inl extraSignature).subst s) :=
  Derivation.rule (T := theory) (.inl (.inr ax)) s h

def Tm.subComp (ht : Tm (Ω := Ω) Γ A t) (hσ : Sub (Ω := Ω) Δ Γ σ)
    (hτ : Sub (Ω := Ω) Θ Δ τ) :
    Equal (Ω := Ω) (subTm (subTm t σ) τ) (subTm t (comp σ τ)) := by
  have e := inherited (Ω := Ω) .subTmComp ![Γ, Δ, Θ, A, t, σ, τ]
    (Fin.cases (by simpa [Contextual.rule] using ht)
      (Fin.cases (by simpa [Contextual.rule] using hσ)
        (Fin.cases (by simpa [Contextual.rule] using hτ) (fun i => nomatch i))))
  simpa [Contextual.rule, Atom.inl] using e

def Tm.subId (ht : Tm (Ω := Ω) Γ A t) :
    Equal (Ω := Ω) (subTm t (identitySub Γ)) t := by
  have e := inherited (Ω := Ω) .subTmId ![Γ, A, t]
    (Fin.cases (by simpa [Contextual.rule] using ht) (fun i => nomatch i))
  simpa [Contextual.rule, Atom.inl] using e

/-- This derivation belongs to Sigma.theory, not closureTheory. -/
def Tm.splitEta (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (ht : Tm (Ω := Ω) (extend Γ (sigma A B)) C t) :
    Equal (Ω := Ω) (Sigma.split A B (subTm t (pack A B))) t := by
  have hc : Equal (Ω := Ω) (subTm t (comp (pack A B) (unpack A B)))
      (subTm t (identitySub (extend Γ (sigma A B)))) :=
    Derivation.congruence (T := theory) (Sum.inl (Sum.inl DependentJudgments.Operation.subTm))
      (Fin.cases (.reflexive t) (Fin.cases (hA.eta hB) (fun i => nomatch i)))
  exact ((ht.subComp (hA.pack hB) (hA.unpack hB)).transitive hc).transitive ht.subId

/-- The original closure rule, including all of its guarded premises, is
admissible in the first extension. Its family premise is unnecessary here. -/
def splitEtaDerivation : Derivation theory (List.ofFn splitEtaRule.premise) splitEtaRule.conclusion := by
  have h (i : Fin splitEtaRule.hypotheses) :
      Derivation theory (List.ofFn splitEtaRule.premise) (splitEtaRule.premise i) :=
    .hypothesis (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact Tm.splitEta (h 0) (h 1) (h 3)

end SquareKit.Internal.DependentJudgments.Sigma
