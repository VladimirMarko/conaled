import SquareKit.Internal.DependentJudgments.Sigma.Substitution

/-! Ordinary source authors build dependent sums from their typing derivations.
Model operations, admission proofs and coherence do not occur in this interface. -/
namespace SquareKit.Internal.DependentJudgments.Sigma
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ A B C a b d : Expression V}

private def extra (ax : Axiom) (σ : Fin (rule ax).parameterCount → Expression V)
    (h : ∀ i, Derivation theory Ω (((rule ax).premise i).subst σ)) :
    Derivation theory Ω ((rule ax).conclusion.subst σ) :=
  Derivation.rule (T := theory) (Sum.inr ax) σ h

def Ty.sigma (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B) :
    Ty (Ω := Ω) Γ (Sigma.sigma A B) :=
  by
    have e := extra (Ω := Ω) .formation ![Γ, A, B] (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB) (fun i => nomatch i)))
    simpa [rule] using e

def Ty.pack (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B) :
    Sub (Ω := Ω) (branchContext Γ A B) (extend Γ (Sigma.sigma A B)) (Sigma.pack A B) :=
  by
    have e := extra (Ω := Ω) .pack ![Γ, A, B] (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB) (fun i => nomatch i)))
    simpa [rule] using e

def Ty.unpack (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B) :
    Sub (Ω := Ω) (extend Γ (Sigma.sigma A B)) (branchContext Γ A B) (Sigma.unpack A B) :=
  by
    have e := extra (Ω := Ω) .unpack ![Γ, A, B] (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB) (fun i => nomatch i)))
    simpa [rule] using e

def Tm.pair (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (ha : Tm (Ω := Ω) Γ A a)
    (hb : Tm (Ω := Ω) Γ (subTy B (pairSub A (identitySub Γ) a)) b) :
    Tm (Ω := Ω) Γ (Sigma.sigma A B) (Sigma.pair Γ A B a b) :=
  by
    have e := extra (Ω := Ω) .pair ![Γ, A, B, a, b] (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB) (Fin.cases (by simpa [rule] using ha) (Fin.cases (by simpa [rule] using hb) (fun i => nomatch i)))))
    simpa [rule] using e

def Tm.split (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (hC : Ty (Ω := Ω) (extend Γ (Sigma.sigma A B)) C)
    (hd : Tm (Ω := Ω) (branchContext Γ A B) (subTy C (Sigma.pack A B)) d) :
    Tm (Ω := Ω) (extend Γ (Sigma.sigma A B)) C (Sigma.split A B d) :=
  by
    have e := extra (Ω := Ω) .split ![Γ, A, B, C, d] (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB) (Fin.cases (by simpa [rule] using hC) (Fin.cases (by simpa [rule] using hd) (fun i => nomatch i)))))
    simpa [rule] using e

def Tm.splitBeta (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (hC : Ty (Ω := Ω) (extend Γ (Sigma.sigma A B)) C)
    (hd : Tm (Ω := Ω) (branchContext Γ A B) (subTy C (Sigma.pack A B)) d) :
    Equal (Ω := Ω) (subTm (Sigma.split A B d) (Sigma.pack A B)) d :=
  by
    have e := extra (Ω := Ω) .splitBeta ![Γ, A, B, C, d] (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB) (Fin.cases (by simpa [rule] using hC) (Fin.cases (by simpa [rule] using hd) (fun i => nomatch i)))))
    simpa [rule] using e

def Ty.beta (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B) :
    Equal (Ω := Ω) (comp (Sigma.unpack A B) (Sigma.pack A B)) (identitySub (branchContext Γ A B)) :=
  by
    have e := extra (Ω := Ω) .beta ![Γ, A, B] (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB) (fun i => nomatch i)))
    simpa [rule] using e

def Ty.eta (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B) :
    Equal (Ω := Ω) (comp (Sigma.pack A B) (Sigma.unpack A B))
      (identitySub (extend Γ (Sigma.sigma A B))) :=
  by
    have e := extra (Ω := Ω) .eta ![Γ, A, B] (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB) (fun i => nomatch i)))
    simpa [rule] using e

/-- A named source derivation, fixed before any model or motive is selected. -/
def splitDerivation : Derivation theory (List.ofFn splitRule.premise) splitRule.conclusion := by
  have h (i : Fin splitRule.hypotheses) :
      Derivation theory (List.ofFn splitRule.premise) (splitRule.premise i) :=
    .hypothesis (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact Tm.split (h 0) (h 1) (h 2) (h 3)


/-- The computation argument is also authored independently of its interpretation. -/
def splitBetaDerivation : Derivation theory (List.ofFn splitBetaRule.premise) splitBetaRule.conclusion := by
  have h (i : Fin splitBetaRule.hypotheses) :
      Derivation theory (List.ofFn splitBetaRule.premise) (splitBetaRule.premise i) :=
    .hypothesis (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact Tm.splitBeta (h 0) (h 1) (h 2) (h 3)

end SquareKit.Internal.DependentJudgments.Sigma
