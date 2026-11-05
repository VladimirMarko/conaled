import SquareKit.Internal.DependentJudgments.Sigma.Reindexing

/-! Source authors use the stable theory with ordinary typing premises. The
constructor laws and dependent branch alignments are supplied by admission. -/
namespace SquareKit.Internal.DependentJudgments.Sigma.Reindexing
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A B C a b d σ : Expression V}

abbrev Ctx (Γ : Expression V) := Derivation theory Ω (context Γ)
abbrev Ty (Γ A : Expression V) := Derivation theory Ω (family Γ A)
abbrev Tm (Γ A t : Expression V) := Derivation theory Ω (term Γ A t)
abbrev Sub (Δ Γ σ : Expression V) := Derivation theory Ω (substitution Δ Γ σ)
abbrev Equal (a b : Expression V) := Derivation theory Ω (.eq a b)

private def extra (ax : Sigma.Axiom) (σ : Fin (Sigma.rule ax).parameterCount → Expression V)
    (h : ∀ i, Derivation theory Ω (((Sigma.rule ax).premise i).subst σ)) :
    Derivation theory Ω ((Sigma.rule ax).conclusion.subst σ) :=
  Derivation.rule (T := theory) (Sum.inl (Sum.inr ax)) σ h

def Ty.sigma (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B) :
    Ty (Ω := Ω) Γ (Sigma.sigma A B) :=
  by
    have e := extra (Ω := Ω) .formation ![Γ, A, B] (Fin.cases (by simpa [Sigma.rule] using hA) (Fin.cases (by simpa [Sigma.rule] using hB) (fun i => nomatch i)))
    simpa [Sigma.rule] using e

def Ty.pack (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B) :
    Sub (Ω := Ω) (branchContext Γ A B) (extend Γ (Sigma.sigma A B)) (Sigma.pack A B) :=
  by
    have e := extra (Ω := Ω) .pack ![Γ, A, B] (Fin.cases (by simpa [Sigma.rule] using hA) (Fin.cases (by simpa [Sigma.rule] using hB) (fun i => nomatch i)))
    simpa [Sigma.rule] using e

def Ty.unpack (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B) :
    Sub (Ω := Ω) (extend Γ (Sigma.sigma A B)) (branchContext Γ A B) (Sigma.unpack A B) :=
  by
    have e := extra (Ω := Ω) .unpack ![Γ, A, B] (Fin.cases (by simpa [Sigma.rule] using hA) (Fin.cases (by simpa [Sigma.rule] using hB) (fun i => nomatch i)))
    simpa [Sigma.rule] using e

def Tm.pair (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (ha : Tm (Ω := Ω) Γ A a)
    (hb : Tm (Ω := Ω) Γ (subTy B (pairSub A (identitySub Γ) a)) b) :
    Tm (Ω := Ω) Γ (Sigma.sigma A B) (Sigma.pair Γ A B a b) :=
  by
    have e := extra (Ω := Ω) .pair ![Γ, A, B, a, b] (Fin.cases (by simpa [Sigma.rule] using hA) (Fin.cases (by simpa [Sigma.rule] using hB) (Fin.cases (by simpa [Sigma.rule] using ha) (Fin.cases (by simpa [Sigma.rule] using hb) (fun i => nomatch i)))))
    simpa [Sigma.rule] using e

def Tm.split (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (hC : Ty (Ω := Ω) (extend Γ (Sigma.sigma A B)) C)
    (hd : Tm (Ω := Ω) (branchContext Γ A B) (subTy C (Sigma.pack A B)) d) :
    Tm (Ω := Ω) (extend Γ (Sigma.sigma A B)) C (Sigma.split A B d) :=
  by
    have e := extra (Ω := Ω) .split ![Γ, A, B, C, d] (Fin.cases (by simpa [Sigma.rule] using hA) (Fin.cases (by simpa [Sigma.rule] using hB) (Fin.cases (by simpa [Sigma.rule] using hC) (Fin.cases (by simpa [Sigma.rule] using hd) (fun i => nomatch i)))))
    simpa [Sigma.rule] using e

def Tm.splitBeta (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (hC : Ty (Ω := Ω) (extend Γ (Sigma.sigma A B)) C)
    (hd : Tm (Ω := Ω) (branchContext Γ A B) (subTy C (Sigma.pack A B)) d) :
    Equal (Ω := Ω) (subTm (Sigma.split A B d) (Sigma.pack A B)) d :=
  by
    have e := extra (Ω := Ω) .splitBeta ![Γ, A, B, C, d] (Fin.cases (by simpa [Sigma.rule] using hA) (Fin.cases (by simpa [Sigma.rule] using hB) (Fin.cases (by simpa [Sigma.rule] using hC) (Fin.cases (by simpa [Sigma.rule] using hd) (fun i => nomatch i)))))
    simpa [Sigma.rule] using e

def Ty.beta (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B) :
    Equal (Ω := Ω) (comp (Sigma.unpack A B) (Sigma.pack A B)) (identitySub (branchContext Γ A B)) :=
  by
    have e := extra (Ω := Ω) .beta ![Γ, A, B] (Fin.cases (by simpa [Sigma.rule] using hA) (Fin.cases (by simpa [Sigma.rule] using hB) (fun i => nomatch i)))
    simpa [Sigma.rule] using e

def Ty.eta (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B) :
    Equal (Ω := Ω) (comp (Sigma.pack A B) (Sigma.unpack A B))
      (identitySub (extend Γ (Sigma.sigma A B))) :=
  by
    have e := extra (Ω := Ω) .eta ![Γ, A, B] (Fin.cases (by simpa [Sigma.rule] using hA) (Fin.cases (by simpa [Sigma.rule] using hB) (fun i => nomatch i)))
    simpa [Sigma.rule] using e


private def stable (ax : Axiom) (σ : Fin (rule ax).parameterCount → Expression V)
    (h : ∀ i, Derivation theory Ω (((rule ax).premise i).subst σ)) :
    Derivation theory Ω ((rule ax).conclusion.subst σ) :=
  Derivation.rule (T := theory) (Sum.inr ax) σ h

def Ty.sigmaSub (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (hσ : Sub (Ω := Ω) Δ Γ σ) : Equal (Ω := Ω) (subTy (Sigma.sigma A B) σ) (Sigma.sigma (subTy A σ) (subTy B (lift Δ A σ))) := by
  have e := stable (Ω := Ω) .sigmaSub ![Γ, A, B, Δ, σ]
    (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB)
      (Fin.cases (by simpa [rule] using hσ) (fun i => nomatch i))))
  simpa [rule] using e

def Ty.packSub (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (hσ : Sub (Ω := Ω) Δ Γ σ) : Equal (Ω := Ω) (comp (lift Δ (Sigma.sigma A B) σ) (Sigma.pack (subTy A σ) (subTy B (lift Δ A σ)))) (comp (Sigma.pack A B) (lift (extend Δ (subTy A σ)) B (lift Δ A σ))) := by
  have e := stable (Ω := Ω) .packSub ![Γ, A, B, Δ, σ]
    (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB)
      (Fin.cases (by simpa [rule] using hσ) (fun i => nomatch i))))
  simpa [rule] using e

def Ty.unpackSub (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (hσ : Sub (Ω := Ω) Δ Γ σ) : Equal (Ω := Ω) (comp (Sigma.unpack A B) (lift Δ (Sigma.sigma A B) σ)) (comp (lift (extend Δ (subTy A σ)) B (lift Δ A σ)) (Sigma.unpack (subTy A σ) (subTy B (lift Δ A σ)))) := by
  have e := stable (Ω := Ω) .unpackSub ![Γ, A, B, Δ, σ]
    (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB)
      (Fin.cases (by simpa [rule] using hσ) (fun i => nomatch i))))
  simpa [rule] using e

def Tm.splitSub (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (hC : Ty (Ω := Ω) (extend Γ (Sigma.sigma A B)) C)
    (hd : Tm (Ω := Ω) (branchContext Γ A B) (subTy C (Sigma.pack A B)) d)
    (hσ : Sub (Ω := Ω) Δ Γ σ) : Equal (Ω := Ω) (subTm (Sigma.split A B d) (lift Δ (Sigma.sigma A B) σ)) (Sigma.split (subTy A σ) (subTy B (lift Δ A σ)) (subTm d (lift (extend Δ (subTy A σ)) B (lift Δ A σ)))) := by
  have e := stable (Ω := Ω) .splitSub ![Γ, A, B, C, d, Δ, σ]
    (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB)
      (Fin.cases (by simpa [rule] using hC) (Fin.cases (by simpa [rule] using hd)
        (Fin.cases (by simpa [rule] using hσ) (fun i => nomatch i))))))
  simpa [rule] using e

def Tm.branchType (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (hC : Ty (Ω := Ω) (extend Γ (Sigma.sigma A B)) C)
    (hd : Tm (Ω := Ω) (branchContext Γ A B) (subTy C (Sigma.pack A B)) d)
    (hσ : Sub (Ω := Ω) Δ Γ σ) : Equal (Ω := Ω) (subTy (subTy C (Sigma.pack A B)) (lift (extend Δ (subTy A σ)) B (lift Δ A σ))) (subTy (subTy C (lift Δ (Sigma.sigma A B) σ)) (Sigma.pack (subTy A σ) (subTy B (lift Δ A σ)))) := by
  have e := stable (Ω := Ω) .branchType ![Γ, A, B, C, d, Δ, σ]
    (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB)
      (Fin.cases (by simpa [rule] using hC) (Fin.cases (by simpa [rule] using hd)
        (Fin.cases (by simpa [rule] using hσ) (fun i => nomatch i))))))
  simpa [rule] using e

def Tm.pairReindex (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (ha : Tm (Ω := Ω) Γ A a)
    (hb : Tm (Ω := Ω) Γ (subTy B (pairSub A (identitySub Γ) a)) b)
    (hσ : Sub (Ω := Ω) Δ Γ σ) : Equal (Ω := Ω)
      (subTm (Sigma.pair Γ A B a b) σ)
      (Sigma.pair Δ (subTy A σ) (subTy B (lift Δ A σ)) (subTm a σ) (subTm b σ)) := by
  have e := stable (Ω := Ω) .pairSub ![Γ, A, B, a, b, Δ, σ]
    (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB)
      (Fin.cases (by simpa [rule] using ha) (Fin.cases (by simpa [rule] using hb)
        (Fin.cases (by simpa [rule] using hσ) (fun i => nomatch i))))))
  simpa [rule] using e

/-- A dependent source argument fixed before the interpreting setting is chosen. -/
def splitReindexDerivation : Derivation theory (List.ofFn splitSubRule.premise) splitSubRule.conclusion := by
  have h (i : Fin splitSubRule.hypotheses) :
      Derivation theory (List.ofFn splitSubRule.premise) (splitSubRule.premise i) :=
    .hypothesis (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact Tm.splitSub (h 0) (h 1) (h 2) (h 3) (h 4)

variable {Θ τ t : Expression V}

@[local simp] private theorem inl_base_context ( x0 : DependentJudgments.Expression V) :
    (DependentJudgments.context x0).inl Contextual.extraSignature = Contextual.context (x0.inl Contextual.extraSignature) := by
  simp only [DependentJudgments.context, Contextual.context, Atom.inl]
  congr 1
  funext i
  fin_cases i ; rfl

@[local simp] private theorem inl_base_family ( x0 x1 : DependentJudgments.Expression V) :
    (DependentJudgments.family x0 x1).inl Contextual.extraSignature = Contextual.family (x0.inl Contextual.extraSignature) (x1.inl Contextual.extraSignature) := by
  simp only [DependentJudgments.family, Contextual.family, Atom.inl]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_base_term ( x0 x1 x2 : DependentJudgments.Expression V) :
    (DependentJudgments.term x0 x1 x2).inl Contextual.extraSignature = Contextual.term (x0.inl Contextual.extraSignature) (x1.inl Contextual.extraSignature) (x2.inl Contextual.extraSignature) := by
  simp only [DependentJudgments.term, Contextual.term, Atom.inl]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_base_substitution ( x0 x1 x2 : DependentJudgments.Expression V) :
    (DependentJudgments.substitution x0 x1 x2).inl Contextual.extraSignature = Contextual.substitution (x0.inl Contextual.extraSignature) (x1.inl Contextual.extraSignature) (x2.inl Contextual.extraSignature) := by
  simp only [DependentJudgments.substitution, Contextual.substitution, Atom.inl]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_base_extend ( x0 x1 : DependentJudgments.Expression V) :
    (DependentJudgments.extend x0 x1).inl Contextual.extraSignature = Contextual.extend (x0.inl Contextual.extraSignature) (x1.inl Contextual.extraSignature) := by
  simp only [DependentJudgments.extend, Contextual.extend, Term.inl, apply2]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_base_weaken ( x0 x1 : DependentJudgments.Expression V) :
    (DependentJudgments.weaken x0 x1).inl Contextual.extraSignature = Contextual.weaken (x0.inl Contextual.extraSignature) (x1.inl Contextual.extraSignature) := by
  simp only [DependentJudgments.weaken, Contextual.weaken, Term.inl, apply2]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_base_generic ( x0 x1 : DependentJudgments.Expression V) :
    (DependentJudgments.generic x0 x1).inl Contextual.extraSignature = Contextual.generic (x0.inl Contextual.extraSignature) (x1.inl Contextual.extraSignature) := by
  simp only [DependentJudgments.generic, Contextual.generic, Term.inl, apply2]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_base_subTy ( x0 x1 : DependentJudgments.Expression V) :
    (DependentJudgments.subTy x0 x1).inl Contextual.extraSignature = Contextual.subTy (x0.inl Contextual.extraSignature) (x1.inl Contextual.extraSignature) := by
  simp only [DependentJudgments.subTy, Contextual.subTy, Term.inl, apply2]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_base_subTm ( x0 x1 : DependentJudgments.Expression V) :
    (DependentJudgments.subTm x0 x1).inl Contextual.extraSignature = Contextual.subTm (x0.inl Contextual.extraSignature) (x1.inl Contextual.extraSignature) := by
  simp only [DependentJudgments.subTm, Contextual.subTm, Term.inl, apply2]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_base_comp ( x0 x1 : DependentJudgments.Expression V) :
    (DependentJudgments.comp x0 x1).inl Contextual.extraSignature = Contextual.comp (x0.inl Contextual.extraSignature) (x1.inl Contextual.extraSignature) := by
  simp only [DependentJudgments.comp, Contextual.comp, Term.inl, apply2]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_base_pair ( x0 x1 x2 : DependentJudgments.Expression V) :
    (DependentJudgments.pair x0 x1 x2).inl Contextual.extraSignature = Contextual.pair (x0.inl Contextual.extraSignature) (x1.inl Contextual.extraSignature) (x2.inl Contextual.extraSignature) := by
  simp only [DependentJudgments.pair, Contextual.pair, Term.inl, apply3]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_contextual_context ( x0 : Contextual.Expression V) :
    (Contextual.context x0).inl extraSignature = Sigma.context (x0.inl extraSignature) := by
  simp only [Sigma.context, Atom.inl]
  congr 1
  funext i
  fin_cases i ; rfl

@[local simp] private theorem inl_contextual_family ( x0 x1 : Contextual.Expression V) :
    (Contextual.family x0 x1).inl extraSignature = Sigma.family (x0.inl extraSignature) (x1.inl extraSignature) := by
  simp only [Sigma.family, Atom.inl]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_contextual_term ( x0 x1 x2 : Contextual.Expression V) :
    (Contextual.term x0 x1 x2).inl extraSignature = Sigma.term (x0.inl extraSignature) (x1.inl extraSignature) (x2.inl extraSignature) := by
  simp only [Sigma.term, Atom.inl]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_contextual_substitution ( x0 x1 x2 : Contextual.Expression V) :
    (Contextual.substitution x0 x1 x2).inl extraSignature = Sigma.substitution (x0.inl extraSignature) (x1.inl extraSignature) (x2.inl extraSignature) := by
  simp only [Sigma.substitution, Atom.inl]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_contextual_extend ( x0 x1 : Contextual.Expression V) :
    (Contextual.extend x0 x1).inl extraSignature = Sigma.extend (x0.inl extraSignature) (x1.inl extraSignature) := by
  simp only [Sigma.extend, Term.inl]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_contextual_weaken ( x0 x1 : Contextual.Expression V) :
    (Contextual.weaken x0 x1).inl extraSignature = Sigma.weaken (x0.inl extraSignature) (x1.inl extraSignature) := by
  simp only [Sigma.weaken, Term.inl]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_contextual_generic ( x0 x1 : Contextual.Expression V) :
    (Contextual.generic x0 x1).inl extraSignature = Sigma.generic (x0.inl extraSignature) (x1.inl extraSignature) := by
  simp only [Sigma.generic, Term.inl]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_contextual_subTy ( x0 x1 : Contextual.Expression V) :
    (Contextual.subTy x0 x1).inl extraSignature = Sigma.subTy (x0.inl extraSignature) (x1.inl extraSignature) := by
  simp only [Sigma.subTy, Term.inl]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_contextual_subTm ( x0 x1 : Contextual.Expression V) :
    (Contextual.subTm x0 x1).inl extraSignature = Sigma.subTm (x0.inl extraSignature) (x1.inl extraSignature) := by
  simp only [Sigma.subTm, Term.inl]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_contextual_comp ( x0 x1 : Contextual.Expression V) :
    (Contextual.comp x0 x1).inl extraSignature = Sigma.comp (x0.inl extraSignature) (x1.inl extraSignature) := by
  simp only [Sigma.comp, Term.inl]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_contextual_pair ( x0 x1 x2 : Contextual.Expression V) :
    (Contextual.pair x0 x1 x2).inl extraSignature = Sigma.pairSub (x0.inl extraSignature) (x1.inl extraSignature) (x2.inl extraSignature) := by
  simp only [Sigma.pairSub, Term.inl]
  congr 1
  funext i
  fin_cases i <;> rfl

@[local simp] private theorem inl_var {S R : Signature} {W : Type} (v : W) :
    (Term.var v : Term S W).inl R = .var v := rfl

@[local simp] private theorem inl_eq {S R : Signature} {W : Type} (a b : Term S W) :
    (Atom.eq a b).inl R = Atom.eq (a.inl R) (b.inl R) := rfl

private def contextual (a : Contextual.Axiom)
    (σ : Fin (Contextual.rule a).parameterCount → Expression V)
    (h : ∀ i, Derivation theory Ω ((((Contextual.rule a).premise i).inl extraSignature).subst σ)) :
    Derivation theory Ω (((Contextual.rule a).conclusion.inl extraSignature).subst σ) :=
  Derivation.rule (T := theory) (Sum.inl (Sum.inl (Sum.inr a))) σ h

private def structural (a : ComprehensionAxiom)
    (σ : Fin (comprehensionTheory.rule a).parameterCount → Expression V)
    (h : ∀ i, Derivation theory Ω (((((comprehensionTheory.rule a).premise i).inl Contextual.extraSignature).inl extraSignature).subst σ)) :
    Derivation theory Ω ((((comprehensionTheory.rule a).conclusion.inl Contextual.extraSignature).inl extraSignature).subst σ) :=
  Derivation.rule (T := theory) (Sum.inl (Sum.inl (Sum.inl a))) σ h

def Ty.extend (hA : Ty (Ω := Ω) Γ A) : Ctx (Ω := Ω) (Sigma.extend Γ A) := by
  have e := structural (Ω := Ω) .extension ![Γ, A] (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hA) (fun i => nomatch i))
  simpa [Contextual.rule, comprehensionTheory] using e

def Ty.weaken (hA : Ty (Ω := Ω) Γ A) : Sub (Ω := Ω) (Sigma.extend Γ A) Γ (Sigma.weaken Γ A) := by
  have e := structural (Ω := Ω) .weakening ![Γ, A] (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hA) (fun i => nomatch i))
  simpa [Contextual.rule, comprehensionTheory] using e

def Ty.generic (hA : Ty (Ω := Ω) Γ A) : Tm (Ω := Ω) (Sigma.extend Γ A) (subTy A (Sigma.weaken Γ A)) (Sigma.generic Γ A) := by
  have e := structural (Ω := Ω) .generic ![Γ, A] (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hA) (fun i => nomatch i))
  simpa [Contextual.rule, comprehensionTheory] using e

def Ty.substitute (hA : Ty (Ω := Ω) Γ A) (hσ : Sub (Ω := Ω) Δ Γ σ) : Ty (Ω := Ω) Δ (subTy A σ) := by
  have e := contextual (Ω := Ω) .subTy ![Γ, Δ, A, σ] (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hA) (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hσ) (fun i => nomatch i)))
  simpa [Contextual.rule, comprehensionTheory] using e

def Tm.substitute (ht : Tm (Ω := Ω) Γ A t) (hσ : Sub (Ω := Ω) Δ Γ σ) : Tm (Ω := Ω) Δ (subTy A σ) (subTm t σ) := by
  have e := contextual (Ω := Ω) .subTm ![Γ, Δ, A, t, σ] (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using ht) (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hσ) (fun i => nomatch i)))
  simpa [Contextual.rule, comprehensionTheory] using e

def Sub.comp (hσ : Sub (Ω := Ω) Δ Γ σ) (hτ : Sub (Ω := Ω) Θ Δ τ) : Sub (Ω := Ω) Θ Γ (Sigma.comp σ τ) := by
  have e := contextual (Ω := Ω) .comp ![Γ, Δ, Θ, σ, τ] (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hσ) (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hτ) (fun i => nomatch i)))
  simpa [Contextual.rule, comprehensionTheory] using e

def Sub.pair (hA : Ty (Ω := Ω) Γ A) (hσ : Sub (Ω := Ω) Δ Γ σ) (ht : Tm (Ω := Ω) Δ (subTy A σ) t) :
    Sub (Ω := Ω) Δ (Sigma.extend Γ A) (Sigma.pairSub A σ t) := by
  have e := structural (Ω := Ω) .pairing ![Γ, Δ, A, σ, t]
    (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hA) (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hσ) (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using ht) (fun i => nomatch i))))
  simpa [Contextual.rule, comprehensionTheory] using e

def Tm.subComp (ht : Tm (Ω := Ω) Γ A t) (hσ : Sub (Ω := Ω) Δ Γ σ)
    (hτ : Sub (Ω := Ω) Θ Δ τ) :
    Equal (Ω := Ω) (subTm (subTm t σ) τ) (subTm t (Sigma.comp σ τ)) := by
  have e := contextual (Ω := Ω) .subTmComp ![Γ, Δ, Θ, A, t, σ, τ]
    (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using ht) (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hσ) (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hτ) (fun i => nomatch i))))
  simpa [Contextual.rule, comprehensionTheory] using e


def Ty.subComp (hA : Ty (Ω := Ω) Γ A) (hσ : Sub (Ω := Ω) Δ Γ σ) (hτ : Sub (Ω := Ω) Θ Δ τ) : Equal (Ω := Ω) (subTy (subTy A σ) τ) (subTy A (Sigma.comp σ τ)) := by
  have e := contextual (Ω := Ω) .subTyComp ![Γ, Δ, Θ, A, σ, τ] (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hA) (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hσ) (Fin.cases (by simpa [Contextual.rule, comprehensionTheory] using hτ) (fun i => nomatch i))))
  simpa [Contextual.rule, comprehensionTheory] using e

def Tm.convert (ht : Tm (Ω := Ω) Γ A t) (e : Equal (Ω := Ω) A B) : Tm (Ω := Ω) Γ B t :=
  Derivation.conversion (T := theory) (Sum.inl (Sum.inl Predicate.term))
    (Fin.cases (.reflexive Γ) (Fin.cases e (Fin.cases (.reflexive t) (fun i => nomatch i)))) ht

def Equal.extend {g g' a a' : Expression V} (hg : Equal (Ω := Ω) g g')
    (ha : Equal (Ω := Ω) a a') : Equal (Ω := Ω) (Sigma.extend g a) (Sigma.extend g' a') :=
  Derivation.congruence (T := theory) (.inl (.inl .extend))
    (Fin.cases hg (Fin.cases ha (fun i => nomatch i)))

def Equal.subTm {t t' s s' : Expression V} (ht : Equal (Ω := Ω) t t')
    (hs : Equal (Ω := Ω) s s') : Equal (Ω := Ω) (Sigma.subTm t s) (Sigma.subTm t' s') :=
  Derivation.congruence (T := theory) (.inl (.inl .subTm))
    (Fin.cases ht (Fin.cases hs (fun i => nomatch i)))

def Sub.resource (hσ : Sub (Ω := Ω) Δ Γ σ) (e : Equal (Ω := Ω) Δ Θ) : Sub (Ω := Ω) Θ Γ σ :=
  Derivation.conversion (T := theory) (.inl (.inl .substitution))
    (Fin.cases e (Fin.cases (.reflexive Γ) (Fin.cases (.reflexive σ) (fun i => nomatch i)))) hσ

def Sub.lift (hσ : Sub (Ω := Ω) Δ Γ σ) (hA : Ty (Ω := Ω) Γ A) :
    Sub (Ω := Ω) (extend Δ (subTy A σ)) (extend Γ A) (Sigma.lift Δ A σ) :=
  Sub.pair hA (hσ.comp (hA.substitute hσ).weaken)
    ((hA.substitute hσ).generic.convert (hA.subComp hσ (hA.substitute hσ).weaken))

/-- The source map has its domain converted by the admitted formation equality. -/
def Sub.sumLift (hσ : Sub (Ω := Ω) Δ Γ σ) (hA : Ty (Ω := Ω) Γ A)
    (hB : Ty (Ω := Ω) (extend Γ A) B) :
    Sub (Ω := Ω) (extend Δ (Sigma.sigma (subTy A σ) (subTy B (Sigma.lift Δ A σ))))
      (extend Γ (Sigma.sigma A B)) (Sigma.lift Δ (Sigma.sigma A B) σ) :=
  (hσ.lift (hA.sigma hB)).resource (Equal.extend (.reflexive Δ) (hA.sigmaSub hB hσ))

/-- The new branch is typed at the rebuilt motive, by the admitted branch-type
comparison. Neither motive nor branch typing is supplied again by the author. -/
def Tm.reindexBranch (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (hC : Ty (Ω := Ω) (extend Γ (Sigma.sigma A B)) C)
    (hd : Tm (Ω := Ω) (branchContext Γ A B) (subTy C (Sigma.pack A B)) d)
    (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Tm (Ω := Ω) (branchContext Δ (subTy A σ) (subTy B (Sigma.lift Δ A σ)))
      (subTy (subTy C (Sigma.lift Δ (Sigma.sigma A B) σ))
        (Sigma.pack (subTy A σ) (subTy B (Sigma.lift Δ A σ))))
      (subTm d (Sigma.lift (extend Δ (subTy A σ)) B (Sigma.lift Δ A σ))) :=
  (hd.substitute ((hσ.lift hA).lift hB)).convert (Tm.branchType hA hB hC hd hσ)

/-- Two successive arbitrary base substitutions rebuild the sum, motive and
branch twice. This source proof composes two admitted naturality derivations. -/
def Tm.splitSubComp (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (hC : Ty (Ω := Ω) (extend Γ (Sigma.sigma A B)) C)
    (hd : Tm (Ω := Ω) (branchContext Γ A B) (subTy C (Sigma.pack A B)) d)
    (hσ : Sub (Ω := Ω) Δ Γ σ) (hτ : Sub (Ω := Ω) Θ Δ τ) :
    let A₁ := subTy A σ
    let B₁ := subTy B (Sigma.lift Δ A σ)
    let d₁ := subTm d (Sigma.lift (extend Δ A₁) B (Sigma.lift Δ A σ))
    Equal (Ω := Ω)
      (subTm (subTm (Sigma.split A B d) (Sigma.lift Δ (Sigma.sigma A B) σ))
        (Sigma.lift Θ (Sigma.sigma A₁ B₁) τ))
      (Sigma.split (subTy A₁ τ) (subTy B₁ (Sigma.lift Θ A₁ τ))
        (subTm d₁ (Sigma.lift (extend Θ (subTy A₁ τ)) B₁ (Sigma.lift Θ A₁ τ)))) := by
  have hA₁ := hA.substitute hσ
  have hB₁ := hB.substitute (hσ.lift hA)
  have hC₁ := hC.substitute (hσ.sumLift hA hB)
  have hd₁ := Tm.reindexBranch hA hB hC hd hσ
  exact (Equal.subTm (Tm.splitSub hA hB hC hd hσ) (.reflexive _)).transitive
    (Tm.splitSub hA₁ hB₁ hC₁ hd₁ hτ)

def Tm.pairSecond (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (ha : Tm (Ω := Ω) Γ A a)
    (hb : Tm (Ω := Ω) Γ (subTy B (pairSub A (identitySub Γ) a)) b)
    (hσ : Sub (Ω := Ω) Δ Γ σ) : Equal (Ω := Ω)
      (subTy (subTy B (pairSub A (identitySub Γ) a)) σ)
      (subTy (subTy B (Sigma.lift Δ A σ))
        (pairSub (subTy A σ) (identitySub Δ) (subTm a σ))) := by
  have e := stable (Ω := Ω) .pairSecond ![Γ, A, B, a, b, Δ, σ]
    (Fin.cases (by simpa [rule] using hA) (Fin.cases (by simpa [rule] using hB)
      (Fin.cases (by simpa [rule] using ha) (Fin.cases (by simpa [rule] using hb)
        (Fin.cases (by simpa [rule] using hσ) (fun i => nomatch i))))))
  simpa [rule] using e

/-- Pair introduction can be rebuilt after two arbitrary substitutions; the
second component's dependent typing is reconstructed at each step. -/
def Tm.pairSubComp (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (ha : Tm (Ω := Ω) Γ A a)
    (hb : Tm (Ω := Ω) Γ (subTy B (pairSub A (identitySub Γ) a)) b)
    (hσ : Sub (Ω := Ω) Δ Γ σ) (hτ : Sub (Ω := Ω) Θ Δ τ) :
    Equal (Ω := Ω) (subTm (subTm (Sigma.pair Γ A B a b) σ) τ)
      (Sigma.pair Θ (subTy (subTy A σ) τ)
        (subTy (subTy B (Sigma.lift Δ A σ)) (Sigma.lift Θ (subTy A σ) τ))
        (subTm (subTm a σ) τ) (subTm (subTm b σ) τ)) := by
  have hA₁ := hA.substitute hσ
  have hB₁ := hB.substitute (hσ.lift hA)
  have ha₁ := ha.substitute hσ
  have hb₁ := (hb.substitute hσ).convert (Tm.pairSecond hA hB ha hb hσ)
  exact (Equal.subTm (Tm.pairReindex hA hB ha hb hσ) (.reflexive τ)).transitive
    (Tm.pairReindex hA₁ hB₁ ha₁ hb₁ hτ)

/-- The successive reconstruction also agrees with the composite source map.
The inherited substitution-composition rule supplies this final step. -/
def Tm.splitSubComposite (hA : Ty (Ω := Ω) Γ A) (hB : Ty (Ω := Ω) (extend Γ A) B)
    (hC : Ty (Ω := Ω) (extend Γ (Sigma.sigma A B)) C)
    (hd : Tm (Ω := Ω) (branchContext Γ A B) (subTy C (Sigma.pack A B)) d)
    (hσ : Sub (Ω := Ω) Δ Γ σ) (hτ : Sub (Ω := Ω) Θ Δ τ) :
    let A₁ := subTy A σ
    let B₁ := subTy B (Sigma.lift Δ A σ)
    let d₁ := subTm d (Sigma.lift (extend Δ A₁) B (Sigma.lift Δ A σ))
    Equal (Ω := Ω)
      (subTm (Sigma.split A B d) (comp (Sigma.lift Δ (Sigma.sigma A B) σ)
        (Sigma.lift Θ (Sigma.sigma A₁ B₁) τ)))
      (Sigma.split (subTy A₁ τ) (subTy B₁ (Sigma.lift Θ A₁ τ))
        (subTm d₁ (Sigma.lift (extend Θ (subTy A₁ τ)) B₁ (Sigma.lift Θ A₁ τ)))) := by
  have hA₁ := hA.substitute hσ
  have hB₁ := hB.substitute (hσ.lift hA)
  exact ((Tm.split hA hB hC hd).subComp (hσ.sumLift hA hB)
    (hτ.sumLift hA₁ hB₁)).symmetric.transitive (Tm.splitSubComp hA hB hC hd hσ hτ)

end SquareKit.Internal.DependentJudgments.Sigma.Reindexing
