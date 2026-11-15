import SquareKit.DependentMetavariableCertificates

namespace SquareKit.DependentPairJudgments.CertificateEnvironment
open DependentTheoryMaps DependentPairPresentations
variable {S : Signature} {R : Rules.{1,1} (Judgment S)}
  {I : Type} {premise : I → Judgment S}

abbrev Proof (Γ : Context S V) (φ : Form S V) := MetavariableCertificate R premise ⟨V, Γ, φ⟩

/-- Reuse a proof tree after interpreting its open leaves as certificates. -/
def replay {H : Judgment S → Type}
    (hypotheses : ∀ j, H j → MetavariableCertificate R premise j) :
    {j : Judgment S} → Derivation R H j → MetavariableCertificate R premise j
  | _, .hyp h => hypotheses _ h
  | _, .rule r children => .rule r (fun i => replay hypotheses (children i))

/-- Every component is checked in the destination telescope at its substituted
source type. In particular this retains the proof of a selected component. -/
structure Env (Γ : Context S V) (Δ : Context S W) (σ : V → Expr S W) where
  context : Proof (R := R) (premise := premise) Δ .ctx
  component : ∀ v, Proof (R := R) (premise := premise) Δ (.term (σ v) (Expr.subst σ (Γ.lookup v)))

variable (structural : TheoryMap (structuralRules S) R id)

def rule (r : StructuralRule S)
    (children : (i : Fin (StructuralRule.schema r).premises.length) →
      MetavariableCertificate R premise ((StructuralRule.schema r).premises.get i)) :
    MetavariableCertificate R premise (StructuralRule.schema r).conclusion :=
  replay (fun _ h => h.property ▸ children h.val) (structural.certificate r)

def weaken (Γ : Context S V) (A : Expr S V) (φ : Form S V)
    (ctx : Proof (R := R) (premise := premise) Γ .ctx)
    (ty : Proof (R := R) (premise := premise) Γ (.type A))
    (p : Proof (R := R) (premise := premise) Γ φ) :
    Proof (R := R) (premise := premise) (.extend Γ A) (φ.rename Sum.inr) :=
  rule structural (.weaken Γ A φ) (Fin.cases ctx (Fin.cases ty (Fin.cases p (fun i => Fin.elim0 i))))

def identity (Γ : Context S V) (ctx : Proof (R := R) (premise := premise) Γ .ctx) :
    Env (R := R) (premise := premise) Γ Γ Expr.var where
  context := ctx
  component v := by
    change MetavariableCertificate R premise (Judgment.term Γ (.var v) (Expr.subst Expr.var (Γ.lookup v)))
    rw [Expr.subst_id]
    exact rule structural (.variable Γ v) (Fin.cases ctx (fun i => Fin.elim0 i))

/-- Restrict a substitution along the last telescope projection. -/
def restrict {Γ : Context S V} {Δ : Context S W} {A : Expr S V}
    {σ : Fin 1 ⊕ V → Expr S W} (s : Env (R := R) (premise := premise) (.extend Γ A) Δ σ) :
    Env (R := R) (premise := premise) Γ Δ (σ ∘ Sum.inr) where
  context := s.context
  component v := by
    simpa only [Context.lookup, Expr.subst_rename, Function.comp_def] using s.component (.inr v)

/-- Lifting uses weakening and the new variable rule. It does not assume typed
substitution admissibility. The substituted source type must already be formed. -/
def lift {Γ : Context S V} {Δ : Context S W} {σ : V → Expr S W}
    (s : Env (R := R) (premise := premise) Γ Δ σ) (A : Expr S V)
    (ty : Proof (R := R) (premise := premise) Δ (.type (Expr.subst σ A))) :
    Env (R := R) (premise := premise) (.extend Γ A) (.extend Δ (Expr.subst σ A)) (Expr.lift σ) where
  context := rule structural (.extend Δ (Expr.subst σ A)) (Fin.cases s.context (Fin.cases ty (fun i => Fin.elim0 i)))
  component v := by
    cases v with
    | inl i =>
      have c := rule structural (.extend Δ (Expr.subst σ A)) (premise := premise) (Fin.cases s.context (Fin.cases ty (fun i => Fin.elim0 i)))
      have p := rule structural (.variable (.extend Δ (Expr.subst σ A)) (.inl i))
        (Fin.cases c (fun i => Fin.elim0 i))
      simpa only [StructuralRule.schema, Judgment.term, Context.lookup, Expr.lift, Expr.subst_rename, Expr.rename_subst,
        Function.comp_def] using p
    | inr v =>
      have p := weaken structural Δ (Expr.subst σ A)
        (.term (σ v) (Expr.subst σ (Γ.lookup v))) s.context ty (s.component v)
      simpa only [Context.lookup, Expr.lift, Form.rename, Expr.subst_rename,
        Expr.rename_subst, Function.comp_def] using p

/-- Substitute a selected term for the last variable; old variables are fixed. -/
def single (Γ : Context S V) (A a : Expr S V)
    (ctx : Proof (R := R) (premise := premise) Γ .ctx)
    (term : Proof (R := R) (premise := premise) Γ (.term a A)) :
    Env (R := R) (premise := premise) (.extend Γ A) Γ (Sum.elim (fun _ => a) Expr.var) where
  context := ctx
  component v := by
    cases v with
    | inl i =>
      change Proof Γ (.term a (Expr.subst _ (Expr.rename Sum.inr A)))
      simpa only [Expr.subst_rename, Function.comp_def, Sum.elim_inr, Expr.subst_id] using term
    | inr v =>
      change Proof Γ (.term (.var v) (Expr.subst _ (Expr.rename Sum.inr (Γ.lookup v))))
      have p := rule structural (.variable Γ v) (premise := premise)
        (Fin.cases ctx (fun i => Fin.elim0 i))
      simpa only [Expr.subst_rename, Function.comp_def, Sum.elim_inr, Expr.subst_id, StructuralRule.schema, Judgment.term] using p


/-- Reindex all selected components into an extended destination. -/
def weakenTarget {Γ : Context S V} {Δ : Context S W} {σ : V → Expr S W}
    (env : Env (R := R) (premise := premise) Γ Δ σ) (A : Expr S W)
    (type : Proof (R := R) (premise := premise) Δ (.type A)) :
    Env (R := R) (premise := premise) Γ (.extend Δ A)
      (fun v => Expr.rename Sum.inr (σ v)) where
  context := rule structural (.extend Δ A)
    (Fin.cases env.context (Fin.cases type (fun i => Fin.elim0 i)))
  component v := by
    have p := weaken structural Δ A (.term (σ v) (Expr.subst σ (Γ.lookup v)))
      env.context type (env.component v)
    change Proof (.extend Δ A) (.term (Expr.rename Sum.inr (σ v))
      (Expr.rename Sum.inr (Expr.subst σ (Γ.lookup v)))) at p
    rw [Expr.rename_subst] at p
    exact p

/-- Supply the new source variable at its dependent substituted type. -/
def extendSource {Γ : Context S V} {Δ : Context S W} {σ : V → Expr S W}
    (env : Env (R := R) (premise := premise) Γ Δ σ) (A : Expr S V) (a : Expr S W)
    (term : Proof (R := R) (premise := premise) Δ (.term a (Expr.subst σ A))) :
    Env (R := R) (premise := premise) (.extend Γ A) Δ (Sum.elim (fun _ => a) σ) where
  context := env.context
  component v := by
    cases v with
    | inl i =>
      change Proof Δ (.term a (Expr.subst _ (Expr.rename Sum.inr A)))
      rw [Expr.subst_rename]
      exact term
    | inr v =>
      change Proof Δ (.term (σ v) (Expr.subst _ (Expr.rename Sum.inr (Γ.lookup v))))
      rw [Expr.subst_rename]
      exact env.component v

/-- Use a declared premise under its explicitly checked argument environment. -/
def apply (i : I) {Δ : Context S W} {σ : (premise i).Scope → Expr S W}
    (env : Env (R := R) (premise := premise) (premise i).context Δ σ) :
    MetavariableCertificate R premise ⟨W, Δ, (premise i).form.subst σ⟩ :=
  .apply i Δ σ env.context env.component

end SquareKit.DependentPairJudgments.CertificateEnvironment
