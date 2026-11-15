import SquareKit.DependentPairJudgments

/-! Typed telescope substitutions for the contextual pair experiment. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations

namespace Form

def subst (σ : V → Expr S W) : Form S V → Form S W
  | .ctx => .ctx
  | .type A => .type (Expr.subst σ A)
  | .term a A => .term (Expr.subst σ a) (Expr.subst σ A)
  | .typeEq A B => .typeEq (Expr.subst σ A) (Expr.subst σ B)
  | .termEq a b A => .termEq (Expr.subst σ a) (Expr.subst σ b) (Expr.subst σ A)

@[simp] theorem subst_identity (φ : Form S V) : φ.subst Expr.var = φ := by
  cases φ <;> simp [subst]

@[simp] theorem subst_comp (σ : V → Expr S W) (τ : W → Expr S X) (φ : Form S V) :
    (φ.subst σ).subst τ = φ.subst (fun v => Expr.subst τ (σ v)) := by
  cases φ <;> simp [subst]

@[simp] theorem subst_rename (ρ : V → W) (σ : W → Expr S X) (φ : Form S V) :
    (φ.rename ρ).subst σ = φ.subst (σ ∘ ρ) := by
  cases φ <;> simp [subst, rename]
end Form

abbrev structuralRules (S : Signature) := rulesOf (StructuralRule.schema (S := S))

namespace TypedSubstitution
variable {S : Signature} {R : Rules (Judgment S)} {H : Judgment S → Type}

abbrev Proof (Γ : Context S V) (φ : Form S V) := Derivation R H ⟨V, Γ, φ⟩

/-- Every component is checked in the destination telescope at its substituted
source type. In particular this retains the proof of a selected component. -/
structure Typed (Γ : Context S V) (Δ : Context S W) (σ : V → Expr S W) where
  context : Proof (R := R) (H := H) Δ .ctx
  component : ∀ v, Proof (R := R) (H := H) Δ (.term (σ v) (Expr.subst σ (Γ.lookup v)))

variable (structural : TheoryMap (structuralRules S) R id)

def rule (r : StructuralRule S)
    (premises : (i : Fin (StructuralRule.schema r).premises.length) →
      Derivation R H ((StructuralRule.schema r).premises.get i)) :
    Derivation R H (StructuralRule.schema r).conclusion :=
  (structural.certificate r).graft (fun _ h => h.property ▸ premises h.val)

def weaken (Γ : Context S V) (A : Expr S V) (φ : Form S V)
    (ctx : Proof (R := R) (H := H) Γ .ctx)
    (ty : Proof (R := R) (H := H) Γ (.type A))
    (p : Proof (R := R) (H := H) Γ φ) :
    Proof (R := R) (H := H) (.extend Γ A) (φ.rename Sum.inr) :=
  rule structural (.weaken Γ A φ) (Fin.cases ctx (Fin.cases ty (Fin.cases p (fun i => Fin.elim0 i))))

def identity (Γ : Context S V) (ctx : Proof (R := R) (H := H) Γ .ctx) :
    Typed (R := R) (H := H) Γ Γ Expr.var where
  context := ctx
  component v := by
    change Derivation R H (Judgment.term Γ (.var v) (Expr.subst Expr.var (Γ.lookup v)))
    rw [Expr.subst_id]
    exact rule structural (.variable Γ v) (Fin.cases ctx (fun i => Fin.elim0 i))

/-- Restrict a substitution along the last telescope projection. -/
def restrict {Γ : Context S V} {Δ : Context S W} {A : Expr S V}
    {σ : Fin 1 ⊕ V → Expr S W} (s : Typed (R := R) (H := H) (.extend Γ A) Δ σ) :
    Typed (R := R) (H := H) Γ Δ (σ ∘ Sum.inr) where
  context := s.context
  component v := by
    simpa only [Context.lookup, Expr.subst_rename, Function.comp_def] using s.component (.inr v)

/-- Lifting uses weakening and the new variable rule. It does not assume typed
substitution admissibility. The substituted source type must already be formed. -/
def lift {Γ : Context S V} {Δ : Context S W} {σ : V → Expr S W}
    (s : Typed (R := R) (H := H) Γ Δ σ) (A : Expr S V)
    (ty : Proof (R := R) (H := H) Δ (.type (Expr.subst σ A))) :
    Typed (R := R) (H := H) (.extend Γ A) (.extend Δ (Expr.subst σ A)) (Expr.lift σ) where
  context := rule structural (.extend Δ (Expr.subst σ A)) (Fin.cases s.context (Fin.cases ty (fun i => Fin.elim0 i)))
  component v := by
    cases v with
    | inl i =>
      have c := rule structural (.extend Δ (Expr.subst σ A)) (H := H) (Fin.cases s.context (Fin.cases ty (fun i => Fin.elim0 i)))
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
    (ctx : Proof (R := R) (H := H) Γ .ctx)
    (term : Proof (R := R) (H := H) Γ (.term a A)) :
    Typed (R := R) (H := H) (.extend Γ A) Γ (Sum.elim (fun _ => a) Expr.var) where
  context := ctx
  component v := by
    cases v with
    | inl i =>
      change Proof Γ (.term a (Expr.subst _ (Expr.rename Sum.inr A)))
      simpa only [Expr.subst_rename, Function.comp_def, Sum.elim_inr, Expr.subst_id] using term
    | inr v =>
      change Proof Γ (.term (.var v) (Expr.subst _ (Expr.rename Sum.inr (Γ.lookup v))))
      have p := rule structural (.variable Γ v) (H := H)
        (Fin.cases ctx (fun i => Fin.elim0 i))
      simpa only [Expr.subst_rename, Function.comp_def, Sum.elim_inr, Expr.subst_id, StructuralRule.schema, Judgment.term] using p

/-- Extend the source telescope by a component checked at its dependent image. -/
def extendSource {Γ : Context S V} {Δ : Context S W} {σ : V → Expr S W}
    (env : Typed (R := R) (H := H) Γ Δ σ) (A : Expr S V) (a : Expr S W)
    (term : Proof (R := R) (H := H) Δ (.term a (Expr.subst σ A))) :
    Typed (R := R) (H := H) (.extend Γ A) Δ (Sum.elim (fun _ => a) σ) where
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

/-- The induction predicate retains typed arguments of every open telescope. -/
abbrev Reindexed (j : Judgment S) := ∀ {W : Type} (Δ : Context S W)
  (σ : j.Scope → Expr S W), Typed (R := R) (H := H) j.context Δ σ →
  Proof (R := R) (H := H) Δ (j.form.subst σ)

/-- Per-rule reindexing reconstruction. Its inputs are the recursively
reindexed premises, not a transport operation for arbitrary derivations. -/
structure Local where
  step : ∀ r : R.Label,
    (∀ i : Fin (R.count r), Reindexed (R := R) (H := H) (R.premise r i)) →
    Reindexed (R := R) (H := H) (R.conclusion r)

/-- Substitution is admissible once rule-local reconstruction and the explicit
instantiation action of open hypotheses have been supplied. Closed proofs have
no hypothesis obligation. -/
def substitute (laws : Local (R := R) (H := H))
    (hypotheses : ∀ j, H j → Reindexed (R := R) (H := H) j) :
    {j : Judgment S} → Derivation R H j → Reindexed (R := R) (H := H) j
  | _, .hyp h => hypotheses _ h
  | _, .rule r ds => laws.step r (fun i => substitute laws hypotheses (ds i))

/-- Structural reconstruction has no constructor-specific substitution axiom. -/
def structuralStep (r : StructuralRule S)
    (rec : ∀ i : Fin (StructuralRule.schema r).premises.length,
      Reindexed (R := R) (H := H) ((StructuralRule.schema r).premises.get i)) :
    Reindexed (R := R) (H := H) (StructuralRule.schema r).conclusion := by
  cases r with
  | empty => dsimp [StructuralRule.schema, Judgment.ctx, Judgment.type, Judgment.term, Judgment.typeEq, Judgment.termEq] at rec ⊢; intro W Δ σ s; exact s.context
  | extend Γ A => dsimp [StructuralRule.schema, Judgment.ctx, Judgment.type, Judgment.term, Judgment.typeEq, Judgment.termEq] at rec ⊢; intro W Δ σ s; exact s.context
  | «variable» Γ v => dsimp [StructuralRule.schema, Judgment.ctx, Judgment.type, Judgment.term, Judgment.typeEq, Judgment.termEq] at rec ⊢; intro W Δ σ s; exact s.component v
  | weaken Γ A φ =>
      dsimp [StructuralRule.schema, Judgment.ctx, Judgment.type, Judgment.term, Judgment.typeEq, Judgment.termEq] at rec ⊢
      intro W Δ σ s
      change Proof Δ ((φ.rename Sum.inr).subst σ)
      rw [Form.subst_rename]
      exact rec 2 Δ (σ ∘ Sum.inr) (restrict s)
  | typeRefl Γ A =>
      dsimp [StructuralRule.schema, Judgment.ctx, Judgment.type, Judgment.term, Judgment.typeEq, Judgment.termEq] at rec ⊢
      intro W Δ σ s
      exact rule structural (.typeRefl Δ (Expr.subst σ A))
        (Fin.cases (rec 0 Δ σ s) (fun i => Fin.elim0 i))
  | typeSymm Γ A B =>
      dsimp [StructuralRule.schema, Judgment.ctx, Judgment.type, Judgment.term, Judgment.typeEq, Judgment.termEq] at rec ⊢
      intro W Δ σ s
      exact rule structural (.typeSymm Δ (Expr.subst σ A) (Expr.subst σ B))
        (Fin.cases (rec 0 Δ σ s) (fun i => Fin.elim0 i))
  | typeTrans Γ A B C =>
      dsimp [StructuralRule.schema, Judgment.ctx, Judgment.type, Judgment.term, Judgment.typeEq, Judgment.termEq] at rec ⊢
      intro W Δ σ s
      exact rule structural (.typeTrans Δ (Expr.subst σ A) (Expr.subst σ B) (Expr.subst σ C))
        (Fin.cases (rec 0 Δ σ s) (Fin.cases (rec 1 Δ σ s) (fun i => Fin.elim0 i)))
  | termRefl Γ a A =>
      dsimp [StructuralRule.schema, Judgment.ctx, Judgment.type, Judgment.term, Judgment.typeEq, Judgment.termEq] at rec ⊢
      intro W Δ σ s
      exact rule structural (.termRefl Δ (Expr.subst σ a) (Expr.subst σ A))
        (Fin.cases (rec 0 Δ σ s) (fun i => Fin.elim0 i))
  | termSymm Γ a b A =>
      dsimp [StructuralRule.schema, Judgment.ctx, Judgment.type, Judgment.term, Judgment.typeEq, Judgment.termEq] at rec ⊢
      intro W Δ σ s
      exact rule structural (.termSymm Δ (Expr.subst σ a) (Expr.subst σ b) (Expr.subst σ A))
        (Fin.cases (rec 0 Δ σ s) (fun i => Fin.elim0 i))
  | termTrans Γ a b c A =>
      dsimp [StructuralRule.schema, Judgment.ctx, Judgment.type, Judgment.term, Judgment.typeEq, Judgment.termEq] at rec ⊢
      intro W Δ σ s
      exact rule structural (.termTrans Δ (Expr.subst σ a) (Expr.subst σ b)
        (Expr.subst σ c) (Expr.subst σ A))
        (Fin.cases (rec 0 Δ σ s) (Fin.cases (rec 1 Δ σ s) (fun i => Fin.elim0 i)))
  | convert Γ a A B =>
      dsimp [StructuralRule.schema, Judgment.ctx, Judgment.type, Judgment.term, Judgment.typeEq, Judgment.termEq] at rec ⊢
      intro W Δ σ s
      exact rule structural (.convert Δ (Expr.subst σ a) (Expr.subst σ A) (Expr.subst σ B))
        (Fin.cases (rec 0 Δ σ s) (Fin.cases (rec 1 Δ σ s) (fun i => Fin.elim0 i)))
  | convertEq Γ a b A B =>
      dsimp [StructuralRule.schema, Judgment.ctx, Judgment.type, Judgment.term, Judgment.typeEq, Judgment.termEq] at rec ⊢
      intro W Δ σ s
      exact rule structural (.convertEq Δ (Expr.subst σ a) (Expr.subst σ b)
        (Expr.subst σ A) (Expr.subst σ B))
        (Fin.cases (rec 0 Δ σ s) (Fin.cases (rec 1 Δ σ s) (fun i => Fin.elim0 i)))
  | familyCong Γ A B a b =>
      dsimp [StructuralRule.schema, Judgment.ctx, Judgment.type, Judgment.term, Judgment.typeEq, Judgment.termEq] at rec ⊢
      intro W Δ σ s
      have pa := rec 1 Δ σ s
      have pb := rec 2 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural s A pa)
      have pe := rec 3 Δ σ s
      have p := rule structural (.familyCong Δ (Expr.subst σ A)
        (Expr.subst (Expr.lift σ) B) (Expr.subst σ a) (Expr.subst σ b))
        (Fin.cases s.context (Fin.cases pa (Fin.cases pb (Fin.cases pe (fun i => Fin.elim0 i)))))
      change Proof Δ (.typeEq (Expr.subst σ (Elimination.instantiate B a))
        (Expr.subst σ (Elimination.instantiate B b)))
      rw [Elimination.subst_instantiate, Elimination.subst_instantiate]
      exact p

end TypedSubstitution
end SquareKit.DependentPairJudgments
