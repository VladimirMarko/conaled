import SquareKit.DependentCertificateEnvironments
import SquareKit.DependentPairEliminationJudgments

/-! Typed metavariable certificates for projections defined by dependent split. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations Elimination Judgment

namespace MetavariableCertificate
variable {S : Signature} {R : Rules.{1,1} (Judgment S)} {I : Type}
  {premise : I → Judgment S} {H : Judgment S → Type}

/-- Replay an ordinary proof tree, replacing its leaves by typed certificates. -/
def ofDerivation (hypotheses : ∀ j, H j → MetavariableCertificate R premise j) :
    {j : Judgment S} → Derivation R H j → MetavariableCertificate R premise j
  | _, .hyp h => hypotheses _ h
  | _, .rule r children => .rule r (fun i => ofDerivation hypotheses (children i))

end MetavariableCertificate

@[simp] theorem secondMotive_rename (ρ : V → W) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) :
    Expr.rename (Sum.map id ρ) (secondMotive A B) =
      secondMotive (Expr.rename ρ A) (Expr.rename (Sum.map id ρ) B) := by
  have h : (Expr.lift (n := 1) (fun v : Fin 1 ⊕ V => (Expr.var (S := eliminationSignature) (Sum.map id ρ v))) ∘ Sum.map id Sum.inr : Fin 1 ⊕ V → EExpr (Fin 1 ⊕ (Fin 1 ⊕ W))) =
      (fun v => Expr.var (Sum.map id Sum.inr v)) ∘ Sum.map id ρ := by
    funext v
    cases v <;> rfl
  rw [← Expr.subst_vars]
  simp only [secondMotive, subst_instantiate, subst_first, Expr.subst_rename, h,
    Expr.subst_vars, Expr.rename_comp, Function.comp_def, Expr.rename]
  rfl

@[simp] theorem second_branch_type (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) :
    branchType A B (secondMotive A B) =
      instantiate (Expr.rename (Sum.map id (Sum.inr ∘ Sum.inr)) B)
        (Elimination.first (Expr.rename (Sum.inr ∘ Sum.inr) A)
          (Expr.rename (Sum.map id (Sum.inr ∘ Sum.inr)) B) (branchPair A B)) := by
  rw [branchType, secondMotive_rename, secondMotive_at]

namespace ECertificate
variable {I : Type} {premise : I → Judgment eliminationSignature}
  {Γ : Context eliminationSignature V} {A : EExpr V} {B : EExpr (Fin 1 ⊕ V)}
abbrev Cert := MetavariableCertificate Eη premise

def structural (r : StructuralRule eliminationSignature)
    (ps : ∀i : Fin (StructuralRule.schema r).premises.length,
      Cert (premise := premise) ((StructuralRule.schema r).premises.get i)) :
    Cert (premise := premise) (StructuralRule.schema r).conclusion :=
  MetavariableCertificate.rule (R := Eη) (.inl r) ps

def primitive (r : EliminationRule)
    (ps : ∀i : Fin (EliminationRule.schema r).premises.length,
      Cert (premise := premise) ((EliminationRule.schema r).premises.get i)) :
    Cert (premise := premise) (EliminationRule.schema r).conclusion :=
  MetavariableCertificate.rule (R := Eη) (.inr r) ps

def extend (hΓ : Cert (premise := premise) (ctx Γ)) (hA : Cert (premise := premise) (type Γ A)) :
    Cert (premise := premise) (ctx (Γ.extend A)) :=
  structural (.extend Γ A) (Fin.cases hΓ (Fin.cases hA (fun i => nomatch i)))

def variableTerm (hΓ : Cert (premise := premise) (ctx Γ)) (v : V) :
    Cert (premise := premise) (term Γ (.var v) (Γ.lookup v)) :=
  structural (.variable Γ v) (Fin.cases hΓ (fun i => nomatch i))

def weaken (φ : Form eliminationSignature V) (hΓ : Cert (premise := premise) (ctx Γ))
    (hA : Cert (premise := premise) (type Γ A))
    (hφ : Cert (premise := premise) ⟨_, Γ, φ⟩) :
    Cert (premise := premise) ⟨_, Γ.extend A, φ.rename Sum.inr⟩ :=
  structural (.weaken Γ A φ) (Fin.cases hΓ (Fin.cases hA (Fin.cases hφ (fun i => nomatch i))))

def formation (hΓ : Cert (premise := premise) (ctx Γ)) (hA : Cert (premise := premise) (type Γ A))
    (hB : Cert (premise := premise) (type (Γ.extend A) B)) :
    Cert (premise := premise) (type Γ (S A B)) :=
  primitive (.formation Γ A B) (Fin.cases hΓ (Fin.cases hA (Fin.cases hB (fun i => nomatch i))))

private def fromSchema (schema : Schema eliminationSignature)
    (d : Derivation Eη (fun j => {i : Fin schema.premises.length // schema.premises.get i = j})
      schema.conclusion)
    (ps : ∀ i : Fin schema.premises.length, Cert (premise := premise) (schema.premises.get i)) :
    Cert (premise := premise) schema.conclusion :=
  MetavariableCertificate.ofDerivation (fun _ h => h.property ▸ ps h.val) d

def first (hΓ : Cert (premise := premise) (ctx Γ)) (hA : Cert (premise := premise) (type Γ A))
    (hB : Cert (premise := premise) (type (Γ.extend A) B)) (p : EExpr V)
    (hp : Cert (premise := premise) (term Γ p (S A B))) :
    Cert (premise := premise) (term Γ (Elimination.first A B p) A) := by
  let schema : Schema eliminationSignature :=
    ⟨[ctx Γ, type Γ A, type (Γ.extend A) B, term Γ p (S A B)],
      term Γ (Elimination.first A B p) A⟩
  apply fromSchema schema
    (EDerivation.first (.hyp ⟨(0 : Fin 4), rfl⟩) (.hyp ⟨(1 : Fin 4), rfl⟩)
      (.hyp ⟨(2 : Fin 4), rfl⟩) p (.hyp ⟨(3 : Fin 4), rfl⟩))
  exact Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases hp (fun i => nomatch i))))

def firstBeta (hΓ : Cert (premise := premise) (ctx Γ)) (hA : Cert (premise := premise) (type Γ A))
    (hB : Cert (premise := premise) (type (Γ.extend A) B)) (a b : EExpr V)
    (ha : Cert (premise := premise) (term Γ a A))
    (hb : Cert (premise := premise) (term Γ b (instantiate B a))) :
    Cert (premise := premise) (termEq Γ (Elimination.first A B (Elimination.pack A B a b)) a A) := by
  let schema : Schema eliminationSignature :=
    ⟨[ctx Γ, type Γ A, type (Γ.extend A) B, term Γ a A, term Γ b (instantiate B a)],
      termEq Γ (Elimination.first A B (Elimination.pack A B a b)) a A⟩
  apply fromSchema schema
    (EDerivation.firstBeta (.hyp ⟨(0 : Fin 5), rfl⟩) (.hyp ⟨(1 : Fin 5), rfl⟩)
      (.hyp ⟨(2 : Fin 5), rfl⟩) a b (.hyp ⟨(3 : Fin 5), rfl⟩) (.hyp ⟨(4 : Fin 5), rfl⟩))
  exact Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases ha (Fin.cases hb (fun i => nomatch i)))))

private def structuralInclusion : TheoryMap (structuralRules eliminationSignature) Eη id where
  certificate r := Derivation.rule (R := Eη) (.inl r) (fun i => .hyp ⟨i, rfl⟩)

/-- A family premise may be applied only to an environment of typed arguments. -/
abbrev Family (Γ : Context eliminationSignature V) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) :=
  ∀ {W} (Δ : Context eliminationSignature W) (σ : Fin 1 ⊕ V → EExpr W),
    CertificateEnvironment.Env (R := Eη) (premise := premise) (Γ.extend A) Δ σ →
      Cert (premise := premise) (type Δ (Expr.subst σ B))

private def familyRename (family : Family (premise := premise) Γ A B)
    {Δ : Context eliminationSignature W} (ρ : V → W)
    (env : CertificateEnvironment.Env (R := Eη) (premise := premise) Γ Δ (fun v => .var (ρ v)))
    (hA : Cert (premise := premise) (type Δ (Expr.rename ρ A))) :
    Cert (premise := premise) (type (Δ.extend (Expr.rename ρ A)) (Expr.rename (Sum.map id ρ) B)) := by
  have hA' : Cert (premise := premise) (type Δ (Expr.subst (fun v => .var (ρ v)) A)) := by
    simpa only [Expr.subst_vars] using hA
  have h := family _ _ (CertificateEnvironment.lift structuralInclusion env A hA')
  have eq : Expr.lift (n := 1) (fun v => (Expr.var (S := eliminationSignature) (ρ v))) =
      (fun v => Expr.var (Sum.map id ρ v)) := by funext v; cases v <;> rfl
  simpa only [Expr.subst_vars, eq] using h

/-- The motive for the derived second projection is a genuine family application. -/
def secondMotiveType (hΓ : Cert (premise := premise) (ctx Γ))
    (hA : Cert (premise := premise) (type Γ A))
    (hB : Cert (premise := premise) (type (Γ.extend A) B))
    (family : Family (premise := premise) Γ A B) :
    Cert (premise := premise) (type (Γ.extend (S A B)) (secondMotive A B)) := by
  have hS := formation hΓ hA hB
  have env := CertificateEnvironment.weakenTarget structuralInclusion
    (CertificateEnvironment.identity structuralInclusion Γ hΓ) (S A B) hS
  have hAw : Cert (premise := premise) (type (Γ.extend (S A B)) (Expr.rename Sum.inr A)) :=
    weaken (.type A) hΓ hS hA
  have hBw := familyRename family Sum.inr env hAw
  have hp : Cert (premise := premise) (term (Γ.extend (S A B)) (.var (.inl 0))
      (S (Expr.rename Sum.inr A) (Expr.rename (Sum.map id Sum.inr) B))) := by
    have eq : Expr.rename (Sum.inr : V → Fin 1 ⊕ V) (S A B) =
        S (Expr.rename Sum.inr A) (Expr.rename (Sum.map id Sum.inr) B) := by
      rw [← Expr.subst_vars, subst_S]
      have liftEq : Expr.lift (n := 1) (fun v : V => (Expr.var (S := eliminationSignature) (Sum.inr (α := Fin 1) v))) =
          (fun v => Expr.var (Sum.map id Sum.inr v)) := by funext v; cases v <;> rfl
      rw [liftEq, Expr.subst_vars, Expr.subst_vars]
    simpa only [Context.lookup, eq] using variableTerm env.context (Sum.inl (0 : Fin 1))

  have hf := first env.context hAw hBw _ hp
  have hf' : Cert (premise := premise) (term (Γ.extend (S A B))
      (Elimination.first (Expr.rename Sum.inr A) (Expr.rename (Sum.map id Sum.inr) B) (.var (.inl 0)))
      (Expr.subst (fun v => .var (Sum.inr v)) A)) := by
    simpa only [Expr.subst_vars] using hf
  have inst := family _ _ (CertificateEnvironment.extendSource env A _ hf')
  have eq (f : EExpr (Fin 1 ⊕ V)) :
      instantiate (Expr.rename (Sum.map id Sum.inr) B) f =
        Expr.subst (Sum.elim (fun _ : Fin 1 => f) (fun v => Expr.var (Sum.inr v))) B := by
    rw [instantiate, Expr.subst_rename]
    congr 1
    funext v
    cases v <;> rfl
  rw [secondMotive, eq]
  exact inst

/-- The second branch is converted along first beta before split is available. -/
def secondBranch (hΓ : Cert (premise := premise) (ctx Γ))
    (hA : Cert (premise := premise) (type Γ A))
    (hB : Cert (premise := premise) (type (Γ.extend A) B))
    (family : Family (premise := premise) Γ A B) :
    Cert (premise := premise) (term (branchContext Γ A B)
      (Expr.rename flattenToNested (.var (.inl 1))) (branchType A B (secondMotive A B))) := by
  let ρ : V → Fin 1 ⊕ (Fin 1 ⊕ V) := Sum.inr ∘ Sum.inr
  have hΓA := extend hΓ hA
  have hΓAB := extend hΓA hB
  have hAw := weaken (.type A) hΓ hA hA
  have hA2 : Cert (premise := premise) (type (branchContext Γ A B) (Expr.rename ρ A)) := by
    simpa only [Form.rename, Expr.rename_comp, ρ, branchContext, type] using weaken (.type (Expr.rename Sum.inr A)) hΓA hB hAw
  have envA := CertificateEnvironment.weakenTarget structuralInclusion
    (CertificateEnvironment.identity structuralInclusion Γ hΓ) A hA
  have envAB := CertificateEnvironment.weakenTarget structuralInclusion envA B hB
  have hB2 := familyRename family ρ envAB hA2
  have hx : Cert (premise := premise) (term (branchContext Γ A B)
      (.var (.inr (.inl 0))) (Expr.rename ρ A)) := by
    simpa only [Context.lookup, Expr.rename_comp, ρ, branchContext] using variableTerm hΓAB (Sum.inr (Sum.inl (0 : Fin 1)))
  have hy : Cert (premise := premise) (term (branchContext Γ A B) (.var (.inl 0))
      (instantiate (Expr.rename (Sum.map id ρ) B) (.var (.inr (.inl 0))))) := by
    simpa only [ρ, branch_B_at_x, Context.lookup, branchContext] using variableTerm hΓAB (Sum.inl (0 : Fin 1))
  have beta := firstBeta hΓAB hA2 hB2 (.var (.inr (.inl 0))) (.var (.inl 0)) hx hy
  have eq := structural (.familyCong (branchContext Γ A B) (Expr.rename ρ A)
    (Expr.rename (Sum.map id ρ) B)
    (Elimination.first (Expr.rename ρ A) (Expr.rename (Sum.map id ρ) B) (branchPair A B))
    (.var (.inr (.inl 0))))
    (Fin.cases hΓAB (Fin.cases hA2 (Fin.cases hB2 (Fin.cases beta (fun i => nomatch i)))))
  have rev := structural (.typeSymm (branchContext Γ A B) _ _)
    (Fin.cases eq (fun i => nomatch i))
  have converted := structural (.convert (branchContext Γ A B) (.var (.inl 0)) _ _)
    (Fin.cases hy (Fin.cases rev (fun i => nomatch i)))
  simpa [StructuralRule.schema, second_branch_type, flattenToNested, Expr.rename, ρ]
    using converted

def second (hΓ : Cert (premise := premise) (ctx Γ))
    (hA : Cert (premise := premise) (type Γ A))
    (hB : Cert (premise := premise) (type (Γ.extend A) B))
    (family : Family (premise := premise) Γ A B) (p : EExpr V)
    (hp : Cert (premise := premise) (term Γ p (S A B))) :
    Cert (premise := premise) (term Γ (Elimination.second A B p) (instantiate B (Elimination.first A B p))) := by
  have hD := secondMotiveType hΓ hA hB family
  have he := secondBranch hΓ hA hB family
  have result := primitive (.split Γ A B (secondMotive A B) (.var (.inl 1)) p)
    (Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases hD (Fin.cases he (Fin.cases hp (fun i => nomatch i)))))))
  change Cert (term Γ (Elimination.second A B p) (instantiate (secondMotive A B) p)) at result
  rw [secondMotive_at] at result
  exact result

def secondBeta (hΓ : Cert (premise := premise) (ctx Γ))
    (hA : Cert (premise := premise) (type Γ A))
    (hB : Cert (premise := premise) (type (Γ.extend A) B))
    (family : Family (premise := premise) Γ A B) (a b : EExpr V)
    (ha : Cert (premise := premise) (term Γ a A))
    (hb : Cert (premise := premise) (term Γ b (instantiate B a))) :
    Cert (premise := premise) (termEq Γ (Elimination.second A B (Elimination.pack A B a b)) b (instantiate B a)) := by
  have hD := secondMotiveType hΓ hA hB family
  have he := secondBranch hΓ hA hB family
  have beta := primitive (.splitBeta Γ A B (secondMotive A B) (.var (.inl 1)) a b)
    (Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases hD (Fin.cases he (Fin.cases ha (Fin.cases hb (fun i => nomatch i))))))))
  change Cert (termEq Γ (Elimination.second A B (Elimination.pack A B a b)) b
    (instantiate (secondMotive A B) (Elimination.pack A B a b))) at beta
  rw [secondMotive_at] at beta
  have firstEq := firstBeta hΓ hA hB a b ha hb
  have typeEq := structural (.familyCong Γ A B (Elimination.first A B (Elimination.pack A B a b)) a)
    (Fin.cases hΓ (Fin.cases hA (Fin.cases hB (Fin.cases firstEq (fun i => nomatch i)))))
  have result := structural (.convertEq Γ (Elimination.second A B (Elimination.pack A B a b)) b
    (instantiate B (Elimination.first A B (Elimination.pack A B a b))) (instantiate B a))
    (Fin.cases beta (Fin.cases typeEq (fun i => nomatch i)))
  exact result

end ECertificate
end SquareKit.DependentPairJudgments
