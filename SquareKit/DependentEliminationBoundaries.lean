import SquareKit.DependentEliminationPresentationSubstitution
import SquareKit.DependentProjectionBoundaries
import SquareKit.DependentPairEliminationCertificates
import SquareKit.DependentCertificateEmbedding

namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations Elimination TypedSubstitution

private def branchArguments (a b : EExpr V) : Fin 1 ⊕ (Fin 1 ⊕ V) → EExpr V :=
  Sum.elim (fun _ => b) (Sum.elim (fun _ => a) Expr.var)

private theorem branchType_arguments (A : EExpr V) (B D : EExpr (Fin 1 ⊕ V)) (a b : EExpr V) :
    Expr.subst (branchArguments a b) (branchType A B D) = instantiate D (pack A B a b) := by
  simp only [branchType, branchPair, subst_instantiate, subst_pack, Expr.subst_rename]
  have h : (Expr.lift (branchArguments a b) ∘ Sum.map id (Sum.inr ∘ Sum.inr)) =
      (Expr.var : Fin 1 ⊕ V → EExpr (Fin 1 ⊕ V)) := by
    funext v; cases v <;> rfl
  have k : branchArguments a b ∘ (Sum.inr ∘ Sum.inr) = (Expr.var : V → EExpr V) := rfl
  rw [h, k, Expr.subst_id, Expr.subst_id, Expr.subst_id]
  rfl

private theorem branchTerm_arguments (e : EExpr (Fin 2 ⊕ V)) (a b : EExpr V) :
    Expr.subst (branchArguments a b) (Expr.rename flattenToNested e) = branchAt e a b := by
  rw [Expr.subst_rename]
  congr 1
  funext v
  cases v with
  | inl i => fin_cases i <;> rfl
  | inr v => rfl

private def includeCore : TheoryMap Eη eliminationPresentation id where
  certificate r := by
    cases r with
    | inl r => exact Derivation.rule (R := eliminationPresentation) (.inl r) (fun i => .hyp ⟨i, rfl⟩)
    | inr r => exact Derivation.rule (R := eliminationPresentation) (.inr (.inl r)) (fun i => .hyp ⟨i, rfl⟩)

namespace ContextualBoundary
variable {H : Judgment eliminationSignature → Type}

private def secondTerm
    (stable : ∀ j, H j → Reindexed (R := eliminationPresentation) (H := H) j)
    {Γ : Context eliminationSignature V} {A : EExpr V} {B : EExpr (Fin 1 ⊕ V)} {p : EExpr V}
    (ctx : Derivation eliminationPresentation H (.ctx Γ))
    (type : Derivation eliminationPresentation H (.type Γ A))
    (family : Derivation eliminationPresentation H (.type (.extend Γ A) B))
    (term : Derivation eliminationPresentation H (.term Γ p (S A B))) :
    Derivation eliminationPresentation H (.term Γ (second A B p) (instantiate B (first A B p))) := by
  let premises : Fin 4 → Judgment eliminationSignature := fun i =>
    [Judgment.ctx Γ, Judgment.type Γ A, Judgment.type (.extend Γ A) B, Judgment.term Γ p (S A B)].get i
  have cert := ECertificate.second (premise := premises)
    (.hyp 0) (.hyp 1) (.hyp 2) (fun Δ σ env => MetavariableCertificate.apply (R := Eη) (premise := premises) (2 : Fin 4) Δ σ env.context env.component) p (.hyp 3)
  exact (cert.mapRules includeCore).graft (fullEliminationLocal H) stable
    (Fin.cases ctx (Fin.cases type (Fin.cases family (Fin.cases term (fun i => Fin.elim0 i)))))

private def firstTerm
    (stable : ∀ j, H j → Reindexed (R := eliminationPresentation) (H := H) j)
    {Γ : Context eliminationSignature V} {A : EExpr V} {B : EExpr (Fin 1 ⊕ V)} {p : EExpr V}
    (ctx : Derivation eliminationPresentation H (.ctx Γ))
    (type : Derivation eliminationPresentation H (.type Γ A))
    (family : Derivation eliminationPresentation H (.type (.extend Γ A) B))
    (term : Derivation eliminationPresentation H (.term Γ p (S A B))) :
    Derivation eliminationPresentation H (.term Γ (first A B p) A) := by
  let premises : Fin 4 → Judgment eliminationSignature := fun i =>
    [Judgment.ctx Γ, Judgment.type Γ A, Judgment.type (.extend Γ A) B, Judgment.term Γ p (S A B)].get i
  have cert := ECertificate.first (premise := premises)
    (.hyp 0) (.hyp 1) (.hyp 2) p (.hyp 3)
  exact (cert.mapRules includeCore).graft (fullEliminationLocal H) stable
    (Fin.cases ctx (Fin.cases type (Fin.cases family (Fin.cases term (fun i => Fin.elim0 i)))))

private def familyAt
    (stable : ∀ j, H j → Reindexed (R := eliminationPresentation) (H := H) j)
    {Γ : Context eliminationSignature V} {A : EExpr V} {B : EExpr (Fin 1 ⊕ V)} {a : EExpr V}
    (ctx : Derivation eliminationPresentation H (.ctx Γ))
    (family : Derivation eliminationPresentation H (.type (.extend Γ A) B))
    (term : Derivation eliminationPresentation H (.term Γ a A)) :
    Derivation eliminationPresentation H (.type Γ (instantiate B a)) :=
  substitute (fullEliminationLocal H) stable family Γ _
    (single fullEliminationStructural Γ A a ctx term)

/-- All dependent-eliminator primitive boundaries are reconstructed. Split beta
instantiates the supplied branch proof at its typed pair of arguments. -/
def eliminationPrimitive
    (stable : ∀ j, H j → Reindexed (R := eliminationPresentation) (H := H) j)
    (r : EliminationRule)
    (ps : ∀ i : Fin (EliminationRule.schema r).premises.length,
      Derivation eliminationPresentation H ((EliminationRule.schema r).premises.get i)) :
    ContextualBoundary eliminationPresentation H (EliminationRule.schema r).conclusion := by
  let app (r : EliminationRule)
      (children : ∀ i : Fin (EliminationRule.schema r).premises.length,
        Derivation eliminationPresentation H ((EliminationRule.schema r).premises.get i)) :
      Derivation eliminationPresentation H (EliminationRule.schema r).conclusion :=
    (fullEliminationPrimitive.certificate r).graft (fun _ h => h.property ▸ children h.val)
  cases r with
  | formation Γ A B =>
      dsimp [EliminationRule.schema, EliminationRule.family] at ps
      exact ps 0
  | pack Γ A B a b =>
      dsimp [EliminationRule.schema, EliminationRule.family] at ps
      exact ⟨ps 0, app (.formation Γ A B)
        (Fin.cases (ps 0) (Fin.cases (ps 1) (Fin.cases (ps 2) (fun i => Fin.elim0 i))))⟩
  | split Γ A B D e p =>
      dsimp [EliminationRule.schema, EliminationRule.family, EliminationRule.motiveBranch] at ps
      exact ⟨ps 0, familyAt stable (ps 0) (ps 3) (ps 5)⟩
  | splitBeta Γ A B D e a b =>
      dsimp [EliminationRule.schema, EliminationRule.family, EliminationRule.motiveBranch] at ps
      have packed := app (.pack Γ A B a b)
        (Fin.cases (ps 0) (Fin.cases (ps 1) (Fin.cases (ps 2)
          (Fin.cases (ps 5) (Fin.cases (ps 6) (fun i => Fin.elim0 i))))))
      have left := app (.split Γ A B D e (pack A B a b))
        (Fin.cases (ps 0) (Fin.cases (ps 1) (Fin.cases (ps 2) (Fin.cases (ps 3)
          (Fin.cases (ps 4) (Fin.cases packed (fun i => Fin.elim0 i)))))))
      have envA := single fullEliminationStructural Γ A a (ps 0) (ps 5)
      have envAB := TypedSubstitution.extendSource envA B b (ps 6)
      have right := substitute (fullEliminationLocal H) stable (ps 4) Γ _ envAB
      change Proof Γ (.term
        (Expr.subst (branchArguments a b) (Expr.rename flattenToNested e))
        (Expr.subst (branchArguments a b) (branchType A B D))) at right
      rw [branchTerm_arguments, branchType_arguments] at right
      exact ⟨ps 0, familyAt stable (ps 0) (ps 3) packed, left, right⟩
  | eta Γ A B p =>
      dsimp [EliminationRule.schema, EliminationRule.family] at ps
      have ty := app (.formation Γ A B)
        (Fin.cases (ps 0) (Fin.cases (ps 1) (Fin.cases (ps 2) (fun i => Fin.elim0 i))))
      have firstProof := firstTerm stable (ps 0) (ps 1) (ps 2) (ps 3)
      have secondProof := secondTerm stable (ps 0) (ps 1) (ps 2) (ps 3)
      have packed := app (.pack Γ A B (first A B p) (second A B p))
        (Fin.cases (ps 0) (Fin.cases (ps 1) (Fin.cases (ps 2)
          (Fin.cases firstProof (Fin.cases secondProof (fun i => Fin.elim0 i))))))
      exact ⟨ps 0, ty, packed, ps 3⟩

/-- Eliminator congruence explicitly supplies common-typed term endpoints. -/
def eliminationCongruence
    (r : EliminationCongruence)
    (ps : ∀ i : Fin (EliminationCongruence.schema r).premises.length,
      Derivation eliminationPresentation H ((EliminationCongruence.schema r).premises.get i))
    (bs : ∀ i : Fin (EliminationCongruence.schema r).premises.length,
      ContextualBoundary eliminationPresentation H ((EliminationCongruence.schema r).premises.get i)) :
    ContextualBoundary eliminationPresentation H (EliminationCongruence.schema r).conclusion := by
  let app (r : EliminationRule)
      (children : ∀ i : Fin (EliminationRule.schema r).premises.length,
        Derivation eliminationPresentation H ((EliminationRule.schema r).premises.get i)) :
      Derivation eliminationPresentation H (EliminationRule.schema r).conclusion :=
    (fullEliminationPrimitive.certificate r).graft (fun _ h => h.property ▸ children h.val)
  cases r with
  | formation Γ A A' B B' =>
      dsimp [EliminationCongruence.schema, EliminationCongruence.families] at ps bs
      exact ⟨ps 0,
        app (.formation Γ A B) (Fin.cases (ps 0) (Fin.cases (ps 1) (Fin.cases (ps 3) (fun i => Fin.elim0 i)))),
        app (.formation Γ A' B') (Fin.cases (ps 0) (Fin.cases (ps 2) (Fin.cases (ps 4) (fun i => Fin.elim0 i))))⟩
  | pack Γ A A' B B' a a' b b' =>
      dsimp [EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints] at ps bs
      exact ⟨ps 0, (bs 9).2, ps 9, ps 10⟩
  | split Γ A A' B B' D D' e e' p p' =>
      dsimp [EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints] at ps bs
      exact ⟨ps 0, (bs 14).2, ps 14, ps 15⟩

end ContextualBoundary
/-- Full recursive presupposition package for the independently specified
eliminator theory, including branch substitution and macro-expanded eta. -/
def eliminationBoundaryLaws (H : Judgment eliminationSignature → Type)
    (stable : ∀ j, H j → Reindexed (R := eliminationPresentation) (H := H) j) :
    LocalContextualBoundary eliminationPresentation H where
  step r ps bs := by
    cases r with
    | inl r =>
        exact ContextualBoundary.structural fullEliminationStructural
          (fullEliminationLocal H) stable r ps bs
    | inr r =>
      cases r with
      | inl r => exact ContextualBoundary.eliminationPrimitive stable r ps
      | inr r =>
        cases r with
        | inl r => exact ContextualBoundary.eliminationCongruence r ps bs
        | inr r =>
          cases r with
          | inl r =>
              exact DependentPairDeclarations.declarationBoundary
                DependentPairDeclarations.elimination fullEliminationDeclaration r ps
          | inr r =>
              exact DependentPairDeclarations.declarationCongruenceBoundary
                DependentPairDeclarations.elimination fullEliminationDeclaration r ps bs

/-- Every closed Eη derivation has its contextual type and endpoint boundaries.
This is a checked theorem for the bounded table, not an imported acceptability theorem. -/
def eliminationPresuppositions {j : Judgment eliminationSignature}
    (d : Derivation eliminationPresentation (fun _ => Empty) j) :
    ContextualBoundary eliminationPresentation (fun _ => Empty) j :=
  contextualPresuppositions (eliminationBoundaryLaws _ (fun _ h => Empty.elim h))
    (fun _ h => Empty.elim h) d

end SquareKit.DependentPairJudgments
