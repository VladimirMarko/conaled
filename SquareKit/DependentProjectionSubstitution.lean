import SquareKit.DependentTypedSubstitution

namespace SquareKit.DependentPairPresentations.Projection
open DependentTheoryMaps

@[simp] theorem subst_P (f : V → PExpr W) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V)) :
    Expr.subst f (P A B) = P (Expr.subst f A) (Expr.subst (Expr.lift f) B) := by
  simp only [P, Expr.subst]
  congr 1
  funext i
  change Fin 2 at i
  fin_cases i <;> first | exact Elimination.subst_zero f _ | rfl

@[simp] theorem subst_pair (f : V → PExpr W) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V))
    (a b : PExpr V) :
    Expr.subst f (pair A B a b) = pair (Expr.subst f A) (Expr.subst (Expr.lift f) B)
      (Expr.subst f a) (Expr.subst f b) := by
  simp only [pair, Expr.subst]
  congr 1
  funext i
  change Fin 4 at i
  fin_cases i <;> first | exact Elimination.subst_zero f _ | rfl

@[simp] theorem subst_fst (f : V → PExpr W) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V))
    (p : PExpr V) :
    Expr.subst f (fst A B p) = fst (Expr.subst f A) (Expr.subst (Expr.lift f) B) (Expr.subst f p) := by
  simp only [fst, Expr.subst]
  congr 1
  funext i
  change Fin 3 at i
  fin_cases i <;> first | exact Elimination.subst_zero f _ | rfl

@[simp] theorem subst_snd (f : V → PExpr W) (A : PExpr V) (B : PExpr (Fin 1 ⊕ V))
    (p : PExpr V) :
    Expr.subst f (snd A B p) = snd (Expr.subst f A) (Expr.subst (Expr.lift f) B) (Expr.subst f p) := by
  simp only [snd, Expr.subst]
  congr 1
  funext i
  change Fin 3 at i
  fin_cases i <;> first | exact Elimination.subst_zero f _ | rfl
end SquareKit.DependentPairPresentations.Projection

namespace SquareKit.DependentPairJudgments.TypedSubstitution
open DependentTheoryMaps DependentPairPresentations Projection
variable {eta : Bool} {R : Rules (Judgment projectionSignature)}
  {H : Judgment projectionSignature → Type}

def projectionStep
    (structural : TheoryMap (structuralRules projectionSignature) R id)
    (primitive : TheoryMap (rulesOf (ProjectionRule.schema (hasEta := eta))) R id)
    (r : ProjectionRule eta)
    (rec : ∀ i : Fin (ProjectionRule.schema r).premises.length,
      Reindexed (R := R) (H := H) ((ProjectionRule.schema r).premises.get i)) :
    Reindexed (R := R) (H := H) (ProjectionRule.schema r).conclusion := by
  let app (r : ProjectionRule eta)
      (ps : (i : Fin (ProjectionRule.schema r).premises.length) →
        Derivation R H ((ProjectionRule.schema r).premises.get i)) :
      Derivation R H (ProjectionRule.schema r).conclusion :=
    (primitive.certificate r).graft (fun _ h => h.property ▸ ps h.val)
  cases r with
  | formation Γ A B =>
      dsimp [ProjectionRule.schema, ProjectionRule.family, Judgment.type] at rec ⊢
      intro W Δ σ s
      have pa := rec 1 Δ σ s
      have pb := rec 2 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural s A pa)
      change Proof (R := R) (H := H) Δ (.type (Expr.subst σ (P A B)))
      rw [subst_P]
      exact app (.formation Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B))
        (Fin.cases s.context (Fin.cases pa (Fin.cases pb (fun i => Fin.elim0 i))))
  | pair Γ A B a b =>
      dsimp [ProjectionRule.schema, ProjectionRule.components, ProjectionRule.family,
        Judgment.term] at rec ⊢
      intro W Δ σ s
      have pa := rec 1 Δ σ s
      have pb := rec 2 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural s A pa)
      have ha := rec 3 Δ σ s
      have hb : Proof (R := R) (H := H) Δ (.term (Expr.subst σ b)
          (Elimination.instantiate (Expr.subst (Expr.lift σ) B) (Expr.subst σ a))) := by
        have h := rec 4 Δ σ s
        change Proof (R := R) (H := H) Δ (.term (Expr.subst σ b) (Expr.subst σ (Elimination.instantiate B a))) at h
        rw [Elimination.subst_instantiate] at h
        exact h
      change Proof (R := R) (H := H) Δ (.term (Expr.subst σ (pair A B a b)) (Expr.subst σ (P A B)))
      rw [subst_pair, subst_P]
      exact app (.pair Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B)
          (Expr.subst σ a) (Expr.subst σ b))
        (Fin.cases s.context (Fin.cases pa (Fin.cases pb (Fin.cases ha
          (Fin.cases hb (fun i => Fin.elim0 i))))))
  | first Γ A B p =>
      dsimp [ProjectionRule.schema, ProjectionRule.argument, ProjectionRule.family,
        Judgment.term] at rec ⊢
      intro W Δ σ s
      have pa := rec 1 Δ σ s
      have pb := rec 2 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural s A pa)
      have hp : Proof (R := R) (H := H) Δ (.term (Expr.subst σ p) (P (Expr.subst σ A) (Expr.subst (Expr.lift σ) B))) := by
        have h := rec 3 Δ σ s
        change Proof (R := R) (H := H) Δ (.term (Expr.subst σ p) (Expr.subst σ (P A B))) at h
        rw [subst_P] at h
        exact h
      change Proof (R := R) (H := H) Δ (.term (Expr.subst σ (fst A B p)) (Expr.subst σ A))
      rw [subst_fst]
      exact app (.first Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B) (Expr.subst σ p))
        (Fin.cases s.context (Fin.cases pa (Fin.cases pb (Fin.cases hp (fun i => Fin.elim0 i)))))
  | second Γ A B p =>
      dsimp [ProjectionRule.schema, ProjectionRule.argument, ProjectionRule.family,
        Judgment.term] at rec ⊢
      intro W Δ σ s
      have pa := rec 1 Δ σ s
      have pb := rec 2 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural s A pa)
      have hp : Proof (R := R) (H := H) Δ (.term (Expr.subst σ p) (P (Expr.subst σ A) (Expr.subst (Expr.lift σ) B))) := by
        have h := rec 3 Δ σ s
        change Proof (R := R) (H := H) Δ (.term (Expr.subst σ p) (Expr.subst σ (P A B))) at h
        rw [subst_P] at h
        exact h
      change Proof (R := R) (H := H) Δ (.term (Expr.subst σ (snd A B p)) (Expr.subst σ (Elimination.instantiate B (fst A B p))))
      rw [subst_snd, Elimination.subst_instantiate, subst_fst]
      exact app (.second Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B) (Expr.subst σ p))
        (Fin.cases s.context (Fin.cases pa (Fin.cases pb (Fin.cases hp (fun i => Fin.elim0 i)))))
  | firstBeta Γ A B a b =>
      dsimp [ProjectionRule.schema, ProjectionRule.components, ProjectionRule.family,
        Judgment.termEq] at rec ⊢
      intro W Δ σ s
      have pa := rec 1 Δ σ s
      have pb := rec 2 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural s A pa)
      have ha := rec 3 Δ σ s
      have hb : Proof (R := R) (H := H) Δ (.term (Expr.subst σ b)
          (Elimination.instantiate (Expr.subst (Expr.lift σ) B) (Expr.subst σ a))) := by
        have h := rec 4 Δ σ s
        change Proof (R := R) (H := H) Δ (.term (Expr.subst σ b) (Expr.subst σ (Elimination.instantiate B a))) at h
        rw [Elimination.subst_instantiate] at h
        exact h
      change Proof (R := R) (H := H) Δ (.termEq (Expr.subst σ (fst A B (pair A B a b))) (Expr.subst σ a)
        (Expr.subst σ (A)))
      simp only [subst_fst, subst_pair]
      exact app (.firstBeta Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B)
          (Expr.subst σ a) (Expr.subst σ b))
        (Fin.cases s.context (Fin.cases pa (Fin.cases pb (Fin.cases ha
          (Fin.cases hb (fun i => Fin.elim0 i))))))
  | secondBeta Γ A B a b =>
      dsimp [ProjectionRule.schema, ProjectionRule.components, ProjectionRule.family,
        Judgment.termEq] at rec ⊢
      intro W Δ σ s
      have pa := rec 1 Δ σ s
      have pb := rec 2 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural s A pa)
      have ha := rec 3 Δ σ s
      have hb : Proof (R := R) (H := H) Δ (.term (Expr.subst σ b)
          (Elimination.instantiate (Expr.subst (Expr.lift σ) B) (Expr.subst σ a))) := by
        have h := rec 4 Δ σ s
        change Proof (R := R) (H := H) Δ (.term (Expr.subst σ b) (Expr.subst σ (Elimination.instantiate B a))) at h
        rw [Elimination.subst_instantiate] at h
        exact h
      change Proof (R := R) (H := H) Δ (.termEq (Expr.subst σ (snd A B (pair A B a b))) (Expr.subst σ b)
        (Expr.subst σ (Elimination.instantiate B a)))
      simp only [subst_snd, subst_pair, Elimination.subst_instantiate]
      exact app (.secondBeta Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B)
          (Expr.subst σ a) (Expr.subst σ b))
        (Fin.cases s.context (Fin.cases pa (Fin.cases pb (Fin.cases ha
          (Fin.cases hb (fun i => Fin.elim0 i))))))
  | eta allowed Γ A B p =>
      dsimp [ProjectionRule.schema, ProjectionRule.argument, ProjectionRule.family,
        Judgment.termEq] at rec ⊢
      intro W Δ σ s
      have pa := rec 1 Δ σ s
      have pb := rec 2 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural s A pa)
      have hp : Proof (R := R) (H := H) Δ (.term (Expr.subst σ p) (P (Expr.subst σ A) (Expr.subst (Expr.lift σ) B))) := by
        have h := rec 3 Δ σ s
        change Proof (R := R) (H := H) Δ (.term (Expr.subst σ p) (Expr.subst σ (P A B))) at h
        rw [subst_P] at h
        exact h
      change Proof (R := R) (H := H) Δ (.termEq (Expr.subst σ (pair A B (fst A B p) (snd A B p)))
        (Expr.subst σ p) (Expr.subst σ (P A B)))
      rw [subst_pair, subst_fst, subst_snd, subst_P]
      exact app (.eta allowed Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B) (Expr.subst σ p))
        (Fin.cases s.context (Fin.cases pa (Fin.cases pb (Fin.cases hp (fun i => Fin.elim0 i)))))

/-- Structural rule inclusion for any independently supplied primitive table. -/
def includeStructural (schema : L → Schema S) :
    TheoryMap (structuralRules S) (closedRules schema) id where
  certificate r := Derivation.rule (R := closedRules schema) (.inl r) (fun i => .hyp ⟨i, rfl⟩)

def includePrimitive (schema : L → Schema S) :
    TheoryMap (rulesOf schema) (closedRules schema) id where
  certificate r := Derivation.rule (R := closedRules schema) (.inr r) (fun i => .hyp ⟨i, rfl⟩)

/-- Complete admissibility package for either independently specified projection
presentation; every primitive case is reconstructed above. -/
def projectionLocal (eta : Bool) (H : Judgment projectionSignature → Type) :
    Local (R := closedRules (ProjectionRule.schema (hasEta := eta))) (H := H) where
  step r rec := match r with
    | .inl r => structuralStep (includeStructural ProjectionRule.schema) r rec
    | .inr r => projectionStep (includeStructural ProjectionRule.schema)
        (includePrimitive ProjectionRule.schema) r rec

/-- Closed projection derivations admit substitution without any extra rule or
assumption-closure field. -/
def substituteClosed (eta : Bool)
    {j : Judgment projectionSignature}
    (d : Derivation (closedRules (ProjectionRule.schema (hasEta := eta))) (fun _ => Empty) j) :
    Reindexed (R := closedRules (ProjectionRule.schema (hasEta := eta))) (H := fun _ => Empty) j :=
  substitute (projectionLocal eta _) (fun _ h => Empty.elim h) d

end SquareKit.DependentPairJudgments.TypedSubstitution
