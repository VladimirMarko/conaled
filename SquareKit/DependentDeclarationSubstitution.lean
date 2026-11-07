import SquareKit.DependentPairCongruence
import SquareKit.DependentTypedSubstitution

/-! Declaration substitution follows from local operation templates. -/
namespace SquareKit.DependentPairDeclarations
open DependentTheoryMaps DependentPairPresentations DependentPairJudgments

namespace Terms
variable (D : OperationMap signature S)
@[simp] theorem subst_N (σ : V → Expr S W) : Expr.subst σ (N (V := V) D) = N D := by
  rw [N, D.natural]
  congr 1
  funext i
  nomatch i
@[simp] theorem subst_B (σ : V → Expr S W) (n : Expr S V) :
    Expr.subst σ (B D n) = B D (Expr.subst σ n) := by
  rw [B, D.natural]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact Elimination.subst_zero σ n
@[simp] theorem subst_C (σ : V → Expr S W) (n y : Expr S V) :
    Expr.subst σ (C D n y) = C D (Expr.subst σ n) (Expr.subst σ y) := by
  rw [C, D.natural]
  congr 1
  funext i
  change Fin 2 at i
  fin_cases i <;> exact Elimination.subst_zero σ _
@[simp] theorem subst_s (σ : V → Expr S W) (m : Expr S V) :
    Expr.subst σ (s D m) = s D (Expr.subst σ m) := by
  rw [s, D.natural]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact Elimination.subst_zero σ m
@[simp] theorem subst_d (σ : V → Expr S W) (m : Expr S V) :
    Expr.subst σ (d D m) = d D (Expr.subst σ m) := by
  rw [d, D.natural]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact Elimination.subst_zero σ m
@[simp] theorem subst_t (σ : V → Expr S W) (m : Expr S V) :
    Expr.subst σ (t D m) = t D (Expr.subst σ m) := by
  rw [t, D.natural]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact Elimination.subst_zero σ m
@[simp] theorem subst_u (σ : V → Expr S W) (m : Expr S V) :
    Expr.subst σ (u D m) = u D (Expr.subst σ m) := by
  rw [u, D.natural]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact Elimination.subst_zero σ m

@[simp] theorem rename_N (ρ : V → W) : Expr.rename ρ (N (V := V) D) = N D := by
  rw [← Expr.subst_vars, subst_N]
@[simp] theorem rename_B (ρ : V → W) (n : Expr S V) :
    Expr.rename ρ (B D n) = B D (Expr.rename ρ n) := by
  rw [← Expr.subst_vars, subst_B]
  simp only [Expr.subst_vars]
@[simp] theorem rename_C (ρ : V → W) (n y : Expr S V) :
    Expr.rename ρ (C D n y) = C D (Expr.rename ρ n) (Expr.rename ρ y) := by
  rw [← Expr.subst_vars, subst_C]
  simp only [Expr.subst_vars]
@[simp] theorem rename_s (ρ : V → W) (m : Expr S V) :
    Expr.rename ρ (s D m) = s D (Expr.rename ρ m) := by
  rw [← Expr.subst_vars, subst_s]
  simp only [Expr.subst_vars]
@[simp] theorem rename_d (ρ : V → W) (m : Expr S V) :
    Expr.rename ρ (d D m) = d D (Expr.rename ρ m) := by
  rw [← Expr.subst_vars, subst_d]
  simp only [Expr.subst_vars]
@[simp] theorem rename_t (ρ : V → W) (m : Expr S V) :
    Expr.rename ρ (t D m) = t D (Expr.rename ρ m) := by
  rw [← Expr.subst_vars, subst_t]
  simp only [Expr.subst_vars]
@[simp] theorem rename_u (ρ : V → W) (m : Expr S V) :
    Expr.rename ρ (u D m) = u D (Expr.rename ρ m) := by
  rw [← Expr.subst_vars, subst_u]
  simp only [Expr.subst_vars]
end Terms

open DependentPairJudgments.TypedSubstitution
variable {R : Rules (Judgment S)} {H : Judgment S → Type}

def declarationStep (D : OperationMap signature S)
    (primitive : TheoryMap (rulesOf (Rule.schema D)) R id)
    (r : Rule S)
    (rec : ∀ i : Fin (r.schema D).premises.length,
      Reindexed (R := R) (H := H) ((r.schema D).premises.get i)) :
    Reindexed (R := R) (H := H) (r.schema D).conclusion := by
  let app (r : Rule S)
      (ps : (i : Fin (r.schema D).premises.length) → Derivation R H ((r.schema D).premises.get i)) :
      Derivation R H (r.schema D).conclusion :=
    (primitive.certificate r).graft (fun _ h => h.property ▸ ps h.val)
  cases r with
  | N Γ =>
    dsimp [Rule.schema, Judgment.ctx, Judgment.type, Judgment.term] at rec ⊢
    intro W Δ σ ts
    simp [Form.subst]
    simpa [Rule.schema, Judgment.type, Form.subst, Terms.subst_N] using
      app (.N Δ) (Fin.cases ts.context (fun i => Fin.elim0 i))
  | B Γ n =>
    dsimp [Rule.schema, Judgment.ctx, Judgment.type, Judgment.term] at rec ⊢
    intro W Δ σ ts
    simp [Form.subst]
    have hn := rec 1 Δ σ ts
    simpa [Rule.schema, Judgment.type, Form.subst, Terms.subst_B] using
      app (.B Δ (Expr.subst σ n)) (Fin.cases ts.context (Fin.cases
        (by simpa [Rule.schema, Judgment.term, Form.subst, Terms.subst_N] using hn)
        (fun i => Fin.elim0 i)))
  | C Γ n y =>
    dsimp [Rule.schema, Judgment.ctx, Judgment.type, Judgment.term] at rec ⊢
    intro W Δ σ ts
    simp [Form.subst]
    have hn := rec 1 Δ σ ts
    have hy := rec 2 Δ σ ts
    simpa [Rule.schema, Judgment.type, Form.subst, Terms.subst_C] using
      app (.C Δ (Expr.subst σ n) (Expr.subst σ y))
        (Fin.cases ts.context (Fin.cases
          (by simpa [Rule.schema, Judgment.term, Form.subst, Terms.subst_N] using hn)
          (Fin.cases (by simpa [Rule.schema, Judgment.term, Form.subst, Terms.subst_B] using hy)
            (fun i => Fin.elim0 i))))
  | s Γ m =>
    dsimp [Rule.schema, Judgment.ctx, Judgment.type, Judgment.term] at rec ⊢
    intro W Δ σ ts
    simp [Form.subst]
    have hm := rec 1 Δ σ ts
    simpa [Rule.schema, Judgment.term, Form.subst, Terms.subst_N, Terms.subst_s] using
      app (.s Δ (Expr.subst σ m)) (Fin.cases ts.context (Fin.cases
        (by simpa [Rule.schema, Judgment.term, Form.subst, Terms.subst_N] using hm)
        (fun i => Fin.elim0 i)))
  | d Γ m =>
    dsimp [Rule.schema, Judgment.ctx, Judgment.type, Judgment.term] at rec ⊢
    intro W Δ σ ts
    simp [Form.subst]
    have hm := rec 1 Δ σ ts
    simpa [Rule.schema, Judgment.term, Form.subst, Terms.subst_N, Terms.subst_d] using
      app (.d Δ (Expr.subst σ m)) (Fin.cases ts.context (Fin.cases
        (by simpa [Rule.schema, Judgment.term, Form.subst, Terms.subst_N] using hm)
        (fun i => Fin.elim0 i)))
  | t Γ m =>
    dsimp [Rule.schema, Judgment.ctx, Judgment.type, Judgment.term] at rec ⊢
    intro W Δ σ ts
    simp [Form.subst]
    have hm := rec 1 Δ σ ts
    simpa [Rule.schema, Judgment.term, Form.subst, Terms.subst_B, Terms.subst_s, Terms.subst_t] using
      app (.t Δ (Expr.subst σ m)) (Fin.cases ts.context (Fin.cases
        (by simpa [Rule.schema, Judgment.term, Form.subst, Terms.subst_N] using hm)
        (fun i => Fin.elim0 i)))
  | u Γ m =>
    dsimp [Rule.schema, Judgment.ctx, Judgment.type, Judgment.term] at rec ⊢
    intro W Δ σ ts
    simp [Form.subst]
    have hm := rec 1 Δ σ ts
    simpa [Rule.schema, Judgment.term, Form.subst, Terms.subst_C, Terms.subst_s,
      Terms.subst_t, Terms.subst_u] using
      app (.u Δ (Expr.subst σ m)) (Fin.cases ts.context (Fin.cases
        (by simpa [Rule.schema, Judgment.term, Form.subst, Terms.subst_N] using hm)
        (fun i => Fin.elim0 i)))

def declarationCongruenceStep (D : OperationMap signature S)
    (primitive : TheoryMap (rulesOf (Congruence.schema D)) R id)
    (r : Congruence S)
    (rec : ∀ i : Fin (r.schema D).premises.length,
      Reindexed (R := R) (H := H) ((r.schema D).premises.get i)) :
    Reindexed (R := R) (H := H) (r.schema D).conclusion := by
  let app (r : Congruence S)
      (ps : (i : Fin (r.schema D).premises.length) → Derivation R H ((r.schema D).premises.get i)) :
      Derivation R H (r.schema D).conclusion :=
    (primitive.certificate r).graft (fun _ h => h.property ▸ ps h.val)
  cases r with
  | B Γ n n' =>
    dsimp [Congruence.schema, Judgment.ctx, Judgment.typeEq, Judgment.termEq] at rec ⊢
    intro W Δ σ ts
    simp [Form.subst]
    exact app (.B Δ (Expr.subst σ n) (Expr.subst σ n')) (Fin.cases ts.context (Fin.cases (by simpa [Congruence.schema, Judgment.ctx, Judgment.term, Judgment.typeEq, Judgment.termEq, Form.subst] using rec 1 Δ σ ts) (fun i => Fin.elim0 i)))
  | C Γ n n' y y' =>
    dsimp [Congruence.schema, Judgment.ctx, Judgment.typeEq, Judgment.termEq] at rec ⊢
    intro W Δ σ ts
    simp [Form.subst]
    exact app (.C Δ (Expr.subst σ n) (Expr.subst σ n') (Expr.subst σ y) (Expr.subst σ y')) (Fin.cases ts.context (Fin.cases (by simpa [Congruence.schema, Judgment.ctx, Judgment.term, Judgment.typeEq, Judgment.termEq, Form.subst] using rec 1 Δ σ ts) (Fin.cases (by simpa [Congruence.schema, Judgment.ctx, Judgment.term, Judgment.typeEq, Judgment.termEq, Form.subst] using rec 2 Δ σ ts) (Fin.cases (by simpa [Congruence.schema, Judgment.ctx, Judgment.term, Judgment.typeEq, Judgment.termEq, Form.subst] using rec 3 Δ σ ts) (fun i => Fin.elim0 i)))))
  | s Γ m m' =>
    dsimp [Congruence.schema, Judgment.ctx, Judgment.typeEq, Judgment.termEq] at rec ⊢
    intro W Δ σ ts
    simp [Form.subst]
    exact app (.s Δ (Expr.subst σ m) (Expr.subst σ m')) (Fin.cases ts.context (Fin.cases (by simpa [Congruence.schema, Judgment.ctx, Judgment.term, Judgment.typeEq, Judgment.termEq, Form.subst] using rec 1 Δ σ ts) (fun i => Fin.elim0 i)))
  | d Γ m m' =>
    dsimp [Congruence.schema, Judgment.ctx, Judgment.typeEq, Judgment.termEq] at rec ⊢
    intro W Δ σ ts
    simp [Form.subst]
    exact app (.d Δ (Expr.subst σ m) (Expr.subst σ m')) (Fin.cases ts.context (Fin.cases (by simpa [Congruence.schema, Judgment.ctx, Judgment.term, Judgment.typeEq, Judgment.termEq, Form.subst] using rec 1 Δ σ ts) (fun i => Fin.elim0 i)))
  | t Γ m m' =>
    dsimp [Congruence.schema, Judgment.ctx, Judgment.typeEq, Judgment.termEq] at rec ⊢
    intro W Δ σ ts
    simp [Form.subst]
    exact app (.t Δ (Expr.subst σ m) (Expr.subst σ m')) (Fin.cases ts.context (Fin.cases (by simpa [Congruence.schema, Judgment.ctx, Judgment.term, Judgment.typeEq, Judgment.termEq, Form.subst] using rec 1 Δ σ ts) (Fin.cases (by simpa [Congruence.schema, Judgment.ctx, Judgment.term, Judgment.typeEq, Judgment.termEq, Form.subst] using rec 2 Δ σ ts) (fun i => Fin.elim0 i))))
  | u Γ m m' =>
    dsimp [Congruence.schema, Judgment.ctx, Judgment.typeEq, Judgment.termEq] at rec ⊢
    intro W Δ σ ts
    simp [Form.subst]
    exact app (.u Δ (Expr.subst σ m) (Expr.subst σ m')) (Fin.cases ts.context (Fin.cases (by simpa [Congruence.schema, Judgment.ctx, Judgment.term, Judgment.typeEq, Judgment.termEq, Form.subst] using rec 1 Δ σ ts) (Fin.cases (by simpa [Congruence.schema, Judgment.ctx, Judgment.term, Judgment.typeEq, Judgment.termEq, Form.subst] using rec 2 Δ σ ts) (fun i => Fin.elim0 i))))

end SquareKit.DependentPairDeclarations
