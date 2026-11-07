import SquareKit.DependentProjectionSubstitution
import SquareKit.DependentPairCongruence

namespace SquareKit.DependentPairJudgments.TypedSubstitution
open DependentTheoryMaps DependentPairPresentations Projection
variable {R : Rules (Judgment projectionSignature)} {H : Judgment projectionSignature → Type}

/-- Constructor congruence is stable under the same typed substitutions as the
primitive pair rules. The two family telescopes are lifted separately. -/
def projectionCongruenceStep
    (structural : TheoryMap (structuralRules projectionSignature) R id)
    (primitive : TheoryMap (rulesOf ProjectionCongruence.schema) R id)
    (r : ProjectionCongruence)
    (rec : ∀ i : Fin (ProjectionCongruence.schema r).premises.length,
      Reindexed (R := R) (H := H) ((ProjectionCongruence.schema r).premises.get i)) :
    Reindexed (R := R) (H := H) (ProjectionCongruence.schema r).conclusion := by
  let app (r : ProjectionCongruence)
      (ps : (i : Fin (ProjectionCongruence.schema r).premises.length) →
        Derivation R H ((ProjectionCongruence.schema r).premises.get i)) :
      Derivation R H (ProjectionCongruence.schema r).conclusion :=
    (primitive.certificate r).graft (fun _ h => h.property ▸ ps h.val)
  cases r with
  | formation Γ A A' B B'  =>
      dsimp [ProjectionCongruence.schema, ProjectionCongruence.families,
        ProjectionCongruence.endpoints, Judgment.ctx, Judgment.type, Judgment.typeEq,
        Judgment.term, Judgment.termEq] at rec ⊢
      intro W Δ σ st
      have pa := rec 1 Δ σ st
      have pa' := rec 2 Δ σ st
      have p3 := rec 3 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural st A pa)
      have p4 := rec 4 (.extend Δ (Expr.subst σ A')) (Expr.lift σ) (lift structural st A' pa')
      have p6 := rec 6 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural st A pa)
      have p5 := rec 5 Δ σ st
      change Proof Δ (.typeEq (Expr.subst σ (A)) (Expr.subst σ (A'))) at p5
      have result := app (.formation Δ (Expr.subst σ A) (Expr.subst σ A') (Expr.subst (Expr.lift σ) B)
          (Expr.subst (Expr.lift σ) B'))
        (Fin.cases st.context (Fin.cases pa (Fin.cases pa' (Fin.cases p3 (Fin.cases p4 (Fin.cases p5 (Fin.cases p6 (fun i => Fin.elim0 i))))))))
      change Proof Δ (.typeEq (Expr.subst σ (P A B)) (Expr.subst σ (P A' B')))
      simp only [subst_P]
      exact result
  | pair Γ A A' B B' a a' b b' =>
      dsimp [ProjectionCongruence.schema, ProjectionCongruence.families,
        ProjectionCongruence.endpoints, Judgment.ctx, Judgment.type, Judgment.typeEq,
        Judgment.term, Judgment.termEq] at rec ⊢
      intro W Δ σ st
      have pa := rec 1 Δ σ st
      have pa' := rec 2 Δ σ st
      have p3 := rec 3 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural st A pa)
      have p4 := rec 4 (.extend Δ (Expr.subst σ A')) (Expr.lift σ) (lift structural st A' pa')
      have p6 := rec 6 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural st A pa)
      have p5 := rec 5 Δ σ st
      change Proof Δ (.typeEq (Expr.subst σ (A)) (Expr.subst σ (A'))) at p5
      have p7 := rec 7 Δ σ st
      change Proof Δ (.termEq (Expr.subst σ (a)) (Expr.subst σ (a')) (Expr.subst σ (A))) at p7
      have p8 := rec 8 Δ σ st
      change Proof Δ (.termEq (Expr.subst σ (b)) (Expr.subst σ (b')) (Expr.subst σ (Elimination.instantiate B a))) at p8
      simp only [Elimination.subst_instantiate] at p8
      have p9 := rec 9 Δ σ st
      change Proof Δ (.term (Expr.subst σ (pair A B a b)) (Expr.subst σ (P A B))) at p9
      simp only [subst_P, subst_pair] at p9
      have p10 := rec 10 Δ σ st
      change Proof Δ (.term (Expr.subst σ (pair A' B' a' b')) (Expr.subst σ (P A B))) at p10
      simp only [subst_P, subst_pair] at p10
      have result := app (.pair Δ (Expr.subst σ A) (Expr.subst σ A') (Expr.subst (Expr.lift σ) B)
          (Expr.subst (Expr.lift σ) B') (Expr.subst σ a) (Expr.subst σ a') (Expr.subst σ b) (Expr.subst σ b'))
        (Fin.cases st.context (Fin.cases pa (Fin.cases pa' (Fin.cases p3 (Fin.cases p4 (Fin.cases p5 (Fin.cases p6 (Fin.cases p7 (Fin.cases p8 (Fin.cases p9 (Fin.cases p10 (fun i => Fin.elim0 i))))))))))))
      change Proof Δ (.termEq (Expr.subst σ (pair A B a b)) (Expr.subst σ (pair A' B' a' b')) (Expr.subst σ (P A B)))
      simp only [subst_P, subst_pair]
      exact result
  | first Γ A A' B B' p p' =>
      dsimp [ProjectionCongruence.schema, ProjectionCongruence.families,
        ProjectionCongruence.endpoints, Judgment.ctx, Judgment.type, Judgment.typeEq,
        Judgment.term, Judgment.termEq] at rec ⊢
      intro W Δ σ st
      have pa := rec 1 Δ σ st
      have pa' := rec 2 Δ σ st
      have p3 := rec 3 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural st A pa)
      have p4 := rec 4 (.extend Δ (Expr.subst σ A')) (Expr.lift σ) (lift structural st A' pa')
      have p6 := rec 6 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural st A pa)
      have p5 := rec 5 Δ σ st
      change Proof Δ (.typeEq (Expr.subst σ (A)) (Expr.subst σ (A'))) at p5
      have p7 := rec 7 Δ σ st
      change Proof Δ (.termEq (Expr.subst σ (p)) (Expr.subst σ (p')) (Expr.subst σ (P A B))) at p7
      simp only [subst_P] at p7
      have p8 := rec 8 Δ σ st
      change Proof Δ (.term (Expr.subst σ (fst A B p)) (Expr.subst σ (A))) at p8
      simp only [subst_fst] at p8
      have p9 := rec 9 Δ σ st
      change Proof Δ (.term (Expr.subst σ (fst A' B' p')) (Expr.subst σ (A))) at p9
      simp only [subst_fst] at p9
      have result := app (.first Δ (Expr.subst σ A) (Expr.subst σ A') (Expr.subst (Expr.lift σ) B)
          (Expr.subst (Expr.lift σ) B') (Expr.subst σ p) (Expr.subst σ p'))
        (Fin.cases st.context (Fin.cases pa (Fin.cases pa' (Fin.cases p3 (Fin.cases p4 (Fin.cases p5 (Fin.cases p6 (Fin.cases p7 (Fin.cases p8 (Fin.cases p9 (fun i => Fin.elim0 i)))))))))))
      change Proof Δ (.termEq (Expr.subst σ (fst A B p)) (Expr.subst σ (fst A' B' p')) (Expr.subst σ (A)))
      simp only [subst_fst]
      exact result
  | second Γ A A' B B' p p' =>
      dsimp [ProjectionCongruence.schema, ProjectionCongruence.families,
        ProjectionCongruence.endpoints, Judgment.ctx, Judgment.type, Judgment.typeEq,
        Judgment.term, Judgment.termEq] at rec ⊢
      intro W Δ σ st
      have pa := rec 1 Δ σ st
      have pa' := rec 2 Δ σ st
      have p3 := rec 3 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural st A pa)
      have p4 := rec 4 (.extend Δ (Expr.subst σ A')) (Expr.lift σ) (lift structural st A' pa')
      have p6 := rec 6 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural st A pa)
      have p5 := rec 5 Δ σ st
      change Proof Δ (.typeEq (Expr.subst σ (A)) (Expr.subst σ (A'))) at p5
      have p7 := rec 7 Δ σ st
      change Proof Δ (.termEq (Expr.subst σ (p)) (Expr.subst σ (p')) (Expr.subst σ (P A B))) at p7
      simp only [subst_P] at p7
      have p8 := rec 8 Δ σ st
      change Proof Δ (.term (Expr.subst σ (snd A B p)) (Expr.subst σ (Elimination.instantiate B (fst A B p)))) at p8
      simp only [subst_fst, subst_snd, Elimination.subst_instantiate] at p8
      have p9 := rec 9 Δ σ st
      change Proof Δ (.term (Expr.subst σ (snd A' B' p')) (Expr.subst σ (Elimination.instantiate B (fst A B p)))) at p9
      simp only [subst_fst, subst_snd, Elimination.subst_instantiate] at p9
      have result := app (.second Δ (Expr.subst σ A) (Expr.subst σ A') (Expr.subst (Expr.lift σ) B)
          (Expr.subst (Expr.lift σ) B') (Expr.subst σ p) (Expr.subst σ p'))
        (Fin.cases st.context (Fin.cases pa (Fin.cases pa' (Fin.cases p3 (Fin.cases p4 (Fin.cases p5 (Fin.cases p6 (Fin.cases p7 (Fin.cases p8 (Fin.cases p9 (fun i => Fin.elim0 i)))))))))))
      change Proof Δ (.termEq (Expr.subst σ (snd A B p)) (Expr.subst σ (snd A' B' p')) (Expr.subst σ (Elimination.instantiate B (fst A B p))))
      simp only [subst_fst, subst_snd, Elimination.subst_instantiate]
      exact result

end SquareKit.DependentPairJudgments.TypedSubstitution
