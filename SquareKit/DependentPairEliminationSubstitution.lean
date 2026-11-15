import SquareKit.DependentPairEliminationJudgments
import SquareKit.DependentTypedSubstitution
import SquareKit.DependentPairEliminationCongruence

/-! Rule-local typed substitution reconstruction for the eliminator presentation. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations Elimination

@[simp] theorem branchPair_subst (σ : V → EExpr W) (A : EExpr V) (B : EExpr (Fin 1 ⊕ V)) :
    Expr.subst (Expr.lift (Expr.lift σ)) (branchPair A B) =
      branchPair (Expr.subst σ A) (Expr.subst (Expr.lift σ) B) := by
  simp only [branchPair, subst_pack, Expr.subst_rename, Expr.rename_subst]
  congr 1
  · congr 1
    funext v
    simp [Expr.lift, Function.comp_def]
  · congr 1
    funext v
    cases v <;> simp [Expr.lift, Function.comp_def]

@[simp] theorem branchType_subst (σ : V → EExpr W) (A : EExpr V) (B D : EExpr (Fin 1 ⊕ V)) :
    Expr.subst (Expr.lift (Expr.lift σ)) (branchType A B D) =
      branchType (Expr.subst σ A) (Expr.subst (Expr.lift σ) B) (Expr.subst (Expr.lift σ) D) := by
  simp only [branchType, subst_instantiate, branchPair_subst]
  congr 1
  simp only [Expr.subst_rename, Expr.rename_subst]
  congr 1
  funext v
  cases v <;> simp [Expr.lift, Function.comp_def]

@[simp] theorem flatten_subst (σ : V → EExpr W) (e : EExpr (Fin 2 ⊕ V)) :
    Expr.rename flattenToNested (Expr.subst (Expr.lift σ) e) =
      Expr.subst (Expr.lift (Expr.lift σ)) (Expr.rename flattenToNested e) := by
  simp only [Expr.rename_subst, Expr.subst_rename]
  congr 1
  funext v
  cases v with
  | inl i =>
    simp only [Expr.lift, Expr.rename, Function.comp_apply, flattenToNested]
    split <;> rfl
  | inr v => simp [Expr.lift, flattenToNested, Function.comp_def]

@[simp] theorem branchAt_subst (σ : V → EExpr W) (e : EExpr (Fin 2 ⊕ V)) (a b : EExpr V) :
    Expr.subst σ (branchAt e a b) =
      branchAt (Expr.subst (Expr.lift σ) e) (Expr.subst σ a) (Expr.subst σ b) := by
  simp only [branchAt, Expr.subst_comp]
  congr 1
  funext v
  cases v with
  | inl i => simp only [Expr.lift, Expr.subst_var, Sum.elim_inl]; split <;> rfl
  | inr v =>
    simp only [Expr.lift, Expr.subst_rename, Sum.elim_inr]
    change σ v = Expr.subst Expr.var (σ v)
    exact (Expr.subst_id _).symm

namespace TypedSubstitution
variable {R : Rules (Judgment eliminationSignature)} {H : Judgment eliminationSignature → Type}
  (structural : TheoryMap (structuralRules eliminationSignature) R id)
  (primitive : TheoryMap eliminationRules R id)

def eliminationRule (r : EliminationRule)
    (premises : (i : Fin (EliminationRule.schema r).premises.length) →
      Derivation R H ((EliminationRule.schema r).premises.get i)) :
    Derivation R H (EliminationRule.schema r).conclusion :=
  (primitive.certificate r).graft (fun _ h => h.property ▸ premises h.val)

def eliminationStep (r : EliminationRule)
    (rec : ∀ i : Fin (EliminationRule.schema r).premises.length,
      Reindexed (R := R) (H := H) ((EliminationRule.schema r).premises.get i)) :
    Reindexed (R := R) (H := H) (EliminationRule.schema r).conclusion := by
  cases r with
  | formation Γ A B =>
    dsimp [EliminationRule.schema, EliminationRule.family, Judgment.type, Judgment.ctx] at rec ⊢
    intro W Δ σ s
    have pa := rec 1 Δ σ s
    have pb := rec 2 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural s A pa)
    change Proof Δ (.type (Expr.subst σ (S A B)))
    rw [subst_S]
    exact eliminationRule primitive (.formation Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B))
      (Fin.cases s.context (Fin.cases pa (Fin.cases pb (fun i => nomatch i))))
  | pack Γ A B a b =>
    dsimp [EliminationRule.schema, EliminationRule.family, Judgment.type, Judgment.ctx, Judgment.term] at rec ⊢
    intro W Δ σ s
    have pa := rec 1 Δ σ s
    have pb := rec 2 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural s A pa)
    have ha := rec 3 Δ σ s
    have hb := rec 4 Δ σ s
    change Proof Δ (.term (Expr.subst σ (pack A B a b)) (Expr.subst σ (S A B)))
    rw [subst_pack, subst_S]
    exact eliminationRule primitive (.pack Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B)
      (Expr.subst σ a) (Expr.subst σ b))
      (Fin.cases s.context (Fin.cases pa (Fin.cases pb (Fin.cases ha
        (Fin.cases (by simpa [EliminationRule.schema, EliminationRule.family, EliminationRule.motiveBranch, Judgment.type, Judgment.term, branchContext, Form.subst, subst_instantiate] using hb) (fun i => nomatch i))))))
  | split Γ A B D e p =>
    dsimp [EliminationRule.schema, EliminationRule.motiveBranch, EliminationRule.family,
      Judgment.type, Judgment.ctx, Judgment.term] at rec ⊢
    intro W Δ σ s
    have pa := rec 1 Δ σ s
    have sa := lift structural s A pa
    have pb := rec 2 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) sa
    have pS := eliminationRule primitive (.formation Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B))
      (Fin.cases s.context (Fin.cases pa (Fin.cases pb (fun i => nomatch i))))
    have pS' : Proof (R := R) (H := H) Δ (.type (Expr.subst σ (S A B))) := by
      simpa [EliminationRule.schema, EliminationRule.family, EliminationRule.motiveBranch, Judgment.type, Judgment.term, branchContext, Form.subst, subst_S] using pS
    have pd := rec 3 (.extend Δ (Expr.subst σ (S A B))) (Expr.lift σ) (lift structural s (S A B) pS')
    have sab := lift structural sa B pb
    have pe := rec 4 _ (Expr.lift (Expr.lift σ)) sab
    have pp := rec 5 Δ σ s
    change Proof Δ (.term (Expr.subst σ (Elimination.split A B D e p)) (Expr.subst σ (instantiate D p)))
    rw [subst_split, subst_instantiate]
    exact eliminationRule primitive (.split Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B)
      (Expr.subst (Expr.lift σ) D) (Expr.subst (Expr.lift σ) e) (Expr.subst σ p))
      (Fin.cases s.context (Fin.cases pa (Fin.cases pb
        (Fin.cases (by simpa [EliminationRule.schema, EliminationRule.family, EliminationRule.motiveBranch, Judgment.type, Judgment.term, branchContext, Form.subst, subst_S] using pd)
          (Fin.cases (by simpa [EliminationRule.schema, EliminationRule.family, EliminationRule.motiveBranch, Judgment.type, Judgment.term, branchContext, Form.subst, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using pe)
            (Fin.cases (by simpa [EliminationRule.schema, EliminationRule.family, EliminationRule.motiveBranch, Judgment.type, Judgment.term, branchContext, Form.subst, subst_S] using pp) (fun i => nomatch i)))))))
  | splitBeta Γ A B D e a b =>
    dsimp [EliminationRule.schema, EliminationRule.motiveBranch, EliminationRule.family,
      Judgment.type, Judgment.ctx, Judgment.term, Judgment.termEq] at rec ⊢
    intro W Δ σ s
    have pa := rec 1 Δ σ s
    have sa := lift structural s A pa
    have pb := rec 2 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) sa
    have pS := eliminationRule primitive (.formation Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B))
      (Fin.cases s.context (Fin.cases pa (Fin.cases pb (fun i => nomatch i))))
    have pS' : Proof (R := R) (H := H) Δ (.type (Expr.subst σ (S A B))) := by
      simpa [EliminationRule.schema, EliminationRule.family, EliminationRule.motiveBranch, Judgment.type, Judgment.term, branchContext, Form.subst, subst_S] using pS
    have pd := rec 3 (.extend Δ (Expr.subst σ (S A B))) (Expr.lift σ) (lift structural s (S A B) pS')
    have sab := lift structural sa B pb
    have pe := rec 4 _ (Expr.lift (Expr.lift σ)) sab
    have ha := rec 5 Δ σ s
    have hb := rec 6 Δ σ s
    change Proof Δ (.termEq (Expr.subst σ (Elimination.split A B D e (pack A B a b)))
      (Expr.subst σ (branchAt e a b)) (Expr.subst σ (instantiate D (pack A B a b))))
    rw [subst_split, subst_pack, branchAt_subst, subst_instantiate, subst_pack]
    exact eliminationRule primitive (.splitBeta Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B)
      (Expr.subst (Expr.lift σ) D) (Expr.subst (Expr.lift σ) e) (Expr.subst σ a) (Expr.subst σ b))
      (Fin.cases s.context (Fin.cases pa (Fin.cases pb
        (Fin.cases (by simpa [EliminationRule.schema, EliminationRule.family, EliminationRule.motiveBranch, Judgment.type, Judgment.term, branchContext, Form.subst, subst_S] using pd)
          (Fin.cases (by simpa [EliminationRule.schema, EliminationRule.family, EliminationRule.motiveBranch, Judgment.type, Judgment.term, branchContext, Form.subst, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using pe)
            (Fin.cases ha (Fin.cases (by simpa [EliminationRule.schema, EliminationRule.family, EliminationRule.motiveBranch, Judgment.type, Judgment.term, branchContext, Form.subst, subst_instantiate] using hb)
              (fun i => nomatch i))))))))
  | eta Γ A B p =>
    dsimp [EliminationRule.schema, EliminationRule.family,
      Judgment.type, Judgment.ctx, Judgment.term, Judgment.termEq] at rec ⊢
    intro W Δ σ s
    have pa := rec 1 Δ σ s
    have pb := rec 2 (.extend Δ (Expr.subst σ A)) (Expr.lift σ) (lift structural s A pa)
    have pp := rec 3 Δ σ s
    change Proof Δ (.termEq (Expr.subst σ (pack A B (first A B p) (second A B p)))
      (Expr.subst σ p) (Expr.subst σ (S A B)))
    rw [subst_pack, subst_first, subst_second, subst_S]
    exact eliminationRule primitive (.eta Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B) (Expr.subst σ p))
      (Fin.cases s.context (Fin.cases pa (Fin.cases pb
        (Fin.cases (by simpa [EliminationRule.schema, EliminationRule.family, EliminationRule.motiveBranch, Judgment.type, Judgment.term, branchContext, Form.subst, subst_S] using pp) (fun i => nomatch i)))))

def eliminationCongruenceStep
    (congruence : TheoryMap (rulesOf EliminationCongruence.schema) R id)
    (r : EliminationCongruence)
    (rec : ∀ i : Fin (EliminationCongruence.schema r).premises.length,
      Reindexed (R := R) (H := H) ((EliminationCongruence.schema r).premises.get i)) :
    Reindexed (R := R) (H := H) (EliminationCongruence.schema r).conclusion := by
  have app (r : EliminationCongruence)
      (ps : ∀ i : Fin (EliminationCongruence.schema r).premises.length,
        Derivation R H ((EliminationCongruence.schema r).premises.get i)) :
      Derivation R H (EliminationCongruence.schema r).conclusion :=
    (congruence.certificate r).graft (fun _ h => h.property ▸ ps h.val)
  cases r with
  | formation Γ A A' B B' =>
    dsimp [EliminationCongruence.schema, EliminationCongruence.families,
      EliminationCongruence.endpoints, Judgment.typeEq, Judgment.termEq] at rec ⊢
    intro W Δ σ s
    have pa := rec 1 Δ σ s
    have pa' := rec 2 Δ σ s
    have sa := lift structural s A pa
    have sa' := lift structural s A' pa'
    have pb := rec 3 _ (Expr.lift σ) sa
    have pb' := rec 4 _ (Expr.lift σ) sa'
    have hab := rec 5 Δ σ s
    have hbb := rec 6 _ (Expr.lift σ) sa
    have result := app (.formation Δ (Expr.subst σ A) (Expr.subst σ A') (Expr.subst (Expr.lift σ) B) (Expr.subst (Expr.lift σ) B'))
      (by
        refine (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => nomatch i))))))))
        · exact s.context
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using pa
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using pa'
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using pb
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using pb'
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using hab
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using hbb
      )
    simpa [EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using result
  | pack Γ A A' B B' a a' b b' =>
    dsimp [EliminationCongruence.schema, EliminationCongruence.families,
      EliminationCongruence.endpoints, Judgment.typeEq, Judgment.termEq] at rec ⊢
    intro W Δ σ s
    have pa := rec 1 Δ σ s
    have pa' := rec 2 Δ σ s
    have sa := lift structural s A pa
    have sa' := lift structural s A' pa'
    have pb := rec 3 _ (Expr.lift σ) sa
    have pb' := rec 4 _ (Expr.lift σ) sa'
    have hab := rec 5 Δ σ s
    have hbb := rec 6 _ (Expr.lift σ) sa
    have h7 := rec 7 Δ σ s
    have h8 := rec 8 Δ σ s
    have h9 := rec 9 Δ σ s
    have h10 := rec 10 Δ σ s
    have result := app (.pack Δ (Expr.subst σ A) (Expr.subst σ A') (Expr.subst (Expr.lift σ) B) (Expr.subst (Expr.lift σ) B') (Expr.subst σ a) (Expr.subst σ a') (Expr.subst σ b) (Expr.subst σ b'))
      (by
        refine (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => nomatch i))))))))))))
        · exact s.context
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using pa
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using pa'
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using pb
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using pb'
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using hab
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using hbb
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using h7
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using h8
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using h9
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using h10
      )
    simpa [EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using result
  | split Γ A A' B B' D D' e e' p p' =>
    dsimp [EliminationCongruence.schema, EliminationCongruence.families,
      EliminationCongruence.endpoints, Judgment.typeEq, Judgment.termEq] at rec ⊢
    intro W Δ σ s
    have pa := rec 1 Δ σ s
    have pa' := rec 2 Δ σ s
    have sa := lift structural s A pa
    have sa' := lift structural s A' pa'
    have pb := rec 3 _ (Expr.lift σ) sa
    have pb' := rec 4 _ (Expr.lift σ) sa'
    have hab := rec 5 Δ σ s
    have hbb := rec 6 _ (Expr.lift σ) sa
    have pS := eliminationRule primitive (.formation Δ (Expr.subst σ A) (Expr.subst (Expr.lift σ) B))
      (Fin.cases s.context (Fin.cases pa (Fin.cases pb (fun i => nomatch i))))
    have tyS : Proof (R := R) (H := H) Δ (.type (Expr.subst σ (S A B))) := by
      simpa [EliminationRule.schema, Judgment.type, Form.subst, subst_S] using pS
    have ss := lift structural s (S A B) tyS
    have sab := lift structural sa B pb
    have pS' := eliminationRule primitive (.formation Δ (Expr.subst σ A') (Expr.subst (Expr.lift σ) B'))
      (Fin.cases s.context (Fin.cases pa' (Fin.cases pb' (fun i => nomatch i))))
    have tyS' : Proof (R := R) (H := H) Δ (.type (Expr.subst σ (S A' B'))) := by
      simpa [EliminationRule.schema, Judgment.type, Form.subst, subst_S] using pS'
    have ss' := lift structural s (S A' B') tyS'
    have sab' := lift structural sa' B' pb'
    have h7 := rec 7 _ (Expr.lift σ) ss
    have h8 := rec 8 _ (Expr.lift σ) ss'
    have h9 := rec 9 _ (Expr.lift σ) ss
    have h10 := rec 10 _ (Expr.lift (Expr.lift σ)) sab
    have h11 := rec 11 _ (Expr.lift (Expr.lift σ)) sab'
    have h12 := rec 12 _ (Expr.lift (Expr.lift σ)) sab
    have h13 := rec 13 Δ σ s
    have h14 := rec 14 Δ σ s
    have h15 := rec 15 Δ σ s
    have result := app (.split Δ (Expr.subst σ A) (Expr.subst σ A') (Expr.subst (Expr.lift σ) B) (Expr.subst (Expr.lift σ) B') (Expr.subst (Expr.lift σ) D) (Expr.subst (Expr.lift σ) D') (Expr.subst (Expr.lift σ) e) (Expr.subst (Expr.lift σ) e') (Expr.subst σ p) (Expr.subst σ p'))
      (by
        refine (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => nomatch i)))))))))))))))))
        · exact s.context
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using pa
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using pa'
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using pb
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using pb'
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using hab
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using hbb
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using h7
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using h8
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using h9
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using h10
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using h11
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using h12
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using h13
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using h14
        · simpa [Proof, Judgment.ctx, Fin.succ, List.get, EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using h15
      )
    simpa [EliminationCongruence.schema, EliminationCongruence.families, EliminationCongruence.endpoints, Judgment.type, Judgment.typeEq, Judgment.term, Judgment.termEq, branchContext, Form.subst, subst_S, subst_pack, subst_split, subst_instantiate, -Expr.subst_rename, -Expr.rename_subst, ← flatten_subst, branchType_subst] using result
end TypedSubstitution

end SquareKit.DependentPairJudgments
