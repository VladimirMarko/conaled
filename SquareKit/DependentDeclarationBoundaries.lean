import SquareKit.DependentStructuralBoundaries
import SquareKit.DependentDeclarationSubstitution

namespace SquareKit.DependentPairDeclarations
open DependentTheoryMaps DependentPairJudgments
variable {S : Signature} {R : Rules.{1,1} (Judgment S)} {H : Judgment S → Type}

private def applyRule (D : OperationMap signature S)
    (primitive : TheoryMap (rulesOf (Rule.schema D)) R id) (r : Rule S)
    (ps : ∀ i : Fin (r.schema D).premises.length, Derivation R H ((r.schema D).premises.get i)) :
    Derivation R H (r.schema D).conclusion :=
  (primitive.certificate r).graft (fun _ h => h.property ▸ ps h.val)

/-- The ordered declaration table supplies the result-type boundary of each
selected term using only earlier declarations. -/
def declarationBoundary (D : OperationMap signature S)
    (primitive : TheoryMap (rulesOf (Rule.schema D)) R id) (r : Rule S)
    (ps : ∀ i : Fin (r.schema D).premises.length, Derivation R H ((r.schema D).premises.get i)) :
    ContextualBoundary R H (r.schema D).conclusion := by
  cases r with
  | N Γ => exact ps ⟨0, Nat.zero_lt_one⟩
  | B Γ n => dsimp [Rule.schema] at ps; exact ps 0
  | C Γ n y => dsimp [Rule.schema] at ps; exact ps 0
  | s Γ m =>
      dsimp [Rule.schema] at ps
      exact ⟨ps 0, applyRule D primitive (.N Γ) (Fin.cases (ps 0) (fun i => Fin.elim0 i))⟩
  | d Γ m =>
      dsimp [Rule.schema] at ps
      exact ⟨ps 0, applyRule D primitive (.N Γ) (Fin.cases (ps 0) (fun i => Fin.elim0 i))⟩
  | t Γ m =>
      dsimp [Rule.schema] at ps
      have sm := applyRule D primitive (.s Γ m) ps
      exact ⟨ps 0, applyRule D primitive (.B Γ (Terms.s D m))
        (Fin.cases (ps 0) (Fin.cases sm (fun i => Fin.elim0 i)))⟩
  | u Γ m =>
      dsimp [Rule.schema] at ps
      have sm := applyRule D primitive (.s Γ m) ps
      have tm := applyRule D primitive (.t Γ m) ps
      exact ⟨ps 0, applyRule D primitive (.C Γ (Terms.s D m) (Terms.t D m))
        (Fin.cases (ps 0) (Fin.cases sm (Fin.cases tm (fun i => Fin.elim0 i))))⟩

/-- Declaration congruence consumes typed equality boundaries and any explicitly
required converted endpoint; it does not assume equality is untyped. -/
def declarationCongruenceBoundary (D : OperationMap signature S)
    (primitive : TheoryMap (rulesOf (Rule.schema D)) R id) (r : Congruence S)
    (ps : ∀ i : Fin (r.schema D).premises.length, Derivation R H ((r.schema D).premises.get i))
    (bs : ∀ i : Fin (r.schema D).premises.length, ContextualBoundary R H ((r.schema D).premises.get i)) :
    ContextualBoundary R H (r.schema D).conclusion := by
  cases r with
  | B Γ n n' =>
      dsimp [Congruence.schema] at ps bs
      exact ⟨ps 0,
        applyRule D primitive (.B Γ n) (Fin.cases (ps 0) (Fin.cases (bs 1).2.2.1 (fun i => Fin.elim0 i))),
        applyRule D primitive (.B Γ n') (Fin.cases (ps 0) (Fin.cases (bs 1).2.2.2 (fun i => Fin.elim0 i)))⟩
  | C Γ n n' y y' =>
      dsimp [Congruence.schema] at ps bs
      exact ⟨ps 0,
        applyRule D primitive (.C Γ n y)
          (Fin.cases (ps 0) (Fin.cases (bs 1).2.2.1 (Fin.cases (bs 2).2.2.1 (fun i => Fin.elim0 i)))),
        applyRule D primitive (.C Γ n' y')
          (Fin.cases (ps 0) (Fin.cases (bs 1).2.2.2 (Fin.cases (ps 3) (fun i => Fin.elim0 i))))⟩
  | s Γ m m' =>
      dsimp [Congruence.schema] at ps bs
      exact ⟨ps 0,
        applyRule D primitive (.N Γ) (Fin.cases (ps 0) (fun i => Fin.elim0 i)),
        applyRule D primitive (.s Γ m) (Fin.cases (ps 0) (Fin.cases (bs 1).2.2.1 (fun i => Fin.elim0 i))),
        applyRule D primitive (.s Γ m') (Fin.cases (ps 0) (Fin.cases (bs 1).2.2.2 (fun i => Fin.elim0 i)))⟩
  | d Γ m m' =>
      dsimp [Congruence.schema] at ps bs
      exact ⟨ps 0,
        applyRule D primitive (.N Γ) (Fin.cases (ps 0) (fun i => Fin.elim0 i)),
        applyRule D primitive (.d Γ m) (Fin.cases (ps 0) (Fin.cases (bs 1).2.2.1 (fun i => Fin.elim0 i))),
        applyRule D primitive (.d Γ m') (Fin.cases (ps 0) (Fin.cases (bs 1).2.2.2 (fun i => Fin.elim0 i)))⟩
  | t Γ m m' =>
      dsimp [Congruence.schema] at ps bs
      have args : (i : Fin 2) → Derivation R H ([Judgment.ctx Γ, Judgment.term Γ m (Terms.N D)].get i) := Fin.cases (ps 0) (Fin.cases (bs 1).2.2.1 (fun i => Fin.elim0 i))
      exact ⟨ps 0, (declarationBoundary D primitive (.t Γ m) args).2,
        applyRule D primitive (.t Γ m) args, ps 2⟩
  | u Γ m m' =>
      dsimp [Congruence.schema] at ps bs
      have args : (i : Fin 2) → Derivation R H ([Judgment.ctx Γ, Judgment.term Γ m (Terms.N D)].get i) := Fin.cases (ps 0) (Fin.cases (bs 1).2.2.1 (fun i => Fin.elim0 i))
      exact ⟨ps 0, (declarationBoundary D primitive (.u Γ m) args).2,
        applyRule D primitive (.u Γ m) args, ps 2⟩
end SquareKit.DependentPairDeclarations
