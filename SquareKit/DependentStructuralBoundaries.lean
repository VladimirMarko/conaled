import SquareKit.DependentContextualBoundaries

namespace SquareKit.DependentPairJudgments.ContextualBoundary
open DependentTheoryMaps DependentPairPresentations TypedSubstitution
variable {S : Signature} {R : Rules.{1,1} (Judgment S)} {H : Judgment S → Type}

private def extended (structural : TheoryMap (structuralRules S) R id)
    (Γ : Context S V) (A : Expr S V)
    (ctx : Derivation R H (.ctx Γ)) (type : Derivation R H (.type Γ A))
    (vars : ∀ v, Derivation R H (.type Γ (Γ.lookup v))) :
    ∀ v, Derivation R H (.type (.extend Γ A) ((Γ.extend A).lookup v)) := by
  intro v
  cases v with
  | inl i => exact weaken structural Γ A (.type A) ctx type type
  | inr v => exact weaken structural Γ A (.type (Γ.lookup v)) ctx type (vars v)

private def familyType (structural : TheoryMap (structuralRules S) R id)
    (laws : Local (R := R) (H := H))
    (stable : ∀ j, H j → Reindexed (R := R) (H := H) j)
    {Γ : Context S V} {A : Expr S V} {B : Expr S (Fin 1 ⊕ V)} {a : Expr S V}
    (ctx : Derivation R H (.ctx Γ)) (family : Derivation R H (.type (.extend Γ A) B))
    (term : Derivation R H (.term Γ a A)) :
    Derivation R H (.type Γ (Elimination.instantiate B a)) :=
  substitute laws stable family Γ _ (single structural Γ A a ctx term)

/-- Structural cases consume the recursively established boundaries of their
premises. In particular symmetry and conversion do not assume bare equality
hypotheses come with endpoints for free. -/
def structural
    (inclusion : TheoryMap (structuralRules S) R id)
    (laws : Local (R := R) (H := H))
    (stable : ∀ j, H j → Reindexed (R := R) (H := H) j)
    (r : StructuralRule S)
    (ps : ∀ i : Fin (StructuralRule.schema r).premises.length,
      Derivation R H ((StructuralRule.schema r).premises.get i))
    (bs : ∀ i : Fin (StructuralRule.schema r).premises.length,
      ContextualBoundary R H ((StructuralRule.schema r).premises.get i)) :
    ContextualBoundary R H (StructuralRule.schema r).conclusion := by
  cases r with
  | empty => intro v; exact Empty.elim v
  | extend Γ A =>
      dsimp [StructuralRule.schema] at ps bs
      exact extended inclusion Γ A (ps 0) (ps 1) (bs 0)
  | «variable» Γ v =>
      dsimp [StructuralRule.schema] at ps bs
      exact ⟨ps 0, bs 0 v⟩
  | weaken Γ A φ =>
      dsimp [StructuralRule.schema] at ps bs
      have ctx := rule inclusion (.extend Γ A) (Fin.cases (ps 0) (Fin.cases (ps 1) (fun i => Fin.elim0 i)))
      cases φ with
      | ctx => exact extended inclusion Γ A (ps 0) (ps 1) (bs 0)
      | type B => exact ctx
      | term b B => exact ⟨ctx, weaken inclusion Γ A (.type B) (ps 0) (ps 1) (bs 2).2⟩
      | typeEq B C => exact ⟨ctx,
          weaken inclusion Γ A (.type B) (ps 0) (ps 1) (bs 2).2.1,
          weaken inclusion Γ A (.type C) (ps 0) (ps 1) (bs 2).2.2⟩
      | termEq a b B => exact ⟨ctx,
          weaken inclusion Γ A (.type B) (ps 0) (ps 1) (bs 2).2.1,
          weaken inclusion Γ A (.term a B) (ps 0) (ps 1) (bs 2).2.2.1,
          weaken inclusion Γ A (.term b B) (ps 0) (ps 1) (bs 2).2.2.2⟩
  | typeRefl Γ A =>
      dsimp [StructuralRule.schema] at ps bs
      exact ⟨bs 0, ps 0, ps 0⟩
  | typeSymm Γ A B =>
      dsimp [StructuralRule.schema] at ps bs
      exact ⟨(bs 0).1, (bs 0).2.2, (bs 0).2.1⟩
  | typeTrans Γ A B C =>
      dsimp [StructuralRule.schema] at ps bs
      exact ⟨(bs 0).1, (bs 0).2.1, (bs 1).2.2⟩
  | termRefl Γ a A =>
      dsimp [StructuralRule.schema] at ps bs
      exact ⟨(bs 0).1, (bs 0).2, ps 0, ps 0⟩
  | termSymm Γ a b A =>
      dsimp [StructuralRule.schema] at ps bs
      exact ⟨(bs 0).1, (bs 0).2.1, (bs 0).2.2.2, (bs 0).2.2.1⟩
  | termTrans Γ a b c A =>
      dsimp [StructuralRule.schema] at ps bs
      exact ⟨(bs 0).1, (bs 0).2.1, (bs 0).2.2.1, (bs 1).2.2.2⟩
  | convert Γ a A B =>
      dsimp [StructuralRule.schema] at ps bs
      exact ⟨(bs 0).1, (bs 1).2.2⟩
  | convertEq Γ a b A B =>
      dsimp [StructuralRule.schema] at ps bs
      have left := rule inclusion (.convert Γ a A B)
        (Fin.cases (bs 0).2.2.1 (Fin.cases (ps 1) (fun i => Fin.elim0 i)))
      have right := rule inclusion (.convert Γ b A B)
        (Fin.cases (bs 0).2.2.2 (Fin.cases (ps 1) (fun i => Fin.elim0 i)))
      exact ⟨(bs 0).1, (bs 1).2.2, left, right⟩
  | familyCong Γ A B a b =>
      dsimp [StructuralRule.schema] at ps bs
      exact ⟨ps 0, familyType inclusion laws stable (ps 0) (ps 2) (bs 3).2.2.1,
        familyType inclusion laws stable (ps 0) (ps 2) (bs 3).2.2.2⟩
end SquareKit.DependentPairJudgments.ContextualBoundary
