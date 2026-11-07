import SquareKit.DependentDeclarationBoundaries

namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations TypedSubstitution

namespace ContextualBoundary
variable {eta : Bool} {R : Rules.{1,1} (Judgment projectionSignature)}
  {H : Judgment projectionSignature → Type}

/-- Pair congruence retains explicitly typed endpoints; type congruence forms
both pair types independently in their respective dependent telescopes. -/
def projectionCongruence
    (primitive : TheoryMap (rulesOf (ProjectionRule.schema (hasEta := eta))) R id)
    (r : ProjectionCongruence)
    (ps : ∀ i : Fin (ProjectionCongruence.schema r).premises.length,
      Derivation R H ((ProjectionCongruence.schema r).premises.get i))
    (bs : ∀ i : Fin (ProjectionCongruence.schema r).premises.length,
      ContextualBoundary R H ((ProjectionCongruence.schema r).premises.get i)) :
    ContextualBoundary R H (ProjectionCongruence.schema r).conclusion := by
  let app (r : ProjectionRule eta)
      (children : ∀ i : Fin (ProjectionRule.schema r).premises.length,
        Derivation R H ((ProjectionRule.schema r).premises.get i)) :
      Derivation R H (ProjectionRule.schema r).conclusion :=
    (primitive.certificate r).graft (fun _ h => h.property ▸ children h.val)
  cases r with
  | formation Γ A A' B B' =>
      dsimp [ProjectionCongruence.schema, ProjectionCongruence.families] at ps bs
      exact ⟨ps 0,
        app (.formation Γ A B) (Fin.cases (ps 0) (Fin.cases (ps 1) (Fin.cases (ps 3) (fun i => Fin.elim0 i)))),
        app (.formation Γ A' B') (Fin.cases (ps 0) (Fin.cases (ps 2) (Fin.cases (ps 4) (fun i => Fin.elim0 i))))⟩
  | pair Γ A A' B B' a a' b b' =>
      dsimp [ProjectionCongruence.schema, ProjectionCongruence.families, ProjectionCongruence.endpoints] at ps bs
      exact ⟨ps 0, (bs 9).2, ps 9, ps 10⟩
  | first Γ A A' B B' p p' =>
      dsimp [ProjectionCongruence.schema, ProjectionCongruence.families, ProjectionCongruence.endpoints] at ps bs
      exact ⟨ps 0, (bs 8).2, ps 8, ps 9⟩
  | second Γ A A' B B' p p' =>
      dsimp [ProjectionCongruence.schema, ProjectionCongruence.families, ProjectionCongruence.endpoints] at ps bs
      exact ⟨ps 0, (bs 8).2, ps 8, ps 9⟩
end ContextualBoundary

/-- Recursive boundary reconstruction for every rule in either full projection
presentation, under an explicit instantiation action for open hypotheses. -/
def projectionBoundaryLaws (eta : Bool) (H : Judgment projectionSignature → Type)
    (stable : ∀ j, H j → Reindexed (R := projectionPresentation eta) (H := H) j) :
    LocalContextualBoundary (projectionPresentation eta) H where
  step r ps bs := by
    cases r with
    | inl r =>
        exact ContextualBoundary.structural (fullProjectionStructural eta)
          (fullProjectionLocal eta H) stable r ps bs
    | inr r =>
      cases r with
      | inl r =>
          exact ContextualBoundary.projectionPrimitive (fullProjectionStructural eta)
            (fullProjectionPrimitive eta) (fullProjectionLocal eta H) stable r ps
      | inr r =>
        cases r with
        | inl r =>
            exact ContextualBoundary.projectionCongruence (fullProjectionPrimitive eta) r ps bs
        | inr r =>
          cases r with
          | inl r =>
              exact DependentPairDeclarations.declarationBoundary
                DependentPairDeclarations.projection (fullProjectionDeclaration eta) r ps
          | inr r =>
              exact DependentPairDeclarations.declarationCongruenceBoundary
                DependentPairDeclarations.projection (fullProjectionDeclaration eta) r ps bs

/-- All closed derivations have their actual contextual presuppositions. This
covers both equality endpoints, not just context formation. -/
def projectionPresuppositions (eta : Bool) {j : Judgment projectionSignature}
    (d : Derivation (projectionPresentation eta) (fun _ => Empty) j) :
    ContextualBoundary (projectionPresentation eta) (fun _ => Empty) j :=
  contextualPresuppositions (projectionBoundaryLaws eta _ (fun _ h => Empty.elim h))
    (fun _ h => Empty.elim h) d

end SquareKit.DependentPairJudgments
