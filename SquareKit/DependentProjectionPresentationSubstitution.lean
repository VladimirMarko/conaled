import SquareKit.DependentProjectionCongruenceSubstitution
import SquareKit.DependentDeclarationSubstitution
import SquareKit.DependentPairEliminationCongruence

namespace SquareKit.DependentPairJudgments.TypedSubstitution
open DependentTheoryMaps DependentPairPresentations

/-- Reindexing reconstruction assembles by disjoint rule-table sum; no fresh
whole-derivation induction is needed when adding a table. -/
def sumStep {S : Signature} {R : Rules (Judgment S)} {H : Judgment S → Type}
    {L M : Type 1} (left : L → Schema S) (right : M → Schema S)
    (ls : ∀ r, (∀ i : Fin (left r).premises.length,
      Reindexed (R := R) (H := H) ((left r).premises.get i)) →
      Reindexed (R := R) (H := H) (left r).conclusion)
    (rs : ∀ r, (∀ i : Fin (right r).premises.length,
      Reindexed (R := R) (H := H) ((right r).premises.get i)) →
      Reindexed (R := R) (H := H) (right r).conclusion)
    (r : L ⊕ M)
    (rec : ∀ i : Fin (Sum.elim left right r).premises.length,
      Reindexed (R := R) (H := H) ((Sum.elim left right r).premises.get i)) :
    Reindexed (R := R) (H := H) (Sum.elim left right r).conclusion :=
  match r with
  | .inl r => ls r rec
  | .inr r => rs r rec

def fullProjectionStructural (eta : Bool) :
    TheoryMap (structuralRules projectionSignature) (projectionPresentation eta) id where
  certificate r := Derivation.rule (R := projectionPresentation eta) (.inl r)
    (fun i => .hyp ⟨i, rfl⟩)

def fullProjectionPrimitive (eta : Bool) :
    TheoryMap (rulesOf (ProjectionRule.schema (hasEta := eta))) (projectionPresentation eta) id where
  certificate r := Derivation.rule (R := projectionPresentation eta) (.inr (.inl r))
    (fun i => .hyp ⟨i, rfl⟩)

def fullProjectionCongruence (eta : Bool) :
    TheoryMap (rulesOf ProjectionCongruence.schema) (projectionPresentation eta) id where
  certificate r := Derivation.rule (R := projectionPresentation eta) (.inr (.inr (.inl r)))
    (fun i => .hyp ⟨i, rfl⟩)

def fullProjectionDeclaration (eta : Bool) :
    TheoryMap (rulesOf (DependentPairDeclarations.Rule.schema DependentPairDeclarations.projection))
      (projectionPresentation eta) id where
  certificate r := Derivation.rule (R := projectionPresentation eta) (.inr (.inr (.inr (.inl r))))
    (fun i => .hyp ⟨i, rfl⟩)

def fullProjectionDeclarationCongruence (eta : Bool) :
    TheoryMap (rulesOf (DependentPairDeclarations.Congruence.schema DependentPairDeclarations.projection))
      (projectionPresentation eta) id where
  certificate r := Derivation.rule (R := projectionPresentation eta) (.inr (.inr (.inr (.inr r))))
    (fun i => .hyp ⟨i, rfl⟩)

/-- All structural, pair, declaration and congruence rules participate in the
same admissibility theorem; eta remains a separately chosen table parameter. -/
def fullProjectionLocal (eta : Bool) (H : Judgment projectionSignature → Type) :
    Local (R := projectionPresentation eta) (H := H) where
  step := sumStep _ _ (structuralStep (fullProjectionStructural eta))
    (sumStep _ _ (projectionStep (fullProjectionStructural eta) (fullProjectionPrimitive eta))
      (sumStep _ _ (projectionCongruenceStep (fullProjectionStructural eta) (fullProjectionCongruence eta))
        (sumStep _ _
          (DependentPairDeclarations.declarationStep DependentPairDeclarations.projection
            (fullProjectionDeclaration eta))
          (DependentPairDeclarations.declarationCongruenceStep DependentPairDeclarations.projection
            (fullProjectionDeclarationCongruence eta)))))

def substituteFullProjection (eta : Bool) {j : Judgment projectionSignature}
    (d : Derivation (projectionPresentation eta) (fun _ => Empty) j) :
    Reindexed (R := projectionPresentation eta) (H := fun _ => Empty) j :=
  substitute (fullProjectionLocal eta _) (fun _ h => Empty.elim h) d

end SquareKit.DependentPairJudgments.TypedSubstitution
