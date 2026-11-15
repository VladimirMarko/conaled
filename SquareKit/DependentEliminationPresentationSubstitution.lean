import SquareKit.DependentProjectionPresentationSubstitution
import SquareKit.DependentPairEliminationSubstitution

namespace SquareKit.DependentPairJudgments.TypedSubstitution
open DependentTheoryMaps DependentPairPresentations

def fullEliminationStructural :
    TheoryMap (structuralRules eliminationSignature) (eliminationPresentation) id where
  certificate r := Derivation.rule (R := eliminationPresentation) (.inl r)
    (fun i => .hyp ⟨i, rfl⟩)

def fullEliminationPrimitive :
    TheoryMap (rulesOf (EliminationRule.schema)) (eliminationPresentation) id where
  certificate r := Derivation.rule (R := eliminationPresentation) (.inr (.inl r))
    (fun i => .hyp ⟨i, rfl⟩)

def fullEliminationCongruence :
    TheoryMap (rulesOf EliminationCongruence.schema) (eliminationPresentation) id where
  certificate r := Derivation.rule (R := eliminationPresentation) (.inr (.inr (.inl r)))
    (fun i => .hyp ⟨i, rfl⟩)

def fullEliminationDeclaration :
    TheoryMap (rulesOf (DependentPairDeclarations.Rule.schema DependentPairDeclarations.elimination))
      (eliminationPresentation) id where
  certificate r := Derivation.rule (R := eliminationPresentation) (.inr (.inr (.inr (.inl r))))
    (fun i => .hyp ⟨i, rfl⟩)

def fullEliminationDeclarationCongruence :
    TheoryMap (rulesOf (DependentPairDeclarations.Congruence.schema DependentPairDeclarations.elimination))
      (eliminationPresentation) id where
  certificate r := Derivation.rule (R := eliminationPresentation) (.inr (.inr (.inr (.inr r))))
    (fun i => .hyp ⟨i, rfl⟩)

/-- All structural, pair, declaration and congruence rules participate in the
same admissibility theorem. Split remains an independently specified rule. -/
def fullEliminationLocal (H : Judgment eliminationSignature → Type) :
    Local (R := eliminationPresentation) (H := H) where
  step := sumStep _ _ (structuralStep (fullEliminationStructural))
    (sumStep _ _ (eliminationStep (fullEliminationStructural) (fullEliminationPrimitive))
      (sumStep _ _ (eliminationCongruenceStep (fullEliminationStructural) (fullEliminationPrimitive) (fullEliminationCongruence))
        (sumStep _ _
          (DependentPairDeclarations.declarationStep DependentPairDeclarations.elimination
            (fullEliminationDeclaration))
          (DependentPairDeclarations.declarationCongruenceStep DependentPairDeclarations.elimination
            (fullEliminationDeclarationCongruence)))))

def substituteFullElimination {j : Judgment eliminationSignature}
    (d : Derivation (eliminationPresentation) (fun _ => Empty) j) :
    Reindexed (R := eliminationPresentation) (H := fun _ => Empty) j :=
  substitute (fullEliminationLocal _) (fun _ h => Empty.elim h) d

end SquareKit.DependentPairJudgments.TypedSubstitution
