import SquareKit.DependentPairCongruence
import SquareKit.DependentPairEliminationJudgments

/-! Typed congruence for the independent eliminator signature. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations
open Elimination

inductive EliminationCongruence where
  | formation {V} (Γ : Context eliminationSignature V) (A A' : EExpr V)
      (B B' : EExpr (Fin 1 ⊕ V))
  | pack {V} (Γ : Context eliminationSignature V) (A A' : EExpr V)
      (B B' : EExpr (Fin 1 ⊕ V)) (a a' b b' : EExpr V)
  | split {V} (Γ : Context eliminationSignature V) (A A' : EExpr V)
      (B B' D D' : EExpr (Fin 1 ⊕ V)) (e e' : EExpr (Fin 2 ⊕ V)) (p p' : EExpr V)

namespace EliminationCongruence
open Judgment

def families (Γ : Context eliminationSignature V) (A A' : EExpr V)
    (B B' : EExpr (Fin 1 ⊕ V)) : List (Judgment eliminationSignature) :=
  [ctx Γ, type Γ A, type Γ A', type (.extend Γ A) B, type (.extend Γ A') B',
    typeEq Γ A A', typeEq (.extend Γ A) B B']

def endpoints (Γ : Context eliminationSignature V) (a b A : EExpr V) :=
  [term Γ a A, term Γ b A]

def schema : EliminationCongruence → Schema eliminationSignature
  | .formation Γ A A' B B' =>
      ⟨families Γ A A' B B', typeEq Γ (S A B) (S A' B')⟩
  | .pack Γ A A' B B' a a' b b' =>
      ⟨families Γ A A' B B' ++
        [termEq Γ a a' A, termEq Γ b b' (instantiate B a)] ++
        endpoints Γ (Elimination.pack A B a b) (Elimination.pack A' B' a' b') (S A B),
        termEq Γ (Elimination.pack A B a b) (Elimination.pack A' B' a' b') (S A B)⟩
  | .split Γ A A' B B' D D' e e' p p' =>
      ⟨families Γ A A' B B' ++
        [type (.extend Γ (S A B)) D, type (.extend Γ (S A' B')) D',
        typeEq (.extend Γ (S A B)) D D',
        term (branchContext Γ A B) (Expr.rename flattenToNested e) (branchType A B D),
        term (branchContext Γ A' B') (Expr.rename flattenToNested e') (branchType A' B' D'),
        termEq (branchContext Γ A B) (Expr.rename flattenToNested e)
          (Expr.rename flattenToNested e') (branchType A B D),
        termEq Γ p p' (S A B)] ++
        endpoints Γ (Elimination.split A B D e p) (Elimination.split A' B' D' e' p') (instantiate D p),
        termEq Γ (Elimination.split A B D e p) (Elimination.split A' B' D' e' p') (instantiate D p)⟩
end EliminationCongruence

/-- The final tables combine independent pair rules, typed declarations and
constructor congruence. The shared structural closure does not identify them. -/
def projectionPresentation (hasEta : Bool) : Rules (Judgment projectionSignature) :=
  closedRules (Sum.elim (ProjectionRule.schema (hasEta := hasEta))
    (Sum.elim ProjectionCongruence.schema
      (Sum.elim (DependentPairDeclarations.Rule.schema DependentPairDeclarations.projection)
        (DependentPairDeclarations.Congruence.schema DependentPairDeclarations.projection))))

def eliminationPresentation : Rules (Judgment eliminationSignature) :=
  closedRules (Sum.elim EliminationRule.schema
    (Sum.elim EliminationCongruence.schema
      (Sum.elim (DependentPairDeclarations.Rule.schema DependentPairDeclarations.elimination)
        (DependentPairDeclarations.Congruence.schema DependentPairDeclarations.elimination))))

end SquareKit.DependentPairJudgments
