import SquareKit.DependentPairDeclarations

/-! Typed constructor congruence for projection presentations. Common endpoint
boundaries are explicit; unequal raw types are not silently identified. -/
namespace SquareKit.DependentPairJudgments
open DependentTheoryMaps DependentPairPresentations
open Elimination (instantiate)

inductive ProjectionCongruence where
  | formation {V} (Γ : Context projectionSignature V) (A A' : PExpr V)
      (B B' : PExpr (Fin 1 ⊕ V))
  | pair {V} (Γ : Context projectionSignature V) (A A' : PExpr V)
      (B B' : PExpr (Fin 1 ⊕ V)) (a a' b b' : PExpr V)
  | first {V} (Γ : Context projectionSignature V) (A A' : PExpr V)
      (B B' : PExpr (Fin 1 ⊕ V)) (p p' : PExpr V)
  | second {V} (Γ : Context projectionSignature V) (A A' : PExpr V)
      (B B' : PExpr (Fin 1 ⊕ V)) (p p' : PExpr V)

namespace ProjectionCongruence
open Judgment Projection

def families (Γ : Context projectionSignature V) (A A' : PExpr V)
    (B B' : PExpr (Fin 1 ⊕ V)) : List (Judgment projectionSignature) :=
  [ctx Γ, type Γ A, type Γ A', type (.extend Γ A) B, type (.extend Γ A') B',
    typeEq Γ A A', typeEq (.extend Γ A) B B']

/-- The two term endpoints are checked at the same stated type. -/
def endpoints (Γ : Context projectionSignature V) (a b A : PExpr V) :=
  [term Γ a A, term Γ b A]

def schema : ProjectionCongruence → Schema projectionSignature
  | .formation Γ A A' B B' =>
      ⟨families Γ A A' B B', typeEq Γ (P A B) (P A' B')⟩
  | .pair Γ A A' B B' a a' b b' =>
      ⟨families Γ A A' B B' ++
        [termEq Γ a a' A, termEq Γ b b' (instantiate B a)] ++
        endpoints Γ (Projection.pair A B a b) (Projection.pair A' B' a' b') (P A B),
        termEq Γ (Projection.pair A B a b) (Projection.pair A' B' a' b') (P A B)⟩
  | .first Γ A A' B B' p p' =>
      ⟨families Γ A A' B B' ++ [termEq Γ p p' (P A B)] ++
        endpoints Γ (fst A B p) (fst A' B' p') A,
        termEq Γ (fst A B p) (fst A' B' p') A⟩
  | .second Γ A A' B B' p p' =>
      ⟨families Γ A A' B B' ++ [termEq Γ p p' (P A B)] ++
        endpoints Γ (snd A B p) (snd A' B' p') (instantiate B (fst A B p)),
        termEq Γ (snd A B p) (snd A' B' p') (instantiate B (fst A B p))⟩
end ProjectionCongruence

end SquareKit.DependentPairJudgments

namespace SquareKit.DependentPairDeclarations
open DependentTheoryMaps DependentPairPresentations DependentPairJudgments

inductive Congruence (S : Signature) where
  | B {V} (Γ : Context S V) (n n' : Expr S V)
  | C {V} (Γ : Context S V) (n n' y y' : Expr S V)
  | s {V} (Γ : Context S V) (m m' : Expr S V)
  | d {V} (Γ : Context S V) (m m' : Expr S V)
  | t {V} (Γ : Context S V) (m m' : Expr S V)
  | u {V} (Γ : Context S V) (m m' : Expr S V)

def Congruence.schema (D : OperationMap signature S) : Congruence S → Schema S
  | .B Γ n n' =>
      ⟨[.ctx Γ, .termEq Γ n n' (Terms.N D)], .typeEq Γ (Terms.B D n) (Terms.B D n')⟩
  | .C Γ n n' y y' =>
      ⟨[.ctx Γ, .termEq Γ n n' (Terms.N D), .termEq Γ y y' (Terms.B D n),
        .term Γ y' (Terms.B D n')], .typeEq Γ (Terms.C D n y) (Terms.C D n' y')⟩
  | .s Γ m m' =>
      ⟨[.ctx Γ, .termEq Γ m m' (Terms.N D)],
        .termEq Γ (Terms.s D m) (Terms.s D m') (Terms.N D)⟩
  | .d Γ m m' =>
      ⟨[.ctx Γ, .termEq Γ m m' (Terms.N D)],
        .termEq Γ (Terms.d D m) (Terms.d D m') (Terms.N D)⟩
  | .t Γ m m' =>
      ⟨[.ctx Γ, .termEq Γ m m' (Terms.N D),
        .term Γ (Terms.t D m') (Terms.B D (Terms.s D m))],
        .termEq Γ (Terms.t D m) (Terms.t D m') (Terms.B D (Terms.s D m))⟩
  | .u Γ m m' =>
      ⟨[.ctx Γ, .termEq Γ m m' (Terms.N D),
        .term Γ (Terms.u D m') (Terms.C D (Terms.s D m) (Terms.t D m))],
        .termEq Γ (Terms.u D m) (Terms.u D m') (Terms.C D (Terms.s D m) (Terms.t D m))⟩

end SquareKit.DependentPairDeclarations
