import SquareKit.Internal.Cubical.Judgments.NaturalsSyntax
import SquareKit.Internal.Cubical.Dimensions

/-! Source interval expressions carry the existing free De Morgan syntax and
its syntactic conversion derivations. Their arguments remain typed terms. -/
namespace SquareKit.Cubical.Source.Intervals
open GuardedTheory

inductive Operation where
  | interval
  | dimension {n : ℕ} (e : Expr (Fin n))

abbrev extraSignature : Signature where
  Operation := Operation
  arity
    | .interval => 1
    | @Operation.dimension n _ => n+1
  Predicate := Empty
  arguments := Empty.elim

abbrev signature := Naturals.signature.sum extraSignature
abbrev Expression (V : Type) := GuardedTheory.Term signature V
abbrev Judgment (V : Type) := GuardedTheory.Atom signature V

variable {V : Type}
abbrev context (Γ : Expression V) : Judgment V := .pred (.inl (.inl (.inl (.inl .context)))) ![Γ]
abbrev family (Γ A : Expression V) : Judgment V := .pred (.inl (.inl (.inl (.inl .family)))) ![Γ,A]
abbrev term (Γ A t : Expression V) : Judgment V := .pred (.inl (.inl (.inl (.inl .term)))) ![Γ,A,t]
abbrev interval (Γ : Expression V) : Expression V := .app (.inr .interval) ![Γ]
abbrev dimension {n : ℕ} (e : Expr (Fin n)) (Γ : Expression V) (r : Fin n → Expression V) :
    Expression V := .app (.inr (.dimension e)) (Matrix.vecCons Γ r)

abbrev formationRule : Rule signature where
  parameterCount := 1
  hypotheses := 1
  premise := ![context (.var 0)]
  conclusion := family (.var 0) (interval (.var 0))

abbrev dimensionSchema (n : ℕ) (out : Judgment (Fin (n+1))) : Rule signature where
  parameterCount := n+1
  hypotheses := n+1
  premise := Fin.cases (context (.var 0))
    (fun i => term (.var 0) (interval (.var 0)) (.var i.succ))
  conclusion := out

abbrev dimensionRule {n : ℕ} (e : Expr (Fin n)) := dimensionSchema n
  (term (.var 0) (interval (.var 0)) (dimension e (.var 0) (fun i => .var i.succ)))
abbrev variableRule {n : ℕ} (k : Fin n) := dimensionSchema n
  (.eq (dimension (.var k) (.var 0) (fun i => .var i.succ)) (.var k.succ))
abbrev conversionRule {n : ℕ} (e e' : Expr (Fin n)) := dimensionSchema n
  (.eq (dimension e (.var 0) (fun i => .var i.succ))
    (dimension e' (.var 0) (fun i => .var i.succ)))
abbrev compositionRule {m n : ℕ} (e : Expr (Fin m)) (σ : Fin m → Expr (Fin n)) := dimensionSchema n
  (.eq (dimension (Expr.subst σ e) (.var 0) (fun i => .var i.succ))
    (dimension e (.var 0) (fun k => dimension (σ k) (.var 0) (fun i => .var i.succ))))

abbrev substitution (Δ Γ σ : Expression V) : Judgment V :=
  .pred (.inl (.inl (.inl (.inl .substitution)))) ![Δ,Γ,σ]
abbrev subTy (A σ : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl .subTy)))) ![A,σ]
abbrev subTm (t σ : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl .subTm)))) ![t,σ]

abbrev substitutionSchema (n : ℕ) (out : Judgment (Fin (n+3))) : Rule signature where
  parameterCount := n+3
  hypotheses := n+1
  premise := Fin.cases (substitution (.var 1) (.var 0) (.var 2))
    (fun i => term (.var 0) (interval (.var 0)) (.var i.succ.succ.succ))
  conclusion := out
abbrev intervalSubRule := substitutionSchema 0
  (.eq (subTy (interval (.var 0)) (.var 2)) (interval (.var 1)))
abbrev dimensionSubRule {n : ℕ} (e : Expr (Fin n)) := substitutionSchema n
  (.eq (subTm (dimension e (.var 0) (fun i => .var i.succ.succ.succ)) (.var 2))
    (dimension e (.var 1) (fun i => subTm (.var i.succ.succ.succ) (.var 2))))

end SquareKit.Cubical.Source.Intervals
