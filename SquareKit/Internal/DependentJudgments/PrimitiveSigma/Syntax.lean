import SquareKit.Internal.DependentJudgments.Theory

/-! Primitive dependent-sum syntax with an explicit motive argument. -/
namespace SquareKit.Internal.DependentJudgments.PrimitiveSigma
open GuardedTheory

inductive Operation where
  | sigma | pack | split
  deriving DecidableEq

abbrev extraSignature : Signature where
  Operation := Operation
  arity
    | .sigma | .pack => 2
    | .split => 4
  Predicate := Empty
  arguments := Empty.elim

abbrev signature := Contextual.signature.sum extraSignature
abbrev Expression (V : Type) := Term signature V
abbrev Judgment (V : Type) := Atom signature V

variable {V : Type}
abbrev context (Γ : Expression V) : Judgment V := .pred (.inl (.inl .context)) ![Γ]
abbrev family (Γ A : Expression V) : Judgment V := .pred (.inl (.inl .family)) ![Γ, A]
abbrev term (Γ A t : Expression V) : Judgment V := .pred (.inl (.inl .term)) ![Γ, A, t]
abbrev substitution (Δ Γ σ : Expression V) : Judgment V :=
  .pred (.inl (.inl .substitution)) ![Δ, Γ, σ]
abbrev extend (Γ A : Expression V) : Expression V := .app (.inl (.inl .extend)) ![Γ, A]
abbrev identitySub (Γ : Expression V) : Expression V := .app (.inl (.inl .id)) ![Γ]
abbrev comp (σ τ : Expression V) : Expression V := .app (.inl (.inl .comp)) ![σ, τ]
abbrev subTy (A σ : Expression V) : Expression V := .app (.inl (.inl .subTy)) ![A, σ]
abbrev subTm (t σ : Expression V) : Expression V := .app (.inl (.inl .subTm)) ![t, σ]
abbrev weaken (Γ A : Expression V) : Expression V := .app (.inl (.inl .weaken)) ![Γ, A]
abbrev generic (Γ A : Expression V) : Expression V := .app (.inl (.inl .generic)) ![Γ, A]
abbrev pairSub (A σ t : Expression V) : Expression V := .app (.inl (.inl .pair)) ![A, σ, t]
abbrev sigma (A B : Expression V) : Expression V := .app (.inr .sigma) ![A, B]
abbrev pack (A B : Expression V) : Expression V := .app (.inr .pack) ![A, B]
/-- The two-entry dependent branch context. -/
abbrev branchContext (Γ A B : Expression V) := extend (extend Γ A) B
/-- Pairing is a section of the new object type, not a contextual package. -/
abbrev pair (Γ A B a b : Expression V) : Expression V :=
  subTm (generic Γ (sigma A B))
    (comp (pack A B) (pairSub B (pairSub A (identitySub Γ) a) b))
/-- The generic dependent eliminator returns a section over Γ.Σ(A,B). Its
branch has type C[pack] in Γ.A.B. An instance at p is obtained by substitution. -/
abbrev split (A B C d : Expression V) : Expression V := .app (.inr .split) ![A, B, C, d]

abbrev formationSchema (out : Judgment (Fin 3)) : Rule signature where
  parameterCount := 3
  hypotheses := 2
  premise := ![family (.var 0) (.var 1), family (extend (.var 0) (.var 1)) (.var 2)]
  conclusion := out
abbrev formationRule := formationSchema (family (.var 0) (sigma (.var 1) (.var 2)))
abbrev packRule := formationSchema
  (substitution (branchContext (.var 0) (.var 1) (.var 2))
    (extend (.var 0) (sigma (.var 1) (.var 2))) (pack (.var 1) (.var 2)))
abbrev packOverRule := formationSchema
  (.eq (comp (weaken (.var 0) (sigma (.var 1) (.var 2))) (pack (.var 1) (.var 2)))
    (comp (weaken (.var 0) (.var 1)) (weaken (extend (.var 0) (.var 1)) (.var 2))))

abbrev splitSchema (out : Judgment (Fin 5)) : Rule signature where
  parameterCount := 5
  hypotheses := 4
  premise := ![family (.var 0) (.var 1), family (extend (.var 0) (.var 1)) (.var 2),
    family (extend (.var 0) (sigma (.var 1) (.var 2))) (.var 3),
    term (branchContext (.var 0) (.var 1) (.var 2))
      (subTy (.var 3) (pack (.var 1) (.var 2))) (.var 4)]
  conclusion := out
abbrev splitRule := splitSchema
  (term (extend (.var 0) (sigma (.var 1) (.var 2))) (.var 3)
    (split (.var 1) (.var 2) (.var 3) (.var 4)))
abbrev splitBetaRule := splitSchema
  (.eq (subTm (split (.var 1) (.var 2) (.var 3) (.var 4)) (pack (.var 1) (.var 2))) (.var 4))

abbrev pairSchema (out : Judgment (Fin 5)) : Rule signature where
  parameterCount := 5
  hypotheses := 4
  premise := ![family (.var 0) (.var 1), family (extend (.var 0) (.var 1)) (.var 2),
    term (.var 0) (.var 1) (.var 3),
    term (.var 0) (subTy (.var 2) (pairSub (.var 1) (identitySub (.var 0)) (.var 3))) (.var 4)]
  conclusion := out
abbrev pairRule := pairSchema
  (term (.var 0) (sigma (.var 1) (.var 2))
    (pair (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)))

end SquareKit.Internal.DependentJudgments.PrimitiveSigma
