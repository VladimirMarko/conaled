import SquareKit.Internal.Cubical.Judgments.SumsSyntax

/-! Natural number source rules. The successor method binds both the number
and the induction hypothesis through ordinary comprehension contexts. -/
namespace SquareKit.Cubical.Source.Naturals
open GuardedTheory

inductive Operation where
  | nat | zero | succ | elim
  deriving DecidableEq

abbrev extraSignature : Signature where
  Operation := Operation
  arity
    | .nat | .zero => 1
    | .succ => 2
    | .elim => 4
  Predicate := Empty
  arguments := Empty.elim

abbrev signature := Sums.signature.sum extraSignature
abbrev Expression (V : Type) := GuardedTheory.Term signature V
abbrev Judgment (V : Type) := GuardedTheory.Atom signature V

variable {V : Type}
abbrev context (Γ : Expression V) : Judgment V := .pred (.inl (.inl (.inl .context))) ![Γ]
abbrev family (Γ A : Expression V) : Judgment V := .pred (.inl (.inl (.inl .family))) ![Γ,A]
abbrev term (Γ A t : Expression V) : Judgment V := .pred (.inl (.inl (.inl .term))) ![Γ,A,t]
abbrev extend (Γ A : Expression V) : Expression V := .app (.inl (.inl (.inl .extend))) ![Γ,A]
abbrev identity (Γ : Expression V) : Expression V := .app (.inl (.inl (.inl .id))) ![Γ]
abbrev comp (σ τ : Expression V) : Expression V := .app (.inl (.inl (.inl .comp))) ![σ,τ]
abbrev subTy (A σ : Expression V) : Expression V := .app (.inl (.inl (.inl .subTy))) ![A,σ]
abbrev subTm (t σ : Expression V) : Expression V := .app (.inl (.inl (.inl .subTm))) ![t,σ]
abbrev weaken (Γ A : Expression V) : Expression V := .app (.inl (.inl (.inl .weaken))) ![Γ,A]
abbrev generic (Γ A : Expression V) : Expression V := .app (.inl (.inl (.inl .generic))) ![Γ,A]
abbrev pair (A σ t : Expression V) : Expression V := .app (.inl (.inl (.inl .pair))) ![A,σ,t]
abbrev nat (Γ : Expression V) : Expression V := .app (.inr .nat) ![Γ]
abbrev zero (Γ : Expression V) : Expression V := .app (.inr .zero) ![Γ]
abbrev succ (Γ n : Expression V) : Expression V := .app (.inr .succ) ![Γ,n]
abbrev elim (Γ B z s : Expression V) : Expression V := .app (.inr .elim) ![Γ,B,z,s]
abbrev zeroSub (Γ : Expression V) := pair (nat Γ) (identity Γ) (zero Γ)
abbrev successorSub (Γ : Expression V) :=
  pair (nat Γ) (weaken Γ (nat Γ)) (succ (extend Γ (nat Γ)) (generic Γ (nat Γ)))
abbrev stepType (Γ B : Expression V) :=
  subTy B (comp (successorSub Γ) (weaken (extend Γ (nat Γ)) B))

abbrev contextSchema (out : Judgment (Fin 1)) : Rule signature where
  parameterCount := 1
  hypotheses := 1
  premise := ![context (.var 0)]
  conclusion := out
abbrev formationRule := contextSchema (family (.var 0) (nat (.var 0)))
abbrev zeroRule := contextSchema (term (.var 0) (nat (.var 0)) (zero (.var 0)))

abbrev successorSchema (out : Judgment (Fin 2)) : Rule signature where
  parameterCount := 2
  hypotheses := 2
  premise := ![context (.var 0),term (.var 0) (nat (.var 0)) (.var 1)]
  conclusion := out
abbrev successorRule := successorSchema
  (term (.var 0) (nat (.var 0)) (succ (.var 0) (.var 1)))

abbrev eliminationSchema (out : Judgment (Fin 4)) : Rule signature where
  parameterCount := 4
  hypotheses := 4
  premise := ![context (.var 0), family (extend (.var 0) (nat (.var 0))) (.var 1),
    term (.var 0) (subTy (.var 1) (zeroSub (.var 0))) (.var 2),
    term (extend (extend (.var 0) (nat (.var 0))) (.var 1))
      (stepType (.var 0) (.var 1)) (.var 3)]
  conclusion := out
abbrev eliminationRule := eliminationSchema
  (term (extend (.var 0) (nat (.var 0))) (.var 1) (elim (.var 0) (.var 1) (.var 2) (.var 3)))
abbrev zeroBetaRule := eliminationSchema
  (.eq (subTm (elim (.var 0) (.var 1) (.var 2) (.var 3)) (zeroSub (.var 0))) (.var 2))
abbrev successorBetaRule := eliminationSchema
  (.eq (subTm (elim (.var 0) (.var 1) (.var 2) (.var 3)) (successorSub (.var 0)))
    (subTm (.var 3) (pair (.var 1) (identity (extend (.var 0) (nat (.var 0))))
      (elim (.var 0) (.var 1) (.var 2) (.var 3)))))

end SquareKit.Cubical.Source.Naturals
