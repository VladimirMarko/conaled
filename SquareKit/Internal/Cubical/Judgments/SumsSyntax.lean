import SquareKit.Internal.Cubical.Judgments.ProductsSyntax

/-! Dependent sums are specified by formation and inverse maps between
Γ.A.B and Γ.(Σ A B). Substitution along unpacking is dependent elimination. -/
namespace SquareKit.Cubical.Source.Sums
open GuardedTheory

inductive Operation where
  | sigma | pack | unpack
  deriving DecidableEq

abbrev extraSignature : Signature where
  Operation := Operation
  arity _ := 2
  Predicate := Empty
  arguments := Empty.elim

abbrev signature := Products.signature.sum extraSignature
abbrev Expression (V : Type) := GuardedTheory.Term signature V
abbrev Judgment (V : Type) := GuardedTheory.Atom signature V

variable {V : Type}
abbrev family (Γ A : Expression V) : Judgment V := .pred (.inl (.inl .family)) ![Γ,A]
abbrev substitution (Δ Γ σ : Expression V) : Judgment V :=
  .pred (.inl (.inl .substitution)) ![Δ,Γ,σ]
abbrev extend (Γ A : Expression V) : Expression V := .app (.inl (.inl .extend)) ![Γ,A]
abbrev identity (Γ : Expression V) : Expression V := .app (.inl (.inl .id)) ![Γ]
abbrev comp (σ τ : Expression V) : Expression V := .app (.inl (.inl .comp)) ![σ,τ]
abbrev sigma (A B : Expression V) : Expression V := .app (.inr .sigma) ![A,B]
abbrev pack (A B : Expression V) : Expression V := .app (.inr .pack) ![A,B]
abbrev unpack (A B : Expression V) : Expression V := .app (.inr .unpack) ![A,B]

abbrev formationSchema (out : Judgment (Fin 3)) : Rule signature where
  parameterCount := 3
  hypotheses := 2
  premise i := (Products.formationRule.premise i).inl extraSignature
  conclusion := out

abbrev formationRule := formationSchema (family (.var 0) (sigma (.var 1) (.var 2)))
abbrev packRule := formationSchema
  (substitution (extend (extend (.var 0) (.var 1)) (.var 2))
    (extend (.var 0) (sigma (.var 1) (.var 2))) (pack (.var 1) (.var 2)))
abbrev unpackRule := formationSchema
  (substitution (extend (.var 0) (sigma (.var 1) (.var 2)))
    (extend (extend (.var 0) (.var 1)) (.var 2)) (unpack (.var 1) (.var 2)))
abbrev betaRule := formationSchema
  (.eq (comp (unpack (.var 1) (.var 2)) (pack (.var 1) (.var 2)))
    (identity (extend (extend (.var 0) (.var 1)) (.var 2))))
abbrev etaRule := formationSchema
  (.eq (comp (pack (.var 1) (.var 2)) (unpack (.var 1) (.var 2)))
    (identity (extend (.var 0) (sigma (.var 1) (.var 2)))))

abbrev subTy (A σ : Expression V) : Expression V := .app (.inl (.inl .subTy)) ![A,σ]
abbrev lifted : Expression (Fin 5) :=
  (Products.lift (.var 1) (.var 2) (.var 4)).inl extraSignature

abbrev substitutionSchema (out : Judgment (Fin 5)) : Rule signature where
  parameterCount := 5
  hypotheses := 3
  premise i := (Products.piSubRule.premise i).inl extraSignature
  conclusion := out

abbrev sigmaSubRule := substitutionSchema
  (.eq (subTy (sigma (.var 2) (.var 3)) (.var 4))
    (sigma (subTy (.var 2) (.var 4)) (subTy (.var 3) lifted)))

abbrev term (Γ A t : Expression V) : Judgment V :=
  .pred (.inl (.inl .term)) ![Γ,A,t]
abbrev subTm (t σ : Expression V) : Expression V := .app (.inl (.inl .subTm)) ![t,σ]

abbrev eliminationSchema (out : Judgment (Fin 5)) : Rule signature where
  parameterCount := 5
  hypotheses := 4
  premise := ![family (.var 0) (.var 1), family (extend (.var 0) (.var 1)) (.var 2),
    family (extend (.var 0) (sigma (.var 1) (.var 2))) (.var 3),
    term (extend (extend (.var 0) (.var 1)) (.var 2))
      (subTy (.var 3) (pack (.var 1) (.var 2))) (.var 4)]
  conclusion := out

abbrev eliminationRule := eliminationSchema
  (term (extend (.var 0) (sigma (.var 1) (.var 2))) (.var 3)
    (subTm (.var 4) (unpack (.var 1) (.var 2))))

abbrev eliminationBetaRule := eliminationSchema
  (.eq (subTm (subTm (.var 4) (unpack (.var 1) (.var 2))) (pack (.var 1) (.var 2))) (.var 4))

end SquareKit.Cubical.Source.Sums
