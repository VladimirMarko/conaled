import SquareKit.Internal.DependentJudgments.Comprehension
import SquareKit.GuardedTheory.Extension

/-! Source Π rules with explicit comprehension binders. Generic application is
in Γ.A; application to a particular argument is its object-context substitution. -/
namespace SquareKit.Cubical.Source.Products
open GuardedTheory

inductive Operation where
  | pi | lam | app
  deriving DecidableEq

abbrev extraSignature : Signature where
  Operation := Operation
  arity
    | .pi => 2
    | _ => 3
  Predicate := Empty
  arguments := Empty.elim

abbrev signature := Internal.DependentJudgments.signature.sum extraSignature
abbrev Expression (V : Type) := GuardedTheory.Term signature V
abbrev Judgment (V : Type) := GuardedTheory.Atom signature V

variable {V : Type}
abbrev context (Γ : Expression V) : Judgment V := .pred (.inl .context) ![Γ]
abbrev family (Γ A : Expression V) : Judgment V := .pred (.inl .family) ![Γ,A]
abbrev term (Γ A t : Expression V) : Judgment V := .pred (.inl .term) ![Γ,A,t]
abbrev substitution (Δ Γ σ : Expression V) : Judgment V := .pred (.inl .substitution) ![Δ,Γ,σ]
abbrev extend (Γ A : Expression V) : Expression V := .app (.inl .extend) ![Γ,A]
abbrev subTy (A σ : Expression V) : Expression V := .app (.inl .subTy) ![A,σ]
abbrev subTm (t σ : Expression V) : Expression V := .app (.inl .subTm) ![t,σ]
abbrev weaken (Γ A : Expression V) : Expression V := .app (.inl .weaken) ![Γ,A]
abbrev generic (Γ A : Expression V) : Expression V := .app (.inl .generic) ![Γ,A]
abbrev comp (σ τ : Expression V) : Expression V := .app (.inl .comp) ![σ,τ]
abbrev pair (A σ t : Expression V) : Expression V := .app (.inl .pair) ![A,σ,t]
abbrev lift (Δ A σ : Expression V) : Expression V :=
  pair A (comp σ (weaken Δ (subTy A σ))) (generic Δ (subTy A σ))
abbrev pi (A B : Expression V) : Expression V := .app (.inr .pi) ![A,B]
abbrev lam (A B b : Expression V) : Expression V := .app (.inr .lam) ![A,B,b]
abbrev app (A B p : Expression V) : Expression V := .app (.inr .app) ![A,B,p]

abbrev formationSchema (out : Judgment (Fin 3)) : Rule signature where
  parameterCount := 3
  hypotheses := 2
  premise := ![family (.var 0) (.var 1), family (extend (.var 0) (.var 1)) (.var 2)]
  conclusion := out
abbrev formationRule := formationSchema (family (.var 0) (pi (.var 1) (.var 2)))

abbrev bodySchema (out : Judgment (Fin 4)) : Rule signature where
  parameterCount := 4
  hypotheses := 2
  premise := ![family (.var 0) (.var 1), term (extend (.var 0) (.var 1)) (.var 2) (.var 3)]
  conclusion := out
abbrev lamRule := bodySchema (term (.var 0) (pi (.var 1) (.var 2)) (lam (.var 1) (.var 2) (.var 3)))
abbrev betaRule := bodySchema
  (.eq (app (.var 1) (.var 2) (lam (.var 1) (.var 2) (.var 3))) (.var 3))

abbrev functionSchema (out : Judgment (Fin 4)) : Rule signature where
  parameterCount := 4
  hypotheses := 3
  premise := ![family (.var 0) (.var 1), family (extend (.var 0) (.var 1)) (.var 2),
    term (.var 0) (pi (.var 1) (.var 2)) (.var 3)]
  conclusion := out
abbrev appRule := functionSchema (term (extend (.var 0) (.var 1)) (.var 2) (app (.var 1) (.var 2) (.var 3)))
abbrev etaRule := functionSchema
  (.eq (lam (.var 1) (.var 2) (app (.var 1) (.var 2) (.var 3))) (.var 3))

abbrev substitutionSchema (out : Judgment (Fin 5)) : Rule signature where
  parameterCount := 5
  hypotheses := 3
  premise := ![family (.var 0) (.var 2), family (extend (.var 0) (.var 2)) (.var 3),
    substitution (.var 1) (.var 0) (.var 4)]
  conclusion := out
abbrev piSubRule := substitutionSchema
  (.eq (subTy (pi (.var 2) (.var 3)) (.var 4))
    (pi (subTy (.var 2) (.var 4)) (subTy (.var 3) (lift (.var 1) (.var 2) (.var 4)))))

abbrev termSubstitutionSchema (Γ A : Expression (Fin 6)) (out : Judgment (Fin 6)) : Rule signature where
  parameterCount := 6
  hypotheses := 4
  premise := ![family (.var 0) (.var 2), family (extend (.var 0) (.var 2)) (.var 3),
    substitution (.var 1) (.var 0) (.var 5), term Γ A (.var 4)]
  conclusion := out
abbrev lamSubSchema := termSubstitutionSchema (extend (.var 0) (.var 2)) (.var 3)
abbrev appSubSchema := termSubstitutionSchema (.var 0) (pi (.var 2) (.var 3))
abbrev lamSubRule := lamSubSchema
  (.eq (subTm (lam (.var 2) (.var 3) (.var 4)) (.var 5))
    (lam (subTy (.var 2) (.var 5)) (subTy (.var 3) (lift (.var 1) (.var 2) (.var 5)))
      (subTm (.var 4) (lift (.var 1) (.var 2) (.var 5)))))
abbrev appSubRule := appSubSchema
  (.eq (subTm (app (.var 2) (.var 3) (.var 4)) (lift (.var 1) (.var 2) (.var 5)))
    (app (subTy (.var 2) (.var 5)) (subTy (.var 3) (lift (.var 1) (.var 2) (.var 5)))
      (subTm (.var 4) (.var 5))))

end SquareKit.Cubical.Source.Products
