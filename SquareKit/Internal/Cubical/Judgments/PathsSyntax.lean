import SquareKit.Internal.Cubical.Judgments.IntervalsSyntax

/-! Dependent Path rules require typed endpoints and both abstraction boundary
equations. They do not assert identity elimination. -/
namespace SquareKit.Cubical.Source.Paths
open GuardedTheory

inductive Operation where
  | path | lam | app
  deriving DecidableEq

abbrev extraSignature : Signature where
  Operation := Operation
  arity
    | .path => 4
    | _ => 5
  Predicate := Empty
  arguments := Empty.elim

abbrev signature := Intervals.signature.sum extraSignature
abbrev Expression (V : Type) := GuardedTheory.Term signature V
abbrev Judgment (V : Type) := GuardedTheory.Atom signature V

variable {V : Type}
abbrev context (Γ : Expression V) : Judgment V := .pred (.inl (.inl (.inl (.inl (.inl .context))))) ![Γ]
abbrev family (Γ A : Expression V) : Judgment V := .pred (.inl (.inl (.inl (.inl (.inl .family))))) ![Γ,A]
abbrev term (Γ A t : Expression V) : Judgment V := .pred (.inl (.inl (.inl (.inl (.inl .term))))) ![Γ,A,t]
abbrev extend (Γ A : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl .extend))))) ![Γ,A]
abbrev identity (Γ : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl .id))))) ![Γ]
abbrev pair (A σ t : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl .pair))))) ![A,σ,t]
abbrev subTy (A σ : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl .subTy))))) ![A,σ]
abbrev subTm (t σ : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl .subTm))))) ![t,σ]
abbrev interval (Γ : Expression V) : Expression V := .app (.inl (.inr .interval)) ![Γ]
abbrev endpoint (Γ : Expression V) (b : Bool) : Expression V :=
  .app (.inl (.inr (.dimension (n := 0) (if b then .one else .zero)))) (Matrix.vecCons Γ Fin.elim0)
abbrev endpointSub (Γ : Expression V) (b : Bool) := pair (interval Γ) (identity Γ) (endpoint Γ b)
abbrev path (Γ B a₀ a₁ : Expression V) : Expression V := .app (.inr .path) ![Γ,B,a₀,a₁]
abbrev lam (Γ B a₀ a₁ b : Expression V) : Expression V := .app (.inr .lam) ![Γ,B,a₀,a₁,b]
abbrev app (Γ B a₀ a₁ p : Expression V) : Expression V := .app (.inr .app) ![Γ,B,a₀,a₁,p]

abbrev formationSchema (out : Judgment (Fin 4)) : Rule signature where
  parameterCount := 4
  hypotheses := 4
  premise := ![context (.var 0),family (extend (.var 0) (interval (.var 0))) (.var 1),
    term (.var 0) (subTy (.var 1) (endpointSub (.var 0) false)) (.var 2),
    term (.var 0) (subTy (.var 1) (endpointSub (.var 0) true)) (.var 3)]
  conclusion := out
abbrev formationRule := formationSchema (family (.var 0) (path (.var 0) (.var 1) (.var 2) (.var 3)))

abbrev bodySchema (out : Judgment (Fin 5)) : Rule signature where
  parameterCount := 5
  hypotheses := 7
  premise i := if h : i.val < 4 then
    (formationRule.premise ⟨i.val,h⟩).subst (fun j => .var (j.castAdd 1))
    else if i.val = 4 then term (extend (.var 0) (interval (.var 0))) (.var 1) (.var 4)
    else if i.val = 5 then .eq (subTm (.var 4) (endpointSub (.var 0) false)) (.var 2)
    else .eq (subTm (.var 4) (endpointSub (.var 0) true)) (.var 3)
  conclusion := out
abbrev lamRule := bodySchema
  (term (.var 0) (path (.var 0) (.var 1) (.var 2) (.var 3))
    (lam (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)))
abbrev betaRule := bodySchema
  (.eq (app (.var 0) (.var 1) (.var 2) (.var 3)
    (lam (.var 0) (.var 1) (.var 2) (.var 3) (.var 4))) (.var 4))

abbrev functionSchema (out : Judgment (Fin 5)) : Rule signature where
  parameterCount := 5
  hypotheses := 5
  premise i := if h : i.val < 4 then
    (formationRule.premise ⟨i.val,h⟩).subst (fun j => .var (j.castAdd 1))
    else term (.var 0) (path (.var 0) (.var 1) (.var 2) (.var 3)) (.var 4)
  conclusion := out
abbrev appRule := functionSchema
  (term (extend (.var 0) (interval (.var 0))) (.var 1) (app (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)))
abbrev etaRule := functionSchema
  (.eq (lam (.var 0) (.var 1) (.var 2) (.var 3)
    (app (.var 0) (.var 1) (.var 2) (.var 3) (.var 4))) (.var 4))
abbrev endpointRule (b : Bool) := functionSchema
  (.eq (subTm (app (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)) (endpointSub (.var 0) b))
    (if b then .var 3 else .var 2))

abbrev substitution (Δ Γ σ : Expression V) : Judgment V :=
  .pred (.inl (.inl (.inl (.inl (.inl .substitution))))) ![Δ,Γ,σ]
abbrev weaken (Γ A : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl .weaken))))) ![Γ,A]
abbrev generic (Γ A : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl .generic))))) ![Γ,A]
abbrev comp (σ τ : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl .comp))))) ![σ,τ]
abbrev lift (Δ A σ : Expression V) :=
  pair A (comp σ (weaken Δ (subTy A σ))) (generic Δ (subTy A σ))

abbrev substitutionSchema (out : Judgment (Fin 6)) : Rule signature where
  parameterCount := 6
  hypotheses := 5
  premise i := if h : i.val < 4 then
    (formationRule.premise ⟨i.val,h⟩).subst (fun j => .var (![0,2,3,4] j))
    else substitution (.var 1) (.var 0) (.var 5)
  conclusion := out
abbrev pathSubRule := substitutionSchema
  (.eq (subTy (path (.var 0) (.var 2) (.var 3) (.var 4)) (.var 5))
    (path (.var 1) (subTy (.var 2) (lift (.var 1) (interval (.var 0)) (.var 5)))
      (subTm (.var 3) (.var 5)) (subTm (.var 4) (.var 5))))

abbrev bodySubstitutionSchema (out : Judgment (Fin 7)) : Rule signature where
  parameterCount := 7
  hypotheses := 8
  premise i := if h : i.val < 7 then
    (lamRule.premise ⟨i.val,h⟩).subst (fun j => .var (![0,2,3,4,5] j))
    else substitution (.var 1) (.var 0) (.var 6)
  conclusion := out
abbrev lamSubRule := bodySubstitutionSchema
  (.eq (subTm (lam (.var 0) (.var 2) (.var 3) (.var 4) (.var 5)) (.var 6))
    (lam (.var 1) (subTy (.var 2) (lift (.var 1) (interval (.var 0)) (.var 6)))
      (subTm (.var 3) (.var 6)) (subTm (.var 4) (.var 6))
      (subTm (.var 5) (lift (.var 1) (interval (.var 0)) (.var 6)))))

abbrev functionSubstitutionSchema (out : Judgment (Fin 7)) : Rule signature where
  parameterCount := 7
  hypotheses := 6
  premise i := if h : i.val < 5 then
    (appRule.premise ⟨i.val,h⟩).subst (fun j => .var (![0,2,3,4,5] j))
    else substitution (.var 1) (.var 0) (.var 6)
  conclusion := out
abbrev appSubRule := functionSubstitutionSchema
  (.eq (subTm (app (.var 0) (.var 2) (.var 3) (.var 4) (.var 5))
      (lift (.var 1) (interval (.var 0)) (.var 6)))
    (app (.var 1) (subTy (.var 2) (lift (.var 1) (interval (.var 0)) (.var 6)))
      (subTm (.var 3) (.var 6)) (subTm (.var 4) (.var 6)) (subTm (.var 5) (.var 6))))

end SquareKit.Cubical.Source.Paths
