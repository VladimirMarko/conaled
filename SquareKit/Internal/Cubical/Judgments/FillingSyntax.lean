import SquareKit.Internal.Cubical.Judgments.PathsSyntax

/-! Homogeneous composition and generalized transport have explicit selected
provider guards. Partial terms live in the actual restricted context. -/
namespace SquareKit.Cubical.Source.Fillings
open GuardedTheory

inductive Operation where
  | faceTop | faceBot | faceJoin | faceEndpoint (b : Bool)
  | subFace | restriction | inclusion | restrictedSub | subProvider
  | hcomp | transp
  deriving DecidableEq

inductive Predicate where
  | face | provider
  deriving DecidableEq

abbrev extraSignature : Signature where
  Operation := Operation
  arity
    | .faceTop | .faceBot => 1
    | .faceEndpoint _ | .restriction | .inclusion => 2
    | .faceJoin => 3
    | .subFace | .restrictedSub | .subProvider => 4
    | .hcomp => 6
    | .transp => 5
  Predicate := Predicate
  arguments | .face => 2 | .provider => 3

abbrev signature := Paths.signature.sum extraSignature
abbrev Expression (V : Type) := GuardedTheory.Term signature V
abbrev Judgment (V : Type) := GuardedTheory.Atom signature V
variable {V : Type}

abbrev context (Γ : Expression V) : Judgment V := .pred (.inl (.inl (.inl (.inl (.inl (.inl .context)))))) ![Γ]
abbrev family (Γ A : Expression V) : Judgment V := .pred (.inl (.inl (.inl (.inl (.inl (.inl .family)))))) ![Γ,A]
abbrev term (Γ A t : Expression V) : Judgment V := .pred (.inl (.inl (.inl (.inl (.inl (.inl .term)))))) ![Γ,A,t]
abbrev substitution (Δ Γ σ : Expression V) : Judgment V :=
  .pred (.inl (.inl (.inl (.inl (.inl (.inl .substitution)))))) ![Δ,Γ,σ]
abbrev extend (Γ A : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl (.inl .extend)))))) ![Γ,A]
abbrev identity (Γ : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl (.inl .id)))))) ![Γ]
abbrev pair (A σ t : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl (.inl .pair)))))) ![A,σ,t]
abbrev subTy (A σ : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl (.inl .subTy)))))) ![A,σ]
abbrev subTm (t σ : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl (.inl .subTm)))))) ![t,σ]
abbrev weaken (Γ A : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl (.inl .weaken)))))) ![Γ,A]
abbrev generic (Γ A : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl (.inl .generic)))))) ![Γ,A]
abbrev comp (σ τ : Expression V) : Expression V := .app (.inl (.inl (.inl (.inl (.inl (.inl .comp)))))) ![σ,τ]
abbrev interval (Γ : Expression V) : Expression V := .app (.inl (.inl (.inr .interval))) ![Γ]
abbrev endpoint (Γ : Expression V) (b : Bool) : Expression V :=
  .app (.inl (.inl (.inr (.dimension (n := 0) (if b then .one else .zero))))) (Matrix.vecCons Γ Fin.elim0)
abbrev intervalContext (Γ : Expression V) := extend Γ (interval Γ)
abbrev endpointSub (Γ : Expression V) (b : Bool) := pair (interval Γ) (identity Γ) (endpoint Γ b)
abbrev projection (Γ : Expression V) := weaken Γ (interval Γ)
abbrev lift (Δ Γ σ : Expression V) :=
  pair (interval Γ) (comp σ (projection Δ)) (generic Δ (interval Δ))

abbrev face (Γ φ : Expression V) : Judgment V := .pred (.inr .face) ![Γ,φ]
abbrev provider (Γ A F : Expression V) : Judgment V := .pred (.inr .provider) ![Γ,A,F]
abbrev faceTop (Γ : Expression V) : Expression V := .app (.inr .faceTop) ![Γ]
abbrev faceBot (Γ : Expression V) : Expression V := .app (.inr .faceBot) ![Γ]
abbrev faceJoin (Γ φ ψ : Expression V) : Expression V := .app (.inr .faceJoin) ![Γ,φ,ψ]
abbrev faceEndpoint (Γ r : Expression V) (b : Bool) : Expression V := .app (.inr (.faceEndpoint b)) ![Γ,r]
abbrev subFace (Δ Γ φ σ : Expression V) : Expression V := .app (.inr .subFace) ![Δ,Γ,φ,σ]
abbrev restriction (Γ φ : Expression V) : Expression V := .app (.inr .restriction) ![Γ,φ]
abbrev inclusion (Γ φ : Expression V) : Expression V := .app (.inr .inclusion) ![Γ,φ]
abbrev restrictedSub (Δ Γ φ σ : Expression V) : Expression V := .app (.inr .restrictedSub) ![Δ,Γ,φ,σ]
abbrev subProvider (Δ Γ F σ : Expression V) : Expression V := .app (.inr .subProvider) ![Δ,Γ,F,σ]
abbrev hcomp (Γ A F φ u a : Expression V) : Expression V := .app (.inr .hcomp) ![Γ,A,F,φ,u,a]
abbrev transp (Γ B F φ a : Expression V) : Expression V := .app (.inr .transp) ![Γ,B,F,φ,a]
abbrev intervalFace (Γ φ : Expression V) := subFace (intervalContext Γ) Γ φ (projection Γ)
abbrev restrictedTerm (Γ A φ t : Expression V) :=
  term (restriction Γ φ) (subTy A (inclusion Γ φ)) t
abbrev tubeEndpoint (Γ φ u : Expression V) (b : Bool) :=
  subTm u (restrictedSub Γ (intervalContext Γ) (intervalFace Γ φ) (endpointSub Γ b))

abbrev hcompSchema (out : Judgment (Fin 6)) : Rule signature where
  parameterCount := 6
  hypotheses := 5
  premise := ![provider (.var 0) (.var 1) (.var 2), face (.var 0) (.var 3),
    restrictedTerm (intervalContext (.var 0)) (subTy (.var 1) (projection (.var 0)))
      (intervalFace (.var 0) (.var 3)) (.var 4),
    term (.var 0) (.var 1) (.var 5),
    .eq (tubeEndpoint (.var 0) (.var 3) (.var 4) false)
      (subTm (.var 5) (inclusion (.var 0) (.var 3)))]
  conclusion := out
abbrev hcompRule := hcompSchema
  (term (.var 0) (.var 1) (hcomp (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)))
abbrev hcompBoundaryRule := hcompSchema
  (.eq (subTm (hcomp (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5))
    (inclusion (.var 0) (.var 3))) (tubeEndpoint (.var 0) (.var 3) (.var 4) true))

abbrev transpSchema (out : Judgment (Fin 5)) : Rule signature where
  parameterCount := 5
  hypotheses := 4
  premise := ![provider (intervalContext (.var 0)) (.var 1) (.var 2), face (.var 0) (.var 3),
    term (.var 0) (subTy (.var 1) (endpointSub (.var 0) false)) (.var 4),
    .eq (subTy (.var 1) (inclusion (intervalContext (.var 0)) (intervalFace (.var 0) (.var 3))))
      (subTy (subTy (subTy (.var 1) (endpointSub (.var 0) false)) (projection (.var 0)))
        (inclusion (intervalContext (.var 0)) (intervalFace (.var 0) (.var 3))))]
  conclusion := out
abbrev transpRule := transpSchema
  (term (.var 0) (subTy (.var 1) (endpointSub (.var 0) true))
    (transp (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)))
abbrev transpBoundaryRule := transpSchema
  (.eq (subTm (transp (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)) (inclusion (.var 0) (.var 3)))
    (subTm (.var 4) (inclusion (.var 0) (.var 3))))

end SquareKit.Cubical.Source.Fillings
