import SquareKit.Internal.PathTransport.Binding
import SquareKit.Internal.PathTransport.TypedContexts

/-! Expand finite telescopes into their typed dependent binders. -/
namespace SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

inductive PlainTelDeriv : (Γ : RawCtx) → (γ : CtxCode.{u}) →
    (n : Nat) → RawCtx → TelCode γ n → Type (u+1) where
  | nil : CtxDeriv Γ γ → PlainTelDeriv Γ γ 0 [] (telNil γ)
  | cons : TyDeriv Γ γ A a → PlainTelDeriv (A :: Γ) (extendCode γ a) n Δ T →
      PlainTelDeriv Γ γ (n+1) (Δ ++ [A]) (telCons a T)

private theorem liftSubN_succ_right (n : Nat) (σ : RawSub) :
    Expr.liftSubN (n+1) σ = Expr.liftSubN n (Expr.liftSub σ) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Expr.liftSub ih

private theorem subTail_append_singleton (σ : RawSub) (Δ : RawCtx) (B : Expr) :
    subTail σ (Δ ++ [B]) = subTail (Expr.liftSub σ) Δ ++ [B.sub σ] := by
  induction Δ with
  | nil => rfl
  | cons C Δ ih =>
      simp only [List.cons_append, subTail, List.length_append, List.length_singleton,
        liftSubN_succ_right, ih]

def PlainTelDeriv.reindex (hT : PlainTelDeriv.{u} Γ γ n Δ T)
    (hΩ : CtxDeriv Ω ω) (hs : SubDeriv Ω ω Γ γ σ s) :
    PlainTelDeriv Ω ω n (subTail σ Δ) (telPullback T s) :=
  match hT with
  | .nil _ => .nil hΩ
  | .cons hB hT => by
      rw [subTail_append_singleton]
      exact .cons (.sub hB hs)
        (hT.reindex (.ext hΩ (.sub hB hs)) (Authoring.liftSubstitution hΩ hB hs))
termination_by sizeOf hT

def pathSubDerivation (hΓ : CtxDeriv.{u} Γ γ) (hB : TyDeriv Γ γ B b)
    (hx : TmDeriv Γ γ B b x ξ) (hs : SubDeriv Ω ω Γ γ σ s) :
    SubDeriv (pathCtx Ω (B.sub σ) (x.sub σ)) (pathCode (subTyCode b s) (subTmCode ξ s))
      (pathCtx Γ B x) (pathCode b ξ) (Expr.liftSubN 2 σ) (pathSubCode b ξ s) :=
  .pathTailMap hΓ hB hx (.nil (.path hΓ hB hx)) hs

def TelDeriv.normalize (hT : TelDeriv.{u} Γ γ n Δ T) : PlainTelDeriv Γ γ n Δ T :=
  match hT with
  | .nil hΓ => .nil hΓ
  | .cons hB hT => .cons hB hT.normalize
  | .pullback hT hs => hT.normalize.reindex hs.sourceContext hs
  | .pathReindex hΓ hB hx hT hs =>
      hT.normalize.reindex (.path hs.sourceContext (.sub hB hs) (.sub hx hs))
        (pathSubDerivation hΓ hB hx hs)
termination_by sizeOf hT

end SquareKit.Internal.PathTransport.Typed
