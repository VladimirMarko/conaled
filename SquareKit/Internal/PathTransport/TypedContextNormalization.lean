import SquareKit.Internal.PathTransport.TypedTelescopeNormalization

/-! Every supported context has an extension presentation with the same code. -/
namespace SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

inductive PlainCtxDeriv : RawCtx → CtxCode.{u} → Type (u+1) where
  | empty : PlainCtxDeriv [] emptyCode
  | ext : PlainCtxDeriv Γ γ → TyDeriv Γ γ B b → PlainCtxDeriv (B :: Γ) (extendCode γ b)

def PlainCtxDeriv.derivation (hΓ : PlainCtxDeriv.{u} Γ γ) : CtxDeriv Γ γ :=
  match hΓ with
  | .empty => .empty
  | .ext hΓ hB => .ext hΓ.derivation hB

theorem telTotal_cons (a : TyCode.{u} γ) (T : TelCode (extendCode γ a) n) :
    telTotal (telCons a T) = telTotal T := rfl

def PlainTelDeriv.extendContext (hT : PlainTelDeriv.{u} Γ γ n Δ T)
    (hΓ : PlainCtxDeriv Γ γ) : PlainCtxDeriv (Δ ++ Γ) (telTotal T) :=
  match hT with
  | .nil _ => hΓ
  | .cons hB hT => by
      simpa only [telTotal_cons, List.append_assoc, List.singleton_append] using hT.extendContext (.ext hΓ hB)
termination_by sizeOf hT

def pathFamilyDerivation (hΓ : CtxDeriv.{u} Γ γ) (hB : TyDeriv Γ γ B b)
    (hx : TmDeriv Γ γ B b x ξ) :
    TyDeriv (B :: Γ) (extendCode γ b)
      (.identity (B.rename Nat.succ) (x.rename Nat.succ) (.var 0))
      (identityCode (subTyCode b (weakenCode γ b))
        (subTmCode ξ (weakenCode γ b)) (varCode γ b)) := by
  apply TyDeriv.identity
  · simpa only [Expr.sub_var_rename] using TyDeriv.sub hB (.weaken hΓ hB)
  · simpa only [Expr.sub_var_rename] using TmDeriv.sub hx (.weaken hΓ hB)
  · exact .var hΓ hB

def CtxDeriv.normalize (hΓ : CtxDeriv.{u} Γ γ) : PlainCtxDeriv Γ γ :=
  match hΓ with
  | .empty => .empty
  | .ext hΓ hB => .ext hΓ.normalize hB
  | .path hΓ hB hx => .ext (.ext hΓ.normalize hB) (pathFamilyDerivation hΓ hB hx)
  | .telescope hΓ hT => hT.normalize.extendContext hΓ.normalize
  | .branch hΓ hB hx hT =>
      (hT.normalize.reindex hΓ (.root hΓ hB hx)).extendContext hΓ.normalize
termination_by sizeOf hΓ

end SquareKit.Internal.PathTransport.Typed
