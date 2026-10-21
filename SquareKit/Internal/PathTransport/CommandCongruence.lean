import SquareKit.Internal.PathTransport.Authoring
import SquareKit.Internal.PathTransport.StructuralCongruence
namespace SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.PathTransport

theorem genericJRaw_sub (n : Nat) (A x C d y p : Expr) (ρ : RawSub) (args : Fin n → Expr) :
    (genericJRaw n A x C d).sub (argsSub args (consSub p (consSub y ρ))) =
      .pathInduction n (A.sub ρ) (x.sub ρ) (C.sub (Expr.liftSubN (n+2) ρ))
        (d.sub (Expr.liftSubN n ρ)) y p args := by
  have hs : argsSub args (consSub p (consSub y ρ)) ∘ (fun i => i + (n+2)) = ρ := by
    funext i
    simp only [Function.comp_apply, argsSub]
    split
    · omega
    · have hi : i + (n+2) - n = i + 2 := by omega
      rw [hi]
      rfl
  simp only [genericJRaw, Expr.sub, Expr.sub_rename, ← Expr.liftSubN_precomp, hs]
  congr 1
  · simp [argsSub, consSub, show ¬ n + 1 < n by omega]
  · simp [argsSub, consSub]
  · funext i
    simp [argsSub, i.isLt]
namespace Authoring

/-- Apply the same open command at converted endpoint and tail substitutions.
The generic source judgment supplies the operation; the helper cancels its
weakenings and aligns result annotations. -/
def PathCommand.argumentsCongr (cmd : @PathCommand Γ γ A x a ξ n Δ T)
    {args args' : Fin n → Expr} {ρ ρ' : RawSub}
    (e : SubEqDeriv Ω ω (Δ ++ pathCtx Γ A x) (telTotal T)
      (argsSub args (consSub p (consSub y ρ))) s
      (argsSub args' (consSub p' (consSub y' ρ'))) s')
    (hraw : cmd.motive.raw.sub (argsSub args (consSub p (consSub y ρ))) = B)
    (hs : subTyCode cmd.motive.code s = b) (ht : subTyCode cmd.motive.code s' = b) :
    TmEqDeriv Ω ω B b
      (.pathInduction n (A.sub ρ) (x.sub ρ) (cmd.motive.raw.sub (Expr.liftSubN (n+2) ρ))
        (cmd.motive.branch.sub (Expr.liftSubN n ρ)) y p args)
      (castCode hs (subTmCode (jCode a ξ T cmd.motive.code cmd.motive.branchCode) s))
      (.pathInduction n (A.sub ρ') (x.sub ρ') (cmd.motive.raw.sub (Expr.liftSubN (n+2) ρ'))
        (cmd.motive.branch.sub (Expr.liftSubN n ρ')) y' p' args')
      (castCode ht (subTmCode (jCode a ξ T cmd.motive.code cmd.motive.branchCode) s')) := by
  have j := TmDeriv.genericJ cmd.context cmd.type cmd.point cmd.telescope
    cmd.motive.typing cmd.motive.branchTyping
  simpa only [genericJRaw_sub] using j.substitutionCongrAt e hraw hs ht

end Authoring
end SquareKit.Internal.PathTransport.Typed
