import AndPositivityStages

/-! Experimental exact checker composition for #135. Phase certificates are
arguments to symbolic equations, keeping concrete environments out of reduction. -/
namespace AcceptanceComposition
open ConLeche

theorem bind_ok {α β ε : Type} (a : Except ε α) (k : α → Except ε β)
    (x : α) (y : β) (ha : a = .ok x) (hk : k x = .ok y) :
    (a >>= k) = .ok y := by rw [ha]; exact hk

theorem ctors_one (ctx : NestCtx) (ops : CheckerOps (Except CheckError)) (env : Env)
    (rec : Expr → List NestHole → Nat → Nat → Expr → NestState →
      Except CheckError (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr)
    (names : List Name) (holes : List Expr) (cv : ConstantVal) (nF : Nat)
    (st st' : NestState) (crest ty : Expr) (u : Level)
    (ks : List NestFieldKind) (nds : List Expr) (cur : Expr)
    (hn : Name.nodup cv.levelParams = true)
    (hc : nestCrest names us ds holes (cv.type.instantiateLevelParams cv.levelParams us) = some crest)
    (ht : ops.inferType env hi crest = .ok ty)
    (hs : ops.ensureSort env hi ty = .ok u)
    (hf : ∀ err, nestFields (rec crest) prog hi err nF 0 crest st = .ok (ks,nds,cur,st'))
    (hg : ((List.range nF).any fun i => ks.getD i .ordinary != .ordinary &&
      structUsedLater (closeTelescope nds hi cur) 0 i) = false)
    (hr : (nestResHead cur && cur.getAppArgs.all
      (fun x => !x.nestOcc ctx.names ctx.nP hi)) = true) :
    nestCtors ctx ops env rec prog hi us ds names holes [(cv,nF)] st =
      .ok ([(ks,closeTelescope nds hi cur)],
        { st' with ctorNfs := st'.ctorNfs.push (nestCtorNf ctx prog hi us ds cv nds cur) }) := by
  simp only [nestCtors, hn, Bool.false_eq_true, ↓reduceIte,
    hc, unwrapOr, bind, Except.bind, pure, Except.pure, ht, hs, hf, hg, hr]

theorem root_one (ops : CheckerOps (Except CheckError)) (env : Env) (ctx : NestCtx)
    (holes : List Expr) (cs : List (ConstantVal × Nat)) (st st' : NestState)
    (o : List (List NestFieldKind × Expr))
    (hc : nestCtors ctx ops env (fun crest => nestPos ops env ctx (whnfWalkFuel crest)) []
      (ctx.hiAt 0) (ctx.lps.map .param) ctx.params ctx.names holes cs st = .ok (o,st')) :
    nestRoot ops env ctx holes [cs] st = .ok ([o],st') := by
  simp only [nestRoot,hc]
  rfl
end AcceptanceComposition
#audit_graph_module
