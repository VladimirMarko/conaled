import AndPositivityStages

/-! Experimental exact checker composition for #135. Phase certificates are
arguments to symbolic equations, keeping concrete environments out of reduction. -/
namespace AcceptanceComposition
open ConLeche

theorem bind_ok {α β ε : Type} (a : Except ε α) (k : α → Except ε β)
    (x : α) (y : β) (ha : a = .ok x) (hk : k x = .ok y) :
    (a >>= k) = .ok y := by rw [ha]; exact hk

theorem fold_three {α β ε : Type} (f : β → α → Except ε β) (a b c : α) (s0 s1 s2 s3 : β)
    (ha : f s0 a = .ok s1) (hb : f s1 b = .ok s2) (hc : f s2 c = .ok s3) :
    [a,b,c].foldlM f s0 = .ok s3 := by
  simp only [List.foldlM_cons, ha, hb, hc, bind, Except.bind, List.foldlM_nil]
  rfl

theorem pair_ok {α β ε : Type} (p : α × β) :
    (Except.ok p : Except ε (α × β)) = .ok (p.1,p.2) := by cases p; rfl

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
theorem block_positivity (ops : CheckerOps (Except CheckError)) (env : Env)
    (find : Name → Option ConstantInfo) (p : BlockParts) (cv : List ConstantVal)
    (ctors : List (List (ConstantVal × Nat))) (ctx : NestCtx) (holes : List Expr)
    (outs : List (List (List NestFieldKind × Expr))) (st : NestState)
    (hc : blockNestCtx (m := Except CheckError) p.toBlockShape cv find = .ok (ctx,holes))
    (hu : nestUniform (m := Except CheckError) ctx ctors = .ok ())
    (hr : nestRoot ops env ctx holes ctors {} = .ok (outs,st))
    (hs : checkAbsCtorSortsAll ops env ctx ctors outs = .ok ()) :
    checkBlockPositivity ops env find p cv ctors =
      .ok (outs.map (·.map (·.1)),outs.map (·.map (·.2)),st) := by
  simp only [checkBlockPositivity,hc,bind,Except.bind,hu,hr,hs,pure,Except.pure]

theorem block_pass (ops : CheckerOps (Except CheckError)) (env env1 : Env)
    (p0 : BlockParts) (isRec : Bool) (cvs : List ConstantVal) (shape : BlockShape)
    (ctors : List (List (ConstantVal × Nat))) (sorts : List (List (List Level)))
    (ctx : NestCtx) (holes : List Expr) (rd : ClassRead) (cls : List TargetMajor)
    (kinds : List (List (List NestFieldKind))) (nfs : List (List Expr))
    (pos st : NestState)
    (hi : checkBlockInds ops env p0 isRec = .ok (env1,cvs,shape))
    (hc : checkBlockCtors ops env1 env1 (p0.complete shape).toBlockShape
      ((p0.complete shape).members.zip cvs) = .ok (ctors,sorts))
    (hx : blockNestCtx (m := Except CheckError) (p0.complete shape).toBlockShape cvs env1.find? = .ok (ctx,holes))
    (hr : checkBlockClasses ops (mkFEnv env1) (p0.complete shape).toBlockShape ctx.params ctors = .ok (rd,cls))
    (hp : checkBlockPositivity ops env1 env1.find? (p0.complete shape) cvs ctors = .ok (kinds,nfs,pos))
    (hs : nestSeeds ops env1 ctx (classSeeds ctx holes cls) pos = .ok st) :
    checkBlockPass ops env p0 isRec = .ok
      ⟨env1,cvs,p0.complete shape,ctors,sorts,kinds,nfs,ctx.params,rd,cls,st.ctorNfs⟩ := by
  simp only [checkBlockPass,hi,bind,Except.bind,hc,hx,hr,hp,hs,pure,Except.pure]
end AcceptanceComposition
#audit_graph_module
