import CachedTransitionComposition

/-! Experimental cached positivity composition for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedPositivityComposition
open ConLeche ConLeche.Cached CachedTransitionComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

measured_theorem ctors_one : ∀ (ctx : NestCtx) (ops : CheckerOps CheckCM) (env : Env)
    (rec : Expr → List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr)
    (names : List Name) (holes : List Expr) (cv : ConstantVal) (nF : Nat)
    (st st' : NestState) (crest ty : Expr) (u : Level)
    (ks : List NestFieldKind) (nds : List Expr) (cur : Expr) (s s1 s2 s3 : CState),
    Name.nodup cv.levelParams = true →
    nestCrest names us ds holes (cv.type.instantiateLevelParams cv.levelParams us) = some crest →
    ops.inferType env hi crest s = .ok (ty,s1) →
    ops.ensureSort env hi ty s1 = .ok (u,s2) →
    (∀ err, nestFields (rec crest) prog hi err nF 0 crest st s2 = .ok ((ks,nds,cur,st'),s3)) →
    ((List.range nF).any fun i => ks.getD i .ordinary != .ordinary &&
      structUsedLater (closeTelescope nds hi cur) 0 i) = false →
    (nestResHead cur && cur.getAppArgs.all (fun x => !x.nestOcc ctx.names ctx.nP hi)) = true →
    nestCtors ctx ops env rec prog hi us ds names holes [(cv,nF)] st s =
      .ok (([(ks,closeTelescope nds hi cur)],
        { st' with ctorNfs := st'.ctorNfs.push (nestCtorNf ctx prog hi us ds cv nds cur) }),s3) := by
  intro ctx ops env rec prog hi us ds names holes cv nF st st' crest ty u ks nds cur
    s s1 s2 s3 hn hc ht hs hf hg hr
  unfold nestCtors
  simp only [hn, ↓reduceIte, hc, unwrapOr]
  refine bind_ok _ _ s s s3 crest _ rfl ?_
  refine bind_ok _ _ s s1 s3 ty _ ht ?_
  refine bind_ok _ _ s1 s2 s3 u _ hs ?_
  refine bind_ok _ _ s2 s3 s3 (ks,nds,cur,st') _ (hf _) ?_
  simp only [hg, hr, Bool.false_eq_true, ↓reduceIte]
  rfl

measured_theorem root_one : ∀ (ops : CheckerOps CheckCM) (env : Env) (ctx : NestCtx)
    (holes : List Expr) (cs : List (ConstantVal × Nat)) (st st' : NestState)
    (o : List (List NestFieldKind × Expr)) (s s1 : CState),
    nestCtors ctx ops env (fun crest => nestPos ops env ctx (whnfWalkFuel crest)) []
      (ctx.hiAt 0) (ctx.lps.map .param) ctx.params ctx.names holes cs st s = .ok ((o,st'),s1) →
    nestRoot ops env ctx holes [cs] st s = .ok (([o],st'),s1) := by
  intro ops env ctx holes cs st st' o s s1 hc
  unfold nestRoot
  refine bind_ok _ _ s s1 s1 (o,st') _ hc ?_
  rfl
measured_theorem ordinary : ∀ (ops : CheckerOps CheckCM) (env : Env) (ctx : NestCtx)
    (f dep kb : Nat) (prog : List NestHole) (e : Expr) (st : NestState) (s s1 : CState),
    e.nestOcc ctx.names ctx.nP (ctx.hiAt prog.length) = false →
    ops.whnf env dep e s = .ok (e,s1) →
    nestPos ops env ctx (f + 1) prog dep kb e st s = .ok ((.ordinary,e,st),s1) := by
  intro ops env ctx f dep kb prog e st s s1 hn hw
  rw [nestPos]
  refine bind_ok _ _ s s1 s1 e _ hw ?_
  simp only [hn, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
  rfl

measured_theorem fields_step : ∀
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckCM (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (base j nF : Nat) (err : CheckError) (a b nb cur : Expr)
    (k : NestFieldKind) (ks : List NestFieldKind) (nds : List Expr)
    (st st1 st2 : NestState) (s s1 s2 : CState),
    rec prog (base + j) 0 a st s = .ok ((k,nb,st1),s1) →
    nestFields rec prog base err nF (j + 1) (b.instantiate1 (.fvar (base + j) a)) st1 s1 =
      .ok ((ks,nds,cur,st2),s2) →
    nestFields rec prog base err (nF + 1) j (.forallE a b) st s =
      .ok ((k :: ks, nb :: nds,cur,st2),s2) := by
  intro rec prog base j nF err a b nb cur k ks nds st st1 st2 s s1 s2 hr ht
  unfold nestFields
  refine bind_ok _ _ s s1 s2 (k,nb,st1) _ hr ?_
  refine bind_ok _ _ s1 s2 s2 (ks,nds,cur,st2) _ ht ?_
  rfl

measured_theorem abs_one : ∀ (ops : CheckerOps CheckCM) (env : Env) (ctx : NestCtx)
    (cv : ConstantVal) (nF : Nat) (ks : List NestFieldKind) (crest : Expr)
    (fvs : List Expr) (res : Expr) (us : List Level) (s s1 : CState),
    crest.allLevelParamsDefined ctx.lps = true →
    openPisAtFvars nF crest (ctx.hiAt 0) = some (fvs,res) →
    checkStructFieldSortsI ops env (Level.isEquiv ctx.sort .zero == some true) false
      ctx.sort (ctx.hiAt 0) fvs [] nF s = .ok (us,s1) →
    checkAbsCtorSortsAll ops env ctx [[(cv,nF)]] [[(ks,crest)]] s = .ok ((),s1) := by
  intro ops env ctx cv nF ks crest fvs res us s s1 hd ho hf
  have h : checkAbsCtorSorts ops env ctx [(cv,nF)] [(ks,crest)] s = .ok ((),s1) := by
    unfold checkAbsCtorSorts
    simp only [hd, ↓reduceIte, ho, unwrapOr]
    refine bind_ok _ _ s s s1 (fvs,res) _ rfl ?_
    refine bind_ok _ _ s s1 s1 us _ hf ?_
    rfl
  unfold checkAbsCtorSortsAll
  refine bind_ok _ _ s s1 s1 () _ h ?_
  rfl

measured_theorem block_positivity : ∀ (ops : CheckerOps CheckCM) (env : Env)
    (find : Name → Option ConstantInfo) (p : BlockParts) (cv : List ConstantVal)
    (ctors : List (List (ConstantVal × Nat))) (ctx : NestCtx) (holes : List Expr)
    (outs : List (List (List NestFieldKind × Expr))) (st : NestState) (s s1 s2 s3 s4 : CState),
    blockNestCtx (m := CheckCM) p.toBlockShape cv find s = .ok ((ctx,holes),s1) →
    nestUniform (m := CheckCM) ctx ctors s1 = .ok ((),s2) →
    nestRoot ops env ctx holes ctors {} s2 = .ok ((outs,st),s3) →
    checkAbsCtorSortsAll ops env ctx ctors outs s3 = .ok ((),s4) →
    checkBlockPositivity ops env find p cv ctors s =
      .ok ((outs.map (·.map (·.1)),outs.map (·.map (·.2)),st),s4) := by
  intro ops env find p cv ctors ctx holes outs st s s1 s2 s3 s4 hc hu hr hs
  unfold checkBlockPositivity
  refine bind_ok _ _ s s1 s4 (ctx,holes) _ hc ?_
  refine bind_ok _ _ s1 s2 s4 () _ hu ?_
  refine bind_ok _ _ s2 s3 s4 (outs,st) _ hr ?_
  refine bind_ok _ _ s3 s4 s4 () _ hs ?_
  rfl

end CachedPositivityComposition
#audit_graph_module
