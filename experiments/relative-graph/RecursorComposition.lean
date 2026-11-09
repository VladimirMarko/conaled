import AcceptanceComposition
import ConLeche.Verify.CheckerSplit
/-! Experimental #135 checkpoint. Symbolic success assemblers for the existing recursor generator and installer; every operational premise remains explicit.
See [measurement and scope report](../../docs/research/relative-and-root-checkpoint.md). -/
namespace RecursorComposition
open ConLeche
variable {μ : CheckMode} {F : Nat} {env : Env}
theorem classConstOk_of_facts {cv : ConstantVal} {stype : Expr} {u : Level}
    (hfind : env.find? cv.name = none)
    (hres : reservedBasisNames.contains cv.name = false)
    (hnd : Name.nodup cv.levelParams = true)
    (hlb : cv.type.looseBVarsBounded 0 = true)
    (hif : cv.type.hasFvar = false)
    (htp : cv.type.allLevelParamsDefined cv.levelParams = true)
    (htr : cv.type.constsResolve env = true)
    (hst : inferTypeCore μ env F 0 cv.type = .ok stype)
    (hsort : ensureSortCore μ env F 0 stype = .ok u) :
    classConstOk (fueledOps μ F) (mkFEnv env) cv = .ok () := by
  simp only [classConstOk, mkFEnv_find?, constsResolveF_eq, mkFEnv_env, fueledOps_inferType,
    fueledOps_ensureSort, Bind.bind, Except.bind, Pure.pure, Except.pure, hfind, hres,
    hnd, hlb, hif, htp, htr, hst, hsort, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte]

theorem genRec_of_facts (ops : CheckerOps (Except CheckError)) (env : Env)
    (p : BlockShape) (nested : Bool) (params : List Expr) (tbl : List NestCtorNf)
    (rd : ClassRead) (Ms Ms' : List TargetMajor) (cvTas : List ConstantVal)
    (block : List ConstantInfo) (cvRis : List ConstantVal) (ctors : List (List ClassCtor))
    (formers pre : List Expr) (cvGs : List ConstantVal)
    (out : List (ConstantVal × TargetMajor × List Expr))
    (hp : targetRecPins (m := Except CheckError) p block = .ok ())
    (hs : classStreamRecs ops (mkFEnv env) p.recs = .ok cvRis)
    (hk : 0 < p.k)
    (hl : (p.large && !blockLargeElimAllowed p (nested || Ms.any (·.member.isNone))) = false)
    (hn : classesNfs ops env p (cvTas.map (·.type)) tbl Ms = .ok Ms')
    (hc : classesCtors ops env p (cvTas.map (·.type)) rd Ms' 0 Ms' = .ok ctors)
    (hm : ((rd.slots.filter ClassSlot.isMinor).length == (ctors.map List.length).sum) = true)
    (hf : Ms'.mapM (classFormerTy (m := Except CheckError) (mkFEnv env) cvTas) = .ok formers)
    (hpre : (ClassGen.mk p.nP params Ms' formers rd.slots ctors (structElimLevel p.elim p.large) []).prefixBinders = some pre)
    (ht : classRecTysOk ops (mkFEnv env) (ClassGen.mk p.nP params Ms' formers rd.slots ctors (structElimLevel p.elim p.large) pre) p.k p.recs cvRis rd.recCls = .ok cvGs)
    (hr : classRecsRulesOk ops StructWalkers.plain (mkFEnv env)
      (classFeR p Ms' cvGs rd.recCls (mkFEnv env))
      (ClassGen.mk p.nP params Ms' formers rd.slots ctors (structElimLevel p.elim p.large) pre)
      (classRecOf rd.recCls cvGs) cvGs rd.recCls = .ok out) :
    genRecCheck (ShadowOps.ofOps ops) (mkFEnv env) p nested params tbl rd Ms cvTas block = .ok out := by
  simp only [genRecCheck, ShadowOps.ofOps, mkFEnv_env, hp, hs, hk, hl, hn, hc, hm, hf,
    hpre, ht, hr, unwrapOr, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte]

theorem tail_of_facts (ops : CheckerOps (Except CheckError)) (block : List ConstantInfo)
    (q : BlockPass Env) (e2 e3 result : Env) (out : List (ConstantVal × TargetMajor × List Expr))
    (isorts : List (List Level))
    (hi : checkBlockIdxSorts ops q.env₁ q.p.toBlockShape (q.p.members.zip q.cvTas) = .ok isorts)
    (h2 : consBlockCtors q.p.nP q.ctorsAs q.env₁ = e2)
    (hr : checkBlockRec ops e2 q.p (blockNestedBit q.p.toBlockShape q.kinds) q.params q.tbl.toList q.rd q.cls block q.cvTas = .ok out)
    (h3 : consBlockRecsT e2.find? q.p.toBlockShape 0 out e2 = e3)
    (ht : checkBlockTables (m := Except CheckError) q.p.toBlockShape (q.p.members.zip (q.ctorsAs.zip q.sortsss)) e3 = .ok result) :
    checkBlockTail ops block q = .ok result := by
  simp only [checkBlockTail, hi, h2, hr, h3, ht, bind, Except.bind]

theorem block_of_facts (ops : CheckerOps (Except CheckError)) (env result : Env)
    (block : List ConstantInfo) (p : BlockParts) (q : BlockPass Env)
    (hd : (p.allCtors.map (·.1.name)).Nodup ∧ p.memberNames.Nodup)
    (hp : checkBlockPass ops env p (blockRawRec p) = .ok q)
    (ht : checkBlockTail ops block q = .ok result) : checkBlock ops env block p = .ok result := by
  simp only [checkBlock, hd, and_self, ↓reduceIte, hp, ht, bind, Except.bind]

end RecursorComposition
#audit_graph_module
