import CachedPending10Stages
/-! Experimental staged actual emitted backward inference for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedPending10Open
open ConLeche ConLeche.Cached CachedPending10Stages EmittedBackwardAcceptance
set_option acceptance.measureTreeSize false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option cbv.maxSteps 2000000
set_option pp.deepTerms.threshold 4
attribute [local cbv_eval] Expr.bvarBRaw_bvar Expr.bvarBRaw_fvar Expr.bvarBRaw_sort Expr.bvarBRaw_const Expr.bvarBRaw_lit Expr.bvarBRaw_app Expr.bvarBRaw_lam Expr.bvarBRaw_forallE Expr.bvarBRaw_letE Expr.bvarBRaw_proj Expr.fvarBRaw_bvar Expr.fvarBRaw_fvar Expr.fvarBRaw_sort Expr.fvarBRaw_const Expr.fvarBRaw_lit Expr.fvarBRaw_app Expr.fvarBRaw_lam Expr.fvarBRaw_forallE Expr.fvarBRaw_letE Expr.fvarBRaw_proj Expr.hasLP_bvar Expr.hasLP_fvar Expr.hasLP_sort Expr.hasLP_const Expr.hasLP_lit Expr.hasLP_app Expr.hasLP_lam Expr.hasLP_forallE Expr.hasLP_letE Expr.hasLP_proj
attribute [local cbv_eval] whnfLoopI.eq_1 whnfLoopI.eq_2 whnfCoreLoopI.eq_1 whnfCoreLoopI.eq_2
attribute [local cbv_opaque] coreKnotI mkFEnv instListM defeqLamsI
attribute [local cbv_opaque] Std.HashMap.size
attribute [local cbv_eval] coreKnotI_infer_succ coreKnotI_whnf_succ coreKnotI_whnfCore_succ
attribute [local cbv_eval] CachedTransitionComposition.infer_pis_sort
attribute [local cbv_eval] CachedBinderComposition.pis_app CachedBinderComposition.pis_fvar
attribute [local cbv_eval] mkFEnv_find? mkFEnv_env coreKnotI_defeq_succ structWalkersC_eq_plain Expr.abstractRangeC_spec Expr.abstract1C_spec
attribute [local cbv_eval] Expr.instantiateRev_spec Expr.instLevelParams_spec Expr.instantiate1LiftC_spec Expr.getAppArgsC_spec Expr.wscopedBC_spec
attribute [local cbv_eval] Expr.allLevelParamsDefinedC_spec constsResolveFC_spec constsResolveF_eq
attribute [local cbv_eval] lazyDeltaReductionI.eq_1 lazyDeltaReductionI.eq_2 lazyDeltaProjReductionI.eq_1 lazyDeltaProjReductionI.eq_2
attribute [local cbv_eval] inferLamsI.eq_def inferPisI.eq_def betaPeelI.eq_def
attribute [local cbv_eval] whnfAppI.eq_def defeqLamsI_zero defeqLamsI_succ
attribute [local cbv_eval] Std.HashMap.size_emptyWithCapacity Std.HashMap.size_empty Std.HashMap.size_insert
attribute [local cbv_eval] push_mkFEnv
attribute [local cbv_eval] Expr.instantiate1C_spec Expr.instantiateListC_spec Expr.instSpineC_spec
def lower := coreKnotI .verified fe 4611686018427387903
def raw0 := value
def fvs0 : Array Expr := #[]
def state0 := sortMemo
checked_normal_form raw1 : Expr := match raw0 with | .lam _ b => b | _ => .bvar 0
checked_normal_form dom0 : Expr := (match raw0 with | .lam a _ => a | _ => .bvar 0).instantiateRev fvs0
checked_normal_form infer0 : Except CheckError (Expr × CState) := lower.infer 0 dom0 state0
def itype0 := (infer0.toOption.map Prod.fst).getD (.bvar 0)
def imemo0 := (infer0.toOption.map Prod.snd).getD {}
checked_normal_form whnf0 : Except CheckError (Expr × CState) := lower.whnf 0 itype0 imemo0
def state1 := (whnf0.toOption.map Prod.snd).getD {}
def fvs1 := fvs0.push (.fvar 0 dom0)
checked_normal_form raw2 : Expr := match raw1 with | .lam _ b => b | _ => .bvar 0
checked_normal_form dom1 : Expr := (match raw1 with | .lam a _ => a | _ => .bvar 0).instantiateRev fvs1
checked_normal_form infer1 : Except CheckError (Expr × CState) := lower.infer 1 dom1 state1
def itype1 := (infer1.toOption.map Prod.fst).getD (.bvar 0)
def imemo1 := (infer1.toOption.map Prod.snd).getD {}
checked_normal_form whnf1 : Except CheckError (Expr × CState) := lower.whnf 1 itype1 imemo1
def state2 := (whnf1.toOption.map Prod.snd).getD {}
def fvs2 := fvs1.push (.fvar 1 dom1)
checked_normal_form raw3 : Expr := match raw2 with | .lam _ b => b | _ => .bvar 0
checked_normal_form dom2 : Expr := (match raw2 with | .lam a _ => a | _ => .bvar 0).instantiateRev fvs2
checked_normal_form infer2 : Except CheckError (Expr × CState) := lower.infer 2 dom2 state2
def itype2 := (infer2.toOption.map Prod.fst).getD (.bvar 0)
def imemo2 := (infer2.toOption.map Prod.snd).getD {}
checked_normal_form whnf2 : Except CheckError (Expr × CState) := lower.whnf 2 itype2 imemo2
def state3 := (whnf2.toOption.map Prod.snd).getD {}
def fvs3 := fvs2.push (.fvar 2 dom2)
checked_normal_form raw4 : Expr := match raw3 with | .lam _ b => b | _ => .bvar 0
checked_normal_form dom3 : Expr := (match raw3 with | .lam a _ => a | _ => .bvar 0).instantiateRev fvs3
checked_normal_form infer3 : Except CheckError (Expr × CState) := lower.infer 3 dom3 state3
def itype3 := (infer3.toOption.map Prod.fst).getD (.bvar 0)
def imemo3 := (infer3.toOption.map Prod.snd).getD {}
checked_normal_form whnf3 : Except CheckError (Expr × CState) := lower.whnf 3 itype3 imemo3
def state4 := (whnf3.toOption.map Prod.snd).getD {}
def fvs4 := fvs3.push (.fvar 3 dom3)
checked_normal_form raw5 : Expr := match raw4 with | .lam _ b => b | _ => .bvar 0
checked_normal_form dom4 : Expr := (match raw4 with | .lam a _ => a | _ => .bvar 0).instantiateRev fvs4
checked_normal_form infer4 : Except CheckError (Expr × CState) := lower.infer 4 dom4 state4
def itype4 := (infer4.toOption.map Prod.fst).getD (.bvar 0)
def imemo4 := (infer4.toOption.map Prod.snd).getD {}
checked_normal_form whnf4 : Except CheckError (Expr × CState) := lower.whnf 4 itype4 imemo4
def state5 := (whnf4.toOption.map Prod.snd).getD {}
def fvs5 := fvs4.push (.fvar 4 dom4)
checked_normal_form raw6 : Expr := match raw5 with | .lam _ b => b | _ => .bvar 0
checked_normal_form dom5 : Expr := (match raw5 with | .lam a _ => a | _ => .bvar 0).instantiateRev fvs5
checked_normal_form infer5 : Except CheckError (Expr × CState) := lower.infer 5 dom5 state5
def itype5 := (infer5.toOption.map Prod.fst).getD (.bvar 0)
def imemo5 := (infer5.toOption.map Prod.snd).getD {}
checked_normal_form whnf5 : Except CheckError (Expr × CState) := lower.whnf 5 itype5 imemo5
def state6 := (whnf5.toOption.map Prod.snd).getD {}
def fvs6 := fvs5.push (.fvar 5 dom5)
checked_normal_form raw7 : Expr := match raw6 with | .lam _ b => b | _ => .bvar 0
checked_normal_form dom6 : Expr := (match raw6 with | .lam a _ => a | _ => .bvar 0).instantiateRev fvs6
checked_normal_form infer6 : Except CheckError (Expr × CState) := lower.infer 6 dom6 state6
def itype6 := (infer6.toOption.map Prod.fst).getD (.bvar 0)
def imemo6 := (infer6.toOption.map Prod.snd).getD {}
checked_normal_form whnf6 : Except CheckError (Expr × CState) := lower.whnf 6 itype6 imemo6
def state7 := (whnf6.toOption.map Prod.snd).getD {}
def fvs7 := fvs6.push (.fvar 6 dom6)
checked_normal_form raw8 : Expr := match raw7 with | .lam _ b => b | _ => .bvar 0
checked_normal_form dom7 : Expr := (match raw7 with | .lam a _ => a | _ => .bvar 0).instantiateRev fvs7
checked_normal_form infer7 : Except CheckError (Expr × CState) := lower.infer 7 dom7 state7
def itype7 := (infer7.toOption.map Prod.fst).getD (.bvar 0)
def imemo7 := (infer7.toOption.map Prod.snd).getD {}
checked_normal_form whnf7 : Except CheckError (Expr × CState) := lower.whnf 7 itype7 imemo7
def state8 := (whnf7.toOption.map Prod.snd).getD {}
def fvs8 := fvs7.push (.fvar 7 dom7)
checked_normal_form opened : Expr := raw8.instantiateRev fvs8
checked_normal_form head : Expr := opened.getAppFn
checked_normal_form args : List Expr := opened.getAppArgs
checked_normal_form argCount : Nat := args.length
end CachedPending10Open
#audit_graph_module
