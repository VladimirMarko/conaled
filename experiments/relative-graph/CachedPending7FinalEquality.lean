import CachedPending7Value
/-! Experimental final conversion for the actual private matcher in #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedPending7FinalEquality
open ConLeche ConLeche.Cached CachedPending7Stages CachedPending7Value NativeHelper7
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
checked_normal_form lhs0 : Expr := valueType
checked_normal_form rhs0 : Expr := cv.type
def m0 := valueMemo
checked_normal_form a0 : Expr := match lhs0 with | .forallE a _ => a | _ => .bvar 0
checked_normal_form b0 : Expr := match rhs0 with | .forallE a _ => a | _ => .bvar 0
checked_normal_form dl0 : Expr := match lhs0 with | .forallE _ b => b | _ => .bvar 0
checked_normal_form dr0 : Expr := match rhs0 with | .forallE _ b => b | _ => .bvar 0
checked_normal_form domain0 : Except CheckError (Bool × CState) :=
  (coreKnotI .verified fe 4611686018427387903).defeq 0 a0 b0 m0
def m1 := (domain0.toOption.map Prod.snd).getD {}
checked_normal_form lhs1 : Expr := dl0.instantiate1 (.fvar 0 b0)
checked_normal_form rhs1 : Expr := dr0.instantiate1 (.fvar 0 b0)
checked_normal_form a1 : Expr := match lhs1 with | .forallE a _ => a | _ => .bvar 0
checked_normal_form b1 : Expr := match rhs1 with | .forallE a _ => a | _ => .bvar 0
checked_normal_form dl1 : Expr := match lhs1 with | .forallE _ b => b | _ => .bvar 0
checked_normal_form dr1 : Expr := match rhs1 with | .forallE _ b => b | _ => .bvar 0
checked_normal_form domain1 : Except CheckError (Bool × CState) :=
  (coreKnotI .verified fe 4611686018427387902).defeq 1 a1 b1 m1
def m2 := (domain1.toOption.map Prod.snd).getD {}
checked_normal_form lhs2 : Expr := dl1.instantiate1 (.fvar 1 b1)
checked_normal_form rhs2 : Expr := dr1.instantiate1 (.fvar 1 b1)
checked_normal_form a2 : Expr := match lhs2 with | .forallE a _ => a | _ => .bvar 0
checked_normal_form b2 : Expr := match rhs2 with | .forallE a _ => a | _ => .bvar 0
checked_normal_form dl2 : Expr := match lhs2 with | .forallE _ b => b | _ => .bvar 0
checked_normal_form dr2 : Expr := match rhs2 with | .forallE _ b => b | _ => .bvar 0
checked_normal_form domain2 : Except CheckError (Bool × CState) :=
  (coreKnotI .verified fe 4611686018427387901).defeq 2 a2 b2 m2
def m3 := (domain2.toOption.map Prod.snd).getD {}
checked_normal_form lhs3 : Expr := dl2.instantiate1 (.fvar 2 b2)
checked_normal_form rhs3 : Expr := dr2.instantiate1 (.fvar 2 b2)
checked_normal_form a3 : Expr := match lhs3 with | .forallE a _ => a | _ => .bvar 0
checked_normal_form b3 : Expr := match rhs3 with | .forallE a _ => a | _ => .bvar 0
checked_normal_form dl3 : Expr := match lhs3 with | .forallE _ b => b | _ => .bvar 0
checked_normal_form dr3 : Expr := match rhs3 with | .forallE _ b => b | _ => .bvar 0
checked_normal_form domain3 : Except CheckError (Bool × CState) :=
  (coreKnotI .verified fe 4611686018427387900).defeq 3 a3 b3 m3
def m4 := (domain3.toOption.map Prod.snd).getD {}
checked_normal_form lhs4 : Expr := dl3.instantiate1 (.fvar 3 b3)
checked_normal_form rhs4 : Expr := dr3.instantiate1 (.fvar 3 b3)
checked_normal_form a4 : Expr := match lhs4 with | .forallE a _ => a | _ => .bvar 0
checked_normal_form b4 : Expr := match rhs4 with | .forallE a _ => a | _ => .bvar 0
checked_normal_form dl4 : Expr := match lhs4 with | .forallE _ b => b | _ => .bvar 0
checked_normal_form dr4 : Expr := match rhs4 with | .forallE _ b => b | _ => .bvar 0
checked_normal_form domain4 : Except CheckError (Bool × CState) :=
  (coreKnotI .verified fe 4611686018427387899).defeq 4 a4 b4 m4
def m5 := (domain4.toOption.map Prod.snd).getD {}
checked_normal_form lhs5 : Expr := dl4.instantiate1 (.fvar 4 b4)
checked_normal_form rhs5 : Expr := dr4.instantiate1 (.fvar 4 b4)
def leafCore := coreKnotI .verified fe 4611686018427387898
checked_normal_form quick : Except CheckError (Option Bool × CState) := quickDefEqI .verified leafCore 5 lhs5 rhs5 m5
checked_normal_form prop : Except CheckError (Bool × CState) := propIrrelI leafCore fe 5 lhs5 rhs5 m5
def propMemo := (prop.toOption.map Prod.snd).getD {}
checked_normal_form leftWhnf : Except CheckError (Expr × CState) := leafCore.whnfCore true 5 lhs5 propMemo
def leftMemo := (leftWhnf.toOption.map Prod.snd).getD {}
checked_normal_form rightWhnf : Except CheckError (Expr × CState) := leafCore.whnfCore true 5 rhs5 leftMemo
def rightMemo := (rightWhnf.toOption.map Prod.snd).getD {}
measured_theorem quick_ok : quickDefEqI .verified leafCore 5 lhs5 rhs5 m5 = .ok (none,m5) := by rw [quick_eq]; rfl
measured_theorem prop_ok : propIrrelI leafCore fe 5 lhs5 rhs5 m5 = .ok (false,propMemo) := by rw [prop_eq]; rfl
measured_theorem left_ok : leafCore.whnfCore true 5 lhs5 propMemo = .ok (rhs5,leftMemo) := by rw [leftWhnf_eq]; rfl
measured_theorem right_ok : leafCore.whnfCore true 5 rhs5 leftMemo = .ok (rhs5,rightMemo) := by rw [rightWhnf_eq]; rfl
measured_theorem body_ok : defeqBodyI .verified leafCore fe 5 lhs5 rhs5 m5 = .ok (true,rightMemo) := by
  exact CachedDefeqComposition.beta_body .verified leafCore fe 5 lhs5 rhs5 rhs5 rhs5
    m5 m5 propMemo leftMemo rightMemo rightMemo (by cbv) (by cbv)
    quick_ok prop_ok left_ok right_ok (by cbv)
def out5 : CState := {rightMemo with defeqC := rightMemo.defeqC.insert (lhs5,rhs5) true}
measured_theorem leaf_ok : (coreKnotI .verified fe 4611686018427387899).defeq 5 lhs5 rhs5 m5 = .ok (true,out5) := by
  exact CachedDefeqComposition.miss .verified fe 4611686018427387898 5 lhs5 rhs5 m5 rightMemo (by cbv) body_ok
def out4 : CState := {out5 with defeqC := out5.defeqC.insert (lhs4,rhs4) true}
measured_theorem body4_ok : defeqBodyI .verified (coreKnotI .verified fe 4611686018427387899) fe 4 lhs4 rhs4 m4 = .ok (true,out5) := by
  apply CachedDefeqComposition.quick_body .verified _ fe 4 lhs4 rhs4 m4 out5 (by cbv) (by cbv)
  change quickDefEqI .verified _ 4 (.forallE a4 dl4) (.forallE b4 dr4) m4 = _
  exact CachedDefeqComposition.forall_quick .verified _ 4 a4 dl4 b4 dr4 lhs5 rhs5
    m4 m5 out5 (by cbv) (by rw [domain4_eq]; rfl) (by cbv) (by cbv) leaf_ok
measured_theorem step4_ok : (coreKnotI .verified fe 4611686018427387900).defeq 4 lhs4 rhs4 m4 = .ok (true,out4) := by
  exact CachedDefeqComposition.miss .verified fe 4611686018427387899 4 lhs4 rhs4 m4 out5 (by cbv) body4_ok
def out3 : CState := {out4 with defeqC := out4.defeqC.insert (lhs3,rhs3) true}
measured_theorem body3_ok : defeqBodyI .verified (coreKnotI .verified fe 4611686018427387900) fe 3 lhs3 rhs3 m3 = .ok (true,out4) := by
  apply CachedDefeqComposition.quick_body .verified _ fe 3 lhs3 rhs3 m3 out4 (by cbv) (by cbv)
  change quickDefEqI .verified _ 3 (.forallE a3 dl3) (.forallE b3 dr3) m3 = _
  exact CachedDefeqComposition.forall_quick .verified _ 3 a3 dl3 b3 dr3 lhs4 rhs4
    m3 m4 out4 (by cbv) (by rw [domain3_eq]; rfl) (by cbv) (by cbv) step4_ok
measured_theorem step3_ok : (coreKnotI .verified fe 4611686018427387901).defeq 3 lhs3 rhs3 m3 = .ok (true,out3) := by
  exact CachedDefeqComposition.miss .verified fe 4611686018427387900 3 lhs3 rhs3 m3 out4 (by cbv) body3_ok
def out2 : CState := {out3 with defeqC := out3.defeqC.insert (lhs2,rhs2) true}
measured_theorem body2_ok : defeqBodyI .verified (coreKnotI .verified fe 4611686018427387901) fe 2 lhs2 rhs2 m2 = .ok (true,out3) := by
  apply CachedDefeqComposition.quick_body .verified _ fe 2 lhs2 rhs2 m2 out3 (by cbv) (by cbv)
  change quickDefEqI .verified _ 2 (.forallE a2 dl2) (.forallE b2 dr2) m2 = _
  exact CachedDefeqComposition.forall_quick .verified _ 2 a2 dl2 b2 dr2 lhs3 rhs3
    m2 m3 out3 (by cbv) (by rw [domain2_eq]; rfl) (by cbv) (by cbv) step3_ok
measured_theorem step2_ok : (coreKnotI .verified fe 4611686018427387902).defeq 2 lhs2 rhs2 m2 = .ok (true,out2) := by
  exact CachedDefeqComposition.miss .verified fe 4611686018427387901 2 lhs2 rhs2 m2 out3 (by cbv) body2_ok
def out1 : CState := {out2 with defeqC := out2.defeqC.insert (lhs1,rhs1) true}
measured_theorem body1_ok : defeqBodyI .verified (coreKnotI .verified fe 4611686018427387902) fe 1 lhs1 rhs1 m1 = .ok (true,out2) := by
  apply CachedDefeqComposition.quick_body .verified _ fe 1 lhs1 rhs1 m1 out2 (by cbv) (by cbv)
  change quickDefEqI .verified _ 1 (.forallE a1 dl1) (.forallE b1 dr1) m1 = _
  exact CachedDefeqComposition.forall_quick .verified _ 1 a1 dl1 b1 dr1 lhs2 rhs2
    m1 m2 out2 (by cbv) (by rw [domain1_eq]; rfl) (by cbv) (by cbv) step2_ok
measured_theorem step1_ok : (coreKnotI .verified fe 4611686018427387903).defeq 1 lhs1 rhs1 m1 = .ok (true,out1) := by
  exact CachedDefeqComposition.miss .verified fe 4611686018427387902 1 lhs1 rhs1 m1 out2 (by cbv) body1_ok
def out0 : CState := {out1 with defeqC := out1.defeqC.insert (lhs0,rhs0) true}
measured_theorem body0_ok : defeqBodyI .verified (coreKnotI .verified fe 4611686018427387903) fe 0 lhs0 rhs0 m0 = .ok (true,out1) := by
  apply CachedDefeqComposition.quick_body .verified _ fe 0 lhs0 rhs0 m0 out1 (by cbv) (by cbv)
  change quickDefEqI .verified _ 0 (.forallE a0 dl0) (.forallE b0 dr0) m0 = _
  exact CachedDefeqComposition.forall_quick .verified _ 0 a0 dl0 b0 dr0 lhs1 rhs1
    m0 m1 out1 (by cbv) (by rw [domain0_eq]; rfl) (by cbv) (by cbv) step1_ok
measured_theorem step0_ok : (coreKnotI .verified fe 4611686018427387904).defeq 0 lhs0 rhs0 m0 = .ok (true,out0) := by
  exact CachedDefeqComposition.miss .verified fe 4611686018427387903 0 lhs0 rhs0 m0 out1 (by cbv) body0_ok
end CachedPending7FinalEquality
#audit_graph_module
