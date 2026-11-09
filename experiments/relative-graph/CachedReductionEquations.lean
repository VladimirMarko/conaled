import CachedBinderComposition

/-! Experimental projection equations for checked reduction of #417 artifacts.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedReductionEquations
open ConLeche ConLeche.Cached

@[cbv_eval] theorem infer (mode : CheckMode) (fe : FEnv) (fuel d : Nat) (e : Expr) :
    (coreKnotI mode fe (fuel + 1)).infer d e =
      memoEI (·.inferC) (fun s mp => {s with inferC := mp})
        (fun d e => inferBodyI (coreKnotI mode fe fuel) fe d e) d e := rfl

@[cbv_eval] theorem whnf (mode : CheckMode) (fe : FEnv) (fuel d : Nat) (e : Expr) :
    (coreKnotI mode fe (fuel + 1)).whnf d e =
      memoEI (·.whnfC) (fun s mp => {s with whnfC := mp})
        (fun d e => whnfBodyI (coreKnotI mode fe fuel) fe d e) d e := rfl

@[cbv_eval] theorem whnfCore (mode : CheckMode) (fe : FEnv) (fuel d : Nat) (cheap : Bool) (e : Expr) :
    (coreKnotI mode fe (fuel + 1)).whnfCore cheap d e =
      (if cheap then
        memoEI (·.whnfCoreCheapC) (fun s mp => {s with whnfCoreCheapC := mp})
          (fun d e => whnfCoreBodyI mode (coreKnotI mode fe fuel) fe true d e)
      else memoEI (·.whnfCoreC) (fun s mp => {s with whnfCoreC := mp})
          (fun d e => whnfCoreBodyI mode (coreKnotI mode fe fuel) fe false d e)) d e := rfl

@[cbv_eval] theorem defeq (mode : CheckMode) (fe : FEnv) (fuel d : Nat) (a b : Expr) :
    (coreKnotI mode fe (fuel + 1)).defeq d a b =
      memoBI (fun d a b => defeqBodyI mode (coreKnotI mode fe fuel) fe d a b) d a b := rfl

@[cbv_eval] theorem defeqE (mode : CheckMode) (fe : FEnv) (fuel d : Nat) (a b : Expr) :
    (coreKnotI mode fe (fuel + 1)).defeqE d a b =
      withEagerMemos mode
        (memoBI (fun d a b => defeqBodyI mode.toEager (coreKnotI mode.toEager fe fuel) fe d a b) d a b) := rfl

@[cbv_eval] theorem inferIO (mode : CheckMode) (fe : FEnv) (fuel d : Nat) (e : Expr) :
    (coreKnotI mode fe (fuel + 1)).inferIO d e =
      memoEI (·.inferIOC) (fun s mp => {s with inferIOC := mp})
        (fun d e => inferBodyIOI (coreKnotI mode fe fuel).ioView fe d e) d e := rfl
@[cbv_eval] theorem index (env : Env) : (mkFEnv env).idx = (mkFEnvGo env.consts).2 := rfl
@[cbv_eval] theorem visible (env : Env) : (mkFEnv env).visibleBelow = (mkFEnvGo env.consts).1 := rfl
@[cbv_eval] theorem base (env : Env) : (mkFEnv env).base = {} := rfl
@[cbv_eval] theorem overlay (env : Env) : (mkFEnv env).ovl = [] := rfl
@[cbv_eval] theorem tables (env : Env) : (mkFEnv env).tbls = mkTblsGo env.tables := rfl

@[cbv_eval] theorem lams_app (r : CoreFnsI) (d fuel : Nat) (a b : Expr)
    (k : Nat) (fvs : Array Expr) (stk : List Expr) :
    inferLamsI r d fuel (.app a b) k fvs stk = inferLamsLeafI r d (.app a b) k fvs stk := by
  cases fuel <;> rfl

end CachedReductionEquations
#audit_graph_module
