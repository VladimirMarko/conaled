import CachedPositivityComposition

/-! Experimental exact cached pass composition for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedPassComposition
open ConLeche ConLeche.Cached CachedTransitionComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

measured_theorem pass : ∀ (mode : CheckMode) (fe fe1 : FEnv) (p0 : BlockParts)
    (isRec : Bool) (cvs : List ConstantVal) (shape : BlockShape)
    (ctors : List (List (ConstantVal × Nat))) (sorts : List (List (List Level)))
    (ctx : NestCtx) (holes : List Expr) (rd : ClassRead) (cls : List TargetMajor)
    (kinds : List (List (List NestFieldKind))) (nfs : List (List Expr)) (pos st : NestState)
    (s s1 sf s2 s3 s4 s5 s6 : CState),
    checkBlockIndsF (sharedOpsC mode fe) fe p0 isRec s = .ok ((fe1,cvs,shape),s1) →
    flushC s1 = .ok ((),sf) →
    checkBlockCtorsF (sharedOpsC mode fe1) fe1 fe1 (p0.complete shape).toBlockShape
      ((p0.complete shape).members.zip cvs) sf = .ok ((ctors,sorts),s2) →
    blockNestCtx (m := CheckCM) (p0.complete shape).toBlockShape cvs fe1.find? s2 = .ok ((ctx,holes),s3) →
    checkBlockClasses (sharedOpsC mode fe1) fe1 (p0.complete shape).toBlockShape ctx.params ctors s3 =
      .ok ((rd,cls),s4) →
    checkBlockPositivity (sharedOpsC mode fe1) fe1.env fe1.find? (p0.complete shape) cvs ctors s4 =
      .ok ((kinds,nfs,pos),s5) →
    nestSeeds (sharedOpsC mode fe1) fe1.env ctx (classSeeds ctx holes cls) pos s5 = .ok (st,s6) →
    checkBlockPassS mode fe p0 isRec s =
      .ok (⟨fe1,cvs,p0.complete shape,ctors,sorts,kinds,nfs,ctx.params,rd,cls,st.ctorNfs⟩,s6) := by
  intro mode fe fe1 p0 isRec cvs shape ctors sorts ctx holes rd cls kinds nfs pos st
    s s1 sf s2 s3 s4 s5 s6 hi hf hc hx hr hp hs
  unfold checkBlockPassS
  refine bind_ok _ _ s s1 s6 (fe1,cvs,shape) _ hi ?_
  refine bind_ok _ _ s1 sf s6 () _ hf ?_
  refine bind_ok _ _ sf s2 s6 (ctors,sorts) _ hc ?_
  refine bind_ok _ _ s2 s3 s6 (ctx,holes) _ hx ?_
  refine bind_ok _ _ s3 s4 s6 (rd,cls) _ hr ?_
  refine bind_ok _ _ s4 s5 s6 (kinds,nfs,pos) _ hp ?_
  refine bind_ok _ _ s5 s6 s6 st _ hs ?_
  rfl
end CachedPassComposition
#audit_graph_module
