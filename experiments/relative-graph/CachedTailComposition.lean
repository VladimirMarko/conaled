import CachedTransitionComposition

/-! Experimental cached installer-tail composition for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedTailComposition
open ConLeche ConLeche.Cached CachedTransitionComposition
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

measured_theorem tail : ∀ (mode : CheckMode) (block : List ConstantInfo) (q : BlockPass FEnv)
    (fe2 final : FEnv) (out : List (ConstantVal × TargetMajor × List Expr))
    (idxSorts : List (List Level)) (s s1 s2 s3 s4 : CState),
    checkBlockIdxSortsF (sharedOpsC mode q.env₁) q.env₁ q.p.toBlockShape
      (q.p.members.zip q.cvTas) s = .ok (idxSorts,s1) →
    consBlockCtorsF q.p.nP q.ctorsAs q.env₁ = fe2 →
    flushC s1 = .ok ((),s2) →
    genRecCheck (shadowOpsC mode) fe2 q.p.toBlockShape (blockNestedBit q.p.toBlockShape q.kinds)
      q.params q.tbl.toList q.rd q.cls q.cvTas block s2 = .ok (out,s3) →
    checkBlockTablesF (m := CheckCM) structWalkersC q.p.toBlockShape
      (q.p.members.zip (q.ctorsAs.zip q.sortsss))
      (FEnv.pushAll (blockRecInfosTF fe2.find? q.p.toBlockShape 0 out) fe2) s3 = .ok (final,s4) →
    checkBlockTailS mode block q s = .ok (final,s4) := by
  intro mode block q fe2 final out idxSorts s s1 s2 s3 s4 hi he hf hg ht
  cases q
  unfold checkBlockTailS
  refine bind_ok _ _ s s1 s4 idxSorts _ hi ?_
  dsimp only at he
  rw [he]
  refine bind_ok _ _ s1 s2 s4 () _ hf ?_
  refine bind_ok _ _ s2 s3 s4 out _ hg ?_
  exact ht

measured_theorem block : ∀ (mode : CheckMode) (fe final : FEnv) (block : List ConstantInfo)
    (p : BlockParts) (q : BlockPass FEnv) (s s1 s2 s3 : CState),
    (p.allCtors.map (·.1.name)).Nodup ∧ p.memberNames.Nodup →
    flushC s = .ok ((),s1) →
    checkBlockPassS mode fe p (blockRawRec p) s1 = .ok (q,s2) →
    checkBlockTailS mode block q s2 = .ok (final,s3) →
    checkBlockKS mode fe block p s = .ok (final,s3) := by
  intro mode fe final block p q s s1 s2 s3 hd hf hp ht
  unfold checkBlockKS
  simp only [hd, ↓reduceIte]
  refine bind_ok _ _ s s1 s3 () _ hf ?_
  exact bind_ok _ _ s1 s2 s3 q _ hp ht
end CachedTailComposition
#audit_graph_module
