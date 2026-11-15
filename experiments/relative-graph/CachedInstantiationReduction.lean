import CachedPendingComposition
/-! Experimental exact bulk-instantiation memo equations for #417.
See [scope](../../docs/research/relative-cached-acceptance.md). -/
namespace CachedInstantiationReduction
open ConLeche ConLeche.Cached
abbrev InstMap := Std.HashMap (Expr × List Expr × Nat) Expr
def count (m : InstMap) : Nat := m.size
attribute [cbv_opaque] count
attribute [cbv_eval] Std.HashMap.contains_insert
@[cbv_eval] theorem count_empty (n : Nat) : count (Std.HashMap.emptyWithCapacity n) = 0 :=
  Std.HashMap.size_emptyWithCapacity
@[cbv_eval] theorem count_insert (m : InstMap) (k : Expr × List Expr × Nat) (v : Expr) :
    count (m.insert k v) = if m.contains k then count m else count m + 1 := by
  simpa only [count, Std.HashMap.mem_iff_contains] using (Std.HashMap.size_insert (m := m) (k := k) (v := v))
@[cbv_eval] theorem inst_run (e : Expr) (vs : List Expr) (d : Nat) (s : CState) :
    instListM e vs d s =
      if e.bvarB ≤ d then .ok (e,s) else
      match s.instC[(e,vs,d)]? with
      | some r => .ok (r,s)
      | none =>
        let mp := if count s.instC < instCCapC then s.instC else {}
        let r := Expr.instantiateListC e vs d
        .ok (r,{s with instC := mp.insert (e,vs,d) r}) := by
  unfold instListM count
  simp only [modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
  split
  · rfl
  · cases s.instC[(e,vs,d)]? <;> rfl
end CachedInstantiationReduction
#audit_graph_module
