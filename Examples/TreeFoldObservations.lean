import Examples.TreeFoldCache
import Mathlib.Algebra.Group.TypeTags.Basic

/-! Ordered words, product observations and a reachable-summary boundary for
the same measured fold. Independent calculations and statement assessment:
`docs/research/fdsa-tree-fold-resource.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeFoldObservationExamples
open Resources Resources.TreeFold
universe u v
variable {α : Type u} {β : Type v}

/-- Separate entry and callback observations in the actual measured operation. -/
def splitRun (empty : β) (combineRun : β → α → β → Measured β Nat)
    (t : BinaryTree α) : Measured β (Nat × Nat) :=
  run (1, 0) empty
    (fun l a r => reweight (AddMonoidHom.inr Nat Nat) (combineRun l a r)) t

def total : Nat × Nat →+ Nat := AddMonoidHom.fst Nat Nat + AddMonoidHom.snd Nat Nat

/-- Projection erases callback work while preserving its actual returned value. -/
theorem split_first_run (empty : β) (combineRun : β → α → β → Measured β Nat)
    (t : BinaryTree α) :
    reweight (AddMonoidHom.fst Nat Nat) (splitRun empty combineRun t) =
      run 1 empty (fun l a r => Resources.pure (combineRun l a r).1) t := by
  unfold splitRun
  rw [Resources.TreeFold.reweight_run]
  rfl

theorem split_second_run (empty : β) (combineRun : β → α → β → Measured β Nat)
    (t : BinaryTree α) :
    reweight (AddMonoidHom.snd Nat Nat) (splitRun empty combineRun t) =
      run 0 empty combineRun t := by
  unfold splitRun
  rw [Resources.TreeFold.reweight_run]
  rfl

/-- The sum hom returns the original entry-one execution, including its value. -/
theorem split_total_run (empty : β) (combineRun : β → α → β → Measured β Nat)
    (t : BinaryTree α) :
    reweight total (splitRun empty combineRun t) = run 1 empty combineRun t := by
  unfold splitRun
  rw [Resources.TreeFold.reweight_run]
  have hc : (fun l a r => reweight total
      (reweight (AddMonoidHom.inr Nat Nat) (combineRun l a r))) = combineRun := by
    funext l a r
    apply Prod.ext
    · rfl
    · change 0 + (combineRun l a r).2 = (combineRun l a r).2
      exact Nat.zero_add _
  rw [hc]
  rfl

theorem split_structural (empty : β) (combineRun : β → α → β → Measured β Nat)
    (t : BinaryTree α) : (splitRun empty combineRun t).2.1 = 2 * t.numNodes + 1 := by
  calc
    (splitRun empty combineRun t).2.1 =
        (run 1 empty (fun l a r => Resources.pure (combineRun l a r).1) t).2 :=
      congrArg Prod.snd (split_first_run empty combineRun t)
    _ = 2 * t.numNodes + 1 := by
      simpa only [Nat.zero_mul, Nat.add_zero, Nat.one_mul] using
        run_cost_const 1 empty (fun l a r => Resources.pure (combineRun l a r).1) 0
          (fun _ _ _ => rfl) t

theorem split_work (empty : β) (combineRun : β → α → β → Measured β Nat)
    (t : BinaryTree α) :
    (splitRun empty combineRun t).2.2 = (run 0 empty combineRun t).2 :=
  congrArg Prod.snd (split_second_run empty combineRun t)

theorem split_total (empty : β) (combineRun : β → α → β → Measured β Nat)
    (t : BinaryTree α) :
    (splitRun empty combineRun t).2.1 + (splitRun empty combineRun t).2.2 =
      (run 1 empty combineRun t).2 :=
  congrArg Prod.snd (split_total_run empty combineRun t)

theorem append_sample_pair :
    (splitRun [] TreeCacheExamples.appendStepRun TreeCacheExamples.sample).2 = (9, 6) := by
  apply Prod.ext
  · rw [split_structural, TreeCacheExamples.sample_size]
  · have h : 9 +
        (splitRun [] TreeCacheExamples.appendStepRun TreeCacheExamples.sample).2.2 =
          9 + 6 := by
      simpa only [split_structural, TreeCacheExamples.sample_size,
        TreeFoldExamples.single_sample] using
        split_total [] TreeCacheExamples.appendStepRun TreeCacheExamples.sample
    exact Nat.add_left_cancel h

theorem cache_pair (t : BinaryTree α) :
    (splitRun (BinaryTree.nil : BinaryTree (α × Nat))
      (TreeCache.nodeRun 0 TreeCacheExamples.sizeRun) t).2 =
      (2 * t.numNodes + 1, 3 * t.numNodes) := by
  apply Prod.ext
  · exact split_structural _ _ t
  · rw [split_work]
    change (TreeFoldCacheExamples.annotateRun 0 0 TreeCacheExamples.sizeRun t).2 =
      3 * t.numNodes
    rw [TreeFoldCacheExamples.size_cost]
    simp

theorem cache_sample_pair :
    (splitRun .nil (TreeCache.nodeRun 0 TreeCacheExamples.sizeRun)
      TreeCacheExamples.sample).2 = (9, 12) := by
  simpa only [TreeCacheExamples.sample_size] using cache_pair TreeCacheExamples.sample

abbrev Trace := Additive (FreeMonoid Nat)

def traceStep (l a r : Nat) : Measured Nat Trace :=
  (l + r + 1, Additive.ofMul (FreeMonoid.of a))

def words (w : Trace) : List Nat := FreeMonoid.toList w.toMul

theorem trace_value (entry : Trace) (t : BinaryTree Nat) :
    (run entry 0 traceStep t).1 = t.numNodes := by
  rw [run_value_of entry 0 traceStep (fun l (_ : Nat) r => l + r + 1)
    (fun _ _ _ => rfl)]
  exact Trees.fold_numNodes t

/-- Left subtree, right subtree, callback, then structural entry, in that order. -/
theorem trace_node (entry : Trace) (a : Nat) (l r : BinaryTree Nat) :
    words (run entry 0 traceStep (.node a l r)).2 =
      (words (run entry 0 traceStep l).2 ++
        (words (run entry 0 traceStep r).2 ++ [a])) ++ words entry := by
  simp only [run_node_cost, traceStep, words, toMul_add, toMul_ofMul,
    FreeMonoid.toList_mul, FreeMonoid.toList_of]

theorem trace_sample :
    (run (0 : Trace) 0 traceStep TreeCacheExamples.sample).1 = 4 ∧
      words (run (0 : Trace) 0 traceStep TreeCacheExamples.sample).2 = [0, 2, 3, 1] := by
  constructor
  · rw [trace_value, TreeCacheExamples.sample_size]
  · simp only [TreeCacheExamples.sample, trace_node, Resources.TreeFold.run_nil]
    rfl

def entryToken : Trace := Additive.ofMul (FreeMonoid.of 0)

theorem singleton_trace :
    words (run entryToken 0 traceStep (.node 1 .nil .nil)).2 = [0, 0, 1, 0] := by
  simp only [trace_node, Resources.TreeFold.run_nil]
  rfl

theorem collected_trace :
    words ((run (0 : Trace) 0 traceStep (.node 1 .nil .nil)).2 + 3 • entryToken) =
      [1, 0, 0, 0] := by
  simp only [run_node_cost, Resources.TreeFold.run_nil, traceStep, words, entryToken,
    toMul_add, toMul_zero, toMul_ofMul, toMul_nsmul, pow_succ, pow_zero,
    FreeMonoid.toList_mul, FreeMonoid.toList_one, FreeMonoid.toList_of,
    List.nil_append, List.append_nil, List.cons_append]

/-- Collecting all three entries at the end changes this noncommutative trace. -/
theorem trace_not_collected :
    (run entryToken 0 traceStep (.node 1 .nil .nil)).2 ≠
      (run (0 : Trace) 0 traceStep (.node 1 .nil .nil)).2 + 3 • entryToken := by
  intro h
  have hw := congrArg words h
  rw [singleton_trace, collected_trace] at hw
  exact (by decide : ([0, 0, 1, 0] : List Nat) ≠ [1, 0, 0, 0]) hw

/-- The actual callback resets its summary, but charges an unreachable pair. -/
def resetStep (l : Nat) (_ : α) (r : Nat) : Measured Nat Nat :=
  (0, if l = 0 ∧ r = 0 then 0 else 7)

theorem reset_value (entry : Nat) (t : BinaryTree α) :
    (run entry 0 resetStep t).1 = 0 := by
  rw [run_value]
  cases t <;> rfl

theorem reset_reached_cost (entry : Nat) (l : BinaryTree α) (a : α)
    (r : BinaryTree α) :
    (resetStep (run entry 0 resetStep l).1 a (run entry 0 resetStep r).1).2 = 0 := by
  rw [reset_value, reset_value]
  simp [resetStep]

/-- The zero reached bound and the structural lower bound agree exactly.
Both child runs still contribute, although their summaries are discarded. -/
theorem reset_cost (entry : Nat) (t : BinaryTree α) :
    (run entry 0 resetStep t).2 = entry * (2 * t.numNodes + 1) := by
  apply Nat.le_antisymm
  · simpa only [Nat.zero_mul, Nat.add_zero] using
      run_cost_le entry 0 resetStep 0
        (fun l a r => Nat.le_of_eq (reset_reached_cost entry l a r)) t
  · exact structural_le_cost entry 0 resetStep t

theorem reset_unreachable (a : α) : (resetStep 1 a 0).2 = 7 := rfl

theorem reset_not_global (a : α) : ¬ ∀ l r, (resetStep l a r).2 = 0 := by
  intro h
  have hz : (7 : Nat) = 0 := by simpa only [reset_unreachable] using h 1 0
  exact (by decide : (7 : Nat) ≠ 0) hz

end TreeFoldObservationExamples
