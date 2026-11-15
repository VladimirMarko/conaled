import Applications.Resources.TreeTraversalWork
import Applications.Resources.Growth
import Examples.TreeAccumulatorObservations
import Mathlib.Tactic.NormNum

/-! Shape-sensitive exact work and growth of the existing actual traversals.
The suffix-program comparison includes construction. The cached-tree result
is compared through its reader, not identified with a returned list.
Source, independent cases and statement assessment:
`docs/research/fdsa-tree-traversal-work.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeTraversalWorkExamples
open Resources Resources.TreeFold
universe u v
variable {α : Type u} {β : Type v}

/-- The existing concrete Unit chain is a specialization of the shared family. -/
theorem old_chain (n : Nat) : Trees.leftChain () n = TreeCacheExamples.chain n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Trees.leftChain, TreeCacheExamples.chain, ih]

theorem single_cost (entry : Nat) (t : BinaryTree α) :
    (run entry [] TreeCacheExamples.appendStepRun t).2 =
      entry * (2 * t.numNodes + 1) + Trees.leftSizeSum t + t.numNodes := by
  simpa only [Nat.one_mul] using
    run_cost_leftSizeSum entry [] TreeCacheExamples.appendStepRun 1 1
      (fun l a r => by
        simp only [TreeFoldExamples.single_step_cost, TreeFoldExamples.single_value,
          Trees.inorder_length, Nat.one_mul]) t

theorem right_cost (entry : Nat) (t : BinaryTree α) :
    (run entry [] TreeFoldExamples.rightStepRun t).2 =
      entry * (2 * t.numNodes + 1) + Trees.leftSizeSum t + 3 * t.numNodes := by
  simpa only [Nat.one_mul] using
    run_cost_leftSizeSum entry [] TreeFoldExamples.rightStepRun 1 3
      (fun l a r => by
        simp only [TreeFoldExamples.right_step_cost, TreeFoldExamples.right_value,
          Trees.inorder_length, Nat.one_mul]) t

theorem left_cost (entry : Nat) (t : BinaryTree α) :
    (run entry [] TreeFoldExamples.leftStepRun t).2 =
      entry * (2 * t.numNodes + 1) + 2 * Trees.leftSizeSum t + 3 * t.numNodes :=
  run_cost_leftSizeSum entry [] TreeFoldExamples.leftStepRun 2 3
    (fun l a r => by
      simp only [TreeFoldExamples.left_step_cost, TreeFoldExamples.left_value,
        Trees.inorder_length]) t

/-- The callback uses the actual returned child's cache. Its reader theorem
comes from recursive validity and erasure, not an assumed correct raw cache. -/
theorem cache_cost (entry : Nat) (t : BinaryTree α) :
    (TreeFoldCacheExamples.annotateRun entry [] TreeCacheExamples.appendStepRun t).2 =
      entry * (2 * t.numNodes + 1) + Trees.leftSizeSum t + 4 * t.numNodes := by
  have hcost : ∀ (l : BinaryTree α) (a : α) (r : BinaryTree α),
      (TreeCache.nodeRun [] TreeCacheExamples.appendStepRun
        (run entry .nil (TreeCache.nodeRun [] TreeCacheExamples.appendStepRun) l).1 a
        (run entry .nil (TreeCache.nodeRun [] TreeCacheExamples.appendStepRun) r).1).2 =
          1 * l.numNodes + 4 := by
    intro l a r
    have hread : Trees.Cached.read []
        (run entry .nil (TreeCache.nodeRun [] TreeCacheExamples.appendStepRun) l).1 =
          Trees.inorder l := TreeFoldCacheExamples.list_read entry l
    simp only [Nat.one_mul]
    rw [TreeCacheExamples.append_node_cost, hread, Trees.inorder_length]
  simpa only [TreeFoldCacheExamples.annotateRun, Nat.one_mul] using
    run_cost_leftSizeSum entry (BinaryTree.nil : BinaryTree (α × List α))
      (TreeCache.nodeRun [] TreeCacheExamples.appendStepRun) 1 4 hcost t

theorem right_eq_single_add (entry : Nat) (t : BinaryTree α) :
    (run entry [] TreeFoldExamples.rightStepRun t).2 =
      (run entry [] TreeCacheExamples.appendStepRun t).2 + 2 * t.numNodes := by
  rw [right_cost, single_cost]
  ring

theorem left_eq_right_add (entry : Nat) (t : BinaryTree α) :
    (run entry [] TreeFoldExamples.leftStepRun t).2 =
      (run entry [] TreeFoldExamples.rightStepRun t).2 + Trees.leftSizeSum t := by
  rw [left_cost, right_cost]
  ring

theorem cache_eq_single_add (entry : Nat) (t : BinaryTree α) :
    (TreeFoldCacheExamples.annotateRun entry [] TreeCacheExamples.appendStepRun t).2 =
      (run entry [] TreeCacheExamples.appendStepRun t).2 + 3 * t.numNodes := by
  rw [cache_cost, single_cost]
  ring

/-- Compare given inputs; computing a map is not part of these executions. -/
theorem right_cost_map (entry : Nat) (label : α → β) (t : BinaryTree α) :
    (run entry [] TreeFoldExamples.rightStepRun (t.map label)).2 =
      (run entry [] TreeFoldExamples.rightStepRun t).2 := by
  rw [right_cost, right_cost, Trees.numNodes_map, Trees.leftSizeSum_map]

theorem pure_callback_cost (entry : Nat) (t : BinaryTree α) :
    (run entry 0 TreeCacheExamples.sizeRun t).2 =
      entry * (2 * t.numNodes + 1) := by
  simpa only [Nat.zero_mul, Nat.add_zero] using
    run_cost_leftSizeSum entry 0 TreeCacheExamples.sizeRun 0 0
      (fun _ _ _ => by
        simp only [TreeCacheExamples.sizeRun, Resources.pure, Nat.zero_mul, Nat.add_zero]) t

theorem zero_pure_callback (t : BinaryTree α) :
    (run 0 0 TreeCacheExamples.sizeRun t).2 = 0 := by
  rw [pure_callback_cost, Nat.zero_mul]

private theorem size_le_square (n : Nat) (hn : 0 < n) : n ≤ n ^ 2 := by
  have h := Nat.succ_le_of_lt hn
  simpa only [Nat.mul_one, pow_two] using Nat.mul_le_mul_left n h

private theorem entry_le_square (entry n : Nat) (hn : 0 < n) :
    entry * (2 * n + 1) ≤ 3 * entry * n ^ 2 := by
  have h := Nat.succ_le_of_lt hn
  calc
    entry * (2 * n + 1) ≤ entry * (3 * n) :=
      Nat.mul_le_mul_left entry (by omega)
    _ = 3 * entry * n := by ring
    _ ≤ 3 * entry * n ^ 2 := Nat.mul_le_mul_left _ (size_le_square n hn)

theorem single_cost_le_square (entry : Nat) (t : BinaryTree α) (hn : 0 < t.numNodes) :
    (run entry [] TreeCacheExamples.appendStepRun t).2 ≤
      (3 * entry + 1) * t.numNodes ^ 2 := by
  rw [single_cost]
  have he := entry_le_square entry t.numNodes hn
  have ha := Trees.leftSizeSum_add_size_le t
  nlinarith only [he, ha]

theorem right_cost_le_square (entry : Nat) (t : BinaryTree α) (hn : 0 < t.numNodes) :
    (run entry [] TreeFoldExamples.rightStepRun t).2 ≤
      (3 * entry + 3) * t.numNodes ^ 2 := by
  rw [right_cost]
  have he := entry_le_square entry t.numNodes hn
  have ha := Trees.leftSizeSum_add_size_le t
  have hsq := size_le_square t.numNodes hn
  nlinarith only [he, ha, hsq]

theorem left_cost_le_square (entry : Nat) (t : BinaryTree α) (hn : 0 < t.numNodes) :
    (run entry [] TreeFoldExamples.leftStepRun t).2 ≤
      (3 * entry + 3) * t.numNodes ^ 2 := by
  rw [left_cost]
  have he := entry_le_square entry t.numNodes hn
  have ha := Trees.twice_leftSizeSum_add_size_le t
  have hsq := size_le_square t.numNodes hn
  nlinarith only [he, ha, hsq]

theorem cache_cost_le_square (entry : Nat) (t : BinaryTree α) (hn : 0 < t.numNodes) :
    (TreeFoldCacheExamples.annotateRun entry [] TreeCacheExamples.appendStepRun t).2 ≤
      (3 * entry + 4) * t.numNodes ^ 2 := by
  rw [cache_cost]
  have he := entry_le_square entry t.numNodes hn
  have ha := Trees.leftSizeSum_add_size_le t
  have hsq := size_le_square t.numNodes hn
  nlinarith only [he, ha, hsq]

theorem right_leftChain_exact (entry : Nat) (a : α) (n : Nat) :
    run entry [] TreeFoldExamples.rightStepRun (Trees.leftChain a n) =
      (List.replicate n a, entry * (2 * n + 1) + n.choose 2 + 3 * n) := by
  apply Prod.ext
  · rw [TreeFoldExamples.right_value, Trees.inorder_leftChain]
  · rw [right_cost, Trees.leftChain_numNodes, Trees.leftSizeSum_leftChain]

theorem right_rightChain_exact (entry : Nat) (a : α) (n : Nat) :
    run entry [] TreeFoldExamples.rightStepRun (Trees.rightChain a n) =
      (List.replicate n a, (2 * entry + 3) * n + entry) := by
  apply Prod.ext
  · rw [TreeFoldExamples.right_value, Trees.inorder_rightChain]
  · rw [right_cost, Trees.rightChain_numNodes, Trees.leftSizeSum_rightChain]
    ring

theorem right_rightChain_cost (entry : Nat) (a : α) (n : Nat) :
    (run entry [] TreeFoldExamples.rightStepRun (Trees.rightChain a n)).2 =
      (2 * entry + 3) * n + entry :=
  congrArg Prod.snd (right_rightChain_exact entry a n)

/-- Every size has a supplied-label witness; nil is included in this lower bound. -/
theorem right_leftChain_lower (entry : Nat) (a : α) (n : Nat) :
    n ^ 2 ≤ 2 * (run entry [] TreeFoldExamples.rightStepRun (Trees.leftChain a n)).2 := by
  rw [right_cost, Trees.leftChain_numNodes]
  have ha := Trees.twice_leftSizeSum_leftChain a n
  nlinarith [Nat.zero_le (entry * (2 * n + 1)), Nat.zero_le n]

theorem right_rightChain_lower (entry : Nat) (a : α) (n : Nat) :
    n ≤ (run entry [] TreeFoldExamples.rightStepRun (Trees.rightChain a n)).2 := by
  rw [right_rightChain_cost]
  nlinarith [Nat.zero_le (entry * n), Nat.zero_le entry, Nat.zero_le n]

theorem right_rightChain_upper (entry : Nat) (a : α) (n : Nat) (hn : 1 ≤ n) :
    (run entry [] TreeFoldExamples.rightStepRun (Trees.rightChain a n)).2 ≤
      (3 * entry + 3) * n := by
  rw [right_rightChain_cost]
  have he : entry ≤ entry * n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left entry hn
  nlinarith only [he]

/-- Fixed entry, actual execution, and a quadratic witness family. -/
theorem right_leftChain_theta (entry : Nat) (a : α) :
    Asymptotics.IsTheta Filter.atTop
      (fun n => ((run entry [] TreeFoldExamples.rightStepRun (Trees.leftChain a n)).2 : ℝ))
      (fun n => ((n ^ 2 : Nat) : ℝ)) := by
  constructor
  · apply isBigO_of_nat_bound _ _ (3 * entry + 3) 1
    intro n hn
    have hp : 0 < (Trees.leftChain a n).numNodes := by
      rw [Trees.leftChain_numNodes]
      exact lt_of_lt_of_le Nat.zero_lt_one hn
    simpa only [Trees.leftChain_numNodes] using
      right_cost_le_square entry (Trees.leftChain a n) hp
  · exact isBigO_of_nat_bound _ _ 2 0 (fun n _ => right_leftChain_lower entry a n)

/-- The same literal source execution has a linear right-chain family. -/
theorem right_rightChain_theta (entry : Nat) (a : α) :
    Asymptotics.IsTheta Filter.atTop
      (fun n => ((run entry [] TreeFoldExamples.rightStepRun (Trees.rightChain a n)).2 : ℝ))
      (fun n => (n : ℝ)) := by
  constructor
  · exact isBigO_of_nat_bound _ _ (3 * entry + 3) 1
      (fun n hn => right_rightChain_upper entry a n hn)
  · simpa only [Nat.one_mul] using
      isBigO_of_nat_bound (fun n => n)
        (fun n => (run entry [] TreeFoldExamples.rightStepRun (Trees.rightChain a n)).2)
        1 0 (fun n _ => by simpa only [Nat.one_mul] using right_rightChain_lower entry a n)

theorem source_upper (t : BinaryTree α) (hn : 0 < t.numNodes) :
    (run 1 [] TreeFoldExamples.rightStepRun t).2 ≤ 6 * t.numNodes ^ 2 :=
  right_cost_le_square 1 t hn

theorem source_witness (a : α) (n : Nat) :
    (Trees.leftChain a n).numNodes = n ∧
      n ^ 2 ≤ 2 * (run 1 [] TreeFoldExamples.rightStepRun (Trees.leftChain a n)).2 :=
  ⟨Trees.leftChain_numNodes a n, right_leftChain_lower 1 a n⟩

theorem source_rightChain (a : α) (n : Nat) :
    run 1 [] TreeFoldExamples.rightStepRun (Trees.rightChain a n) =
      (List.replicate n a, 5 * n + 1) := right_rightChain_exact 1 a n

theorem nil_not_square_bound (K : Nat) :
    ¬ (run 1 [] TreeFoldExamples.rightStepRun (.nil : BinaryTree α)).2 ≤
      K * (.nil : BinaryTree α).numNodes ^ 2 := by
  simp [BinaryTree.numNodes]

theorem materialize_cost (t : BinaryTree α) (suffix : List α) :
    (TreeAccumulatorExamples.materializeAppend t suffix).2 =
      4 * t.numNodes + 2 + Trees.leftSizeSum t := by
  rw [TreeAccumulatorExamples.materializeAppend_cost, single_cost]
  ring

theorem materialize_le_square (t : BinaryTree α) (suffix : List α)
    (hn : 0 < t.numNodes) :
    (TreeAccumulatorExamples.materializeAppend t suffix).2 ≤ 6 * t.numNodes ^ 2 := by
  rw [materialize_cost]
  have ha := Trees.leftSizeSum_add_size_le t
  have hsq := size_le_square t.numNodes hn
  have hpos : 1 ≤ t.numNodes ^ 2 := le_trans (Nat.succ_le_of_lt hn) hsq
  nlinarith only [ha, hsq, hpos]

theorem materialize_buildOnce_value (t : BinaryTree α) (suffix : List α) :
    (TreeAccumulatorExamples.materializeAppend t suffix).1 =
      (TreeAccumulatorExamples.buildOnce 1 1 t suffix).1 := by
  rw [TreeAccumulatorExamples.materializeAppend_value,
    TreeAccumulatorExamples.buildOnce_exact]

/-- Construction is counted in the second actual program. This work equality
is derived separately from the equality of their erased returned lists. -/
theorem materialize_buildOnce_cost (t : BinaryTree α) (suffix : List α) :
    (TreeAccumulatorExamples.materializeAppend t suffix).2 =
      (TreeAccumulatorExamples.buildOnce 1 1 t suffix).2 + Trees.leftSizeSum t := by
  rw [materialize_cost, TreeAccumulatorExamples.buildOnce_exact]
  ring

theorem rightChain_programs (a : α) (n : Nat) (suffix : List α) :
    TreeAccumulatorExamples.materializeAppend (Trees.rightChain a n) suffix =
      TreeAccumulatorExamples.buildOnce 1 1 (Trees.rightChain a n) suffix := by
  apply Prod.ext
  · exact materialize_buildOnce_value _ _
  · rw [materialize_buildOnce_cost, Trees.leftSizeSum_rightChain, Nat.add_zero]

theorem leftChain_program_excess (a : α) (n : Nat) (suffix : List α) :
    (TreeAccumulatorExamples.materializeAppend (Trees.leftChain a n) suffix).2 =
      (TreeAccumulatorExamples.buildOnce 1 1 (Trees.leftChain a n) suffix).2 + n.choose 2 := by
  rw [materialize_buildOnce_cost, Trees.leftSizeSum_leftChain]

theorem nil_costs (entry : Nat) :
    (run entry [] TreeCacheExamples.appendStepRun (.nil : BinaryTree α)).2 = entry ∧
      (run entry [] TreeFoldExamples.rightStepRun (.nil : BinaryTree α)).2 = entry ∧
      (run entry [] TreeFoldExamples.leftStepRun (.nil : BinaryTree α)).2 = entry ∧
      (TreeFoldCacheExamples.annotateRun entry [] TreeCacheExamples.appendStepRun
        (.nil : BinaryTree α)).2 = entry := by
  rw [single_cost, right_cost, left_cost, cache_cost]
  simp [BinaryTree.numNodes]

theorem singleton_costs (entry : Nat) (a : α) :
    (run entry [] TreeCacheExamples.appendStepRun (.node a .nil .nil)).2 = 3 * entry + 1 ∧
      (run entry [] TreeFoldExamples.rightStepRun (.node a .nil .nil)).2 = 3 * entry + 3 ∧
      (run entry [] TreeFoldExamples.leftStepRun (.node a .nil .nil)).2 = 3 * entry + 3 ∧
      (TreeFoldCacheExamples.annotateRun entry [] TreeCacheExamples.appendStepRun
        (.node a .nil .nil)).2 = 3 * entry + 4 := by
  simp only [single_cost, right_cost, left_cost, cache_cost, Trees.leftSizeSum_node,
    Trees.leftSizeSum_nil, BinaryTree.numNodes]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem empty_inputs (entry : Nat) (t : BinaryTree Empty) :
    Trees.leftSizeSum t = 0 ∧
      run entry [] TreeFoldExamples.rightStepRun t = ([], entry) := by
  rw [TreeCacheExamples.empty_tree t]
  exact ⟨rfl, rfl⟩

theorem repeated_singleton (a : α) :
    Trees.leftSizeSum (.node a (.node a .nil .nil) (.node a .nil .nil)) = 1 := by
  rw [Trees.leftSizeSum_repeated]
  simp only [Trees.leftSizeSum_node, Trees.leftSizeSum_nil, BinaryTree.numNodes]

theorem sample_leftSizeSum : Trees.leftSizeSum TreeCacheExamples.sample = 2 := by
  simp only [TreeCacheExamples.sample, Trees.leftSizeSum_node, Trees.leftSizeSum_nil,
    BinaryTree.numNodes]

/-- These counts are derived through the new shared work theorem's instances. -/
theorem sample_counts :
    (run 1 [] TreeCacheExamples.appendStepRun TreeCacheExamples.sample).2 = 15 ∧
      (run 1 [] TreeFoldExamples.rightStepRun TreeCacheExamples.sample).2 = 23 ∧
      (run 1 [] TreeFoldExamples.leftStepRun TreeCacheExamples.sample).2 = 25 ∧
      (TreeFoldCacheExamples.annotateRun 1 [] TreeCacheExamples.appendStepRun
        TreeCacheExamples.sample).2 = 27 := by
  norm_num [single_cost, right_cost, left_cost, cache_cost, sample_leftSizeSum,
    TreeCacheExamples.sample_size]

/-- Removing structural entry work leaves the actual append/helper work. -/
theorem zero_entry_sample :
    (run 0 [] TreeCacheExamples.appendStepRun TreeCacheExamples.sample).2 = 6 ∧
      (run 0 [] TreeFoldExamples.rightStepRun TreeCacheExamples.sample).2 = 14 ∧
      (run 0 [] TreeFoldExamples.leftStepRun TreeCacheExamples.sample).2 = 16 ∧
      (TreeFoldCacheExamples.annotateRun 0 [] TreeCacheExamples.appendStepRun
        TreeCacheExamples.sample).2 = 18 := by
  norm_num [single_cost, right_cost, left_cost, cache_cost, sample_leftSizeSum,
    TreeCacheExamples.sample_size]

theorem noninjective_sample :
    Trees.leftSizeSum (TreeCacheExamples.sample.map (fun _ => (7 : Nat))) = 2 ∧
      run 1 [] TreeFoldExamples.rightStepRun
        (TreeCacheExamples.sample.map (fun _ => (7 : Nat))) = ([7, 7, 7, 7], 23) := by
  constructor
  · rw [Trees.leftSizeSum_map, sample_leftSizeSum]
  · apply Prod.ext
    · simp only [TreeFoldExamples.right_value, Trees.inorder_map,
        TreeCacheExamples.sample_inorder, List.map_cons, List.map_nil]
    · rw [right_cost_map]
      exact sample_counts.2.1

/-- Shape still matters when size, height and the entire returned list agree. -/
theorem same_observations_different_work (a : α) :
    (Trees.leftChain a 3).numNodes = (Trees.rightChain a 3).numNodes ∧
      (Trees.leftChain a 3).height = (Trees.rightChain a 3).height ∧
      (run 1 [] TreeFoldExamples.rightStepRun (Trees.leftChain a 3)).1 =
        (run 1 [] TreeFoldExamples.rightStepRun (Trees.rightChain a 3)).1 ∧
      Trees.leftSizeSum (Trees.leftChain a 3) = 3 ∧
      Trees.leftSizeSum (Trees.rightChain a 3) = 0 ∧
      (run 1 [] TreeFoldExamples.rightStepRun (Trees.leftChain a 3)).2 = 19 ∧
      (run 1 [] TreeFoldExamples.rightStepRun (Trees.rightChain a 3)).2 = 16 ∧
      (run 1 [] TreeFoldExamples.rightStepRun (Trees.leftChain a 3)).2 ≠
        (run 1 [] TreeFoldExamples.rightStepRun (Trees.rightChain a 3)).2 := by
  rw [Trees.leftChain_numNodes, Trees.rightChain_numNodes,
    Trees.leftChain_height, Trees.rightChain_height,
    right_leftChain_exact, right_rightChain_exact,
    Trees.leftSizeSum_leftChain, Trees.leftSizeSum_rightChain]
  norm_num

/-- The full cached-tree result is observed through its root reader and erasure. -/
theorem sample_cache_observations :
    Trees.Cached.read [] (TreeFoldCacheExamples.annotateRun 1 []
      TreeCacheExamples.appendStepRun TreeCacheExamples.sample).1 = [0, 1, 2, 3] ∧
      Trees.Cached.erase (TreeFoldCacheExamples.annotateRun 1 []
        TreeCacheExamples.appendStepRun TreeCacheExamples.sample).1 =
          TreeCacheExamples.sample ∧
      (TreeFoldCacheExamples.annotateRun 1 [] TreeCacheExamples.appendStepRun
        TreeCacheExamples.sample).2 = 27 :=
  ⟨TreeFoldCacheExamples.list_sample_read,
    TreeFoldCacheExamples.annotate_erases 1 [] TreeCacheExamples.appendStepRun
      TreeCacheExamples.listStep TreeFoldExamples.single_step_value TreeCacheExamples.sample,
    sample_counts.2.2.2⟩

theorem nil_suffix_programs (suffix : List α) :
    TreeAccumulatorExamples.materializeAppend .nil suffix = (suffix, 2) ∧
      TreeAccumulatorExamples.buildOnce 1 1 .nil suffix = (suffix, 2) := by
  constructor
  · apply Prod.ext
    · simp only [TreeAccumulatorExamples.materializeAppend_value, Trees.inorder_nil,
        List.nil_append]
    · simp [materialize_cost, BinaryTree.numNodes]
  · simpa [BinaryTree.numNodes] using
      TreeAccumulatorExamples.buildOnce_exact 1 1 (.nil : BinaryTree α) suffix

theorem singleton_suffix_programs (a : α) (suffix : List α) :
    TreeAccumulatorExamples.materializeAppend (.node a .nil .nil) suffix =
        (a :: suffix, 6) ∧
      TreeAccumulatorExamples.buildOnce 1 1 (.node a .nil .nil) suffix =
        (a :: suffix, 6) := by
  constructor
  · apply Prod.ext
    · simp [TreeAccumulatorExamples.materializeAppend_value, Trees.inorder_node]
    · simp [materialize_cost, BinaryTree.numNodes]
  · simpa [Trees.inorder_node, BinaryTree.numNodes] using
      TreeAccumulatorExamples.buildOnce_exact 1 1 (.node a .nil .nil) suffix

/-- Both complete programs return the same suffix result; construction is included. -/
theorem sample_suffix_programs (suffix : List Nat) :
    TreeAccumulatorExamples.materializeAppend TreeCacheExamples.sample suffix =
        ([0, 1, 2, 3] ++ suffix, 20) ∧
      TreeAccumulatorExamples.buildOnce 1 1 TreeCacheExamples.sample suffix =
        ([0, 1, 2, 3] ++ suffix, 18) ∧
      (TreeAccumulatorExamples.materializeAppend TreeCacheExamples.sample suffix).2 =
        (TreeAccumulatorExamples.buildOnce 1 1 TreeCacheExamples.sample suffix).2 + 2 := by
  refine ⟨?_, ?_, ?_⟩
  · apply Prod.ext
    · rw [TreeAccumulatorExamples.materializeAppend_value, TreeCacheExamples.sample_inorder]
    · norm_num [materialize_cost, sample_leftSizeSum, TreeCacheExamples.sample_size]
  · rw [TreeAccumulatorExamples.buildOnce_exact, TreeCacheExamples.sample_inorder,
      TreeCacheExamples.sample_size]
  · simpa only [sample_leftSizeSum] using
      materialize_buildOnce_cost TreeCacheExamples.sample suffix

end TreeTraversalWorkExamples
