import Applications.Resources.TreeAccumulator
import Examples.TreeFoldObservations

/-! Construction and actual invocation of suffix functions, with independent
phase tariffs and comparisons to actual measured append executions. Source,
independent expectations and statement assessment:
`docs/research/fdsa-tree-accumulator-invocation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeAccumulatorExamples
open Resources Resources.TreeAccumulator
universe u
variable {α : Type u}

/-- The outer fold observes construction. Its callback captures child functions
without invoking them; their later invocation has its own entry observation. -/
def build (constructionEntry invocationEntry : Nat) (t : BinaryTree α) :
    Measured (List α → Measured (List α) Nat) Nat :=
  TreeFold.run constructionEntry (fun suffix => (suffix, invocationEntry))
    (fun left a right => pure (nodeRun invocationEntry left a right)) t

theorem build_value (constructionEntry invocationEntry : Nat) (t : BinaryTree α) :
    (build constructionEntry invocationEntry t).1 = invoke invocationEntry t :=
  TreeFold.run_value_of constructionEntry (fun suffix => (suffix, invocationEntry))
    (fun left a right => pure (nodeRun invocationEntry left a right))
    (nodeRun invocationEntry) (fun _ _ _ => rfl) t

theorem build_cost (constructionEntry invocationEntry : Nat) (t : BinaryTree α) :
    (build constructionEntry invocationEntry t).2 =
      constructionEntry * (2 * t.numNodes + 1) := by
  simpa only [Nat.zero_mul, Nat.add_zero] using
    TreeFold.run_cost_const constructionEntry (fun suffix => (suffix, invocationEntry))
      (fun left a right => pure (nodeRun invocationEntry left a right)) 0
      (fun _ _ _ => rfl) t

theorem build_exact (constructionEntry invocationEntry : Nat) (t : BinaryTree α) :
    build constructionEntry invocationEntry t =
      (invoke invocationEntry t, constructionEntry * (2 * t.numNodes + 1)) := by
  apply Prod.ext
  · exact build_value constructionEntry invocationEntry t
  · exact build_cost constructionEntry invocationEntry t

def buildOnce (constructionEntry invocationEntry : Nat) (t : BinaryTree α)
    (suffix : List α) : Measured (List α) Nat :=
  bind (build constructionEntry invocationEntry t) (fun f => f suffix)

/-- One construction supplies the same function to both actual applications. -/
def buildTwice (constructionEntry invocationEntry : Nat) (t : BinaryTree α)
    (suffix₁ suffix₂ : List α) : Measured (List α × List α) Nat :=
  bind (build constructionEntry invocationEntry t) (fun f =>
    bind (f suffix₁) (fun first =>
      bind (f suffix₂) (fun second => pure (first, second))))

theorem buildOnce_exact (constructionEntry invocationEntry : Nat) (t : BinaryTree α)
    (suffix : List α) :
    buildOnce constructionEntry invocationEntry t suffix =
      (Trees.inorder t ++ suffix,
        (constructionEntry + invocationEntry) * (2 * t.numNodes + 1)) := by
  apply Prod.ext
  · simp only [buildOnce, bind_value, build_value, invoke_value]
  · simp only [buildOnce, build_exact, bind, invoke_exact]
    ring

theorem buildTwice_exact (constructionEntry invocationEntry : Nat) (t : BinaryTree α)
    (suffix₁ suffix₂ : List α) :
    buildTwice constructionEntry invocationEntry t suffix₁ suffix₂ =
      ((Trees.inorder t ++ suffix₁, Trees.inorder t ++ suffix₂),
        (constructionEntry + 2 * invocationEntry) * (2 * t.numNodes + 1)) := by
  apply Prod.ext
  · simp only [buildTwice, bind_value, build_value, invoke_value, pure]
  · simp only [buildTwice, build_exact, bind, invoke_exact, pure]
    ring

theorem nil_nonempty : invoke 1 (.nil : BinaryTree Nat) [9, 8] = ([9, 8], 1) :=
  invoke_nil 1 [9, 8]

theorem singleton (entry : Nat) (a : α) (suffix : List α) :
    invoke entry (.node a .nil .nil) suffix = (a :: suffix, entry * 3) := by
  simpa only [Trees.inorder_node, Trees.inorder_nil, BinaryTree.numNodes,
    List.nil_append, List.cons_append] using
    invoke_exact entry (.node a .nil .nil) suffix

theorem sample (entry : Nat) (suffix : List Nat) :
    invoke entry TreeCacheExamples.sample suffix = ([0, 1, 2, 3] ++ suffix, entry * 9) := by
  rw [invoke_exact, TreeCacheExamples.sample_inorder, TreeCacheExamples.sample_size]

theorem sample_empty : invoke 1 TreeCacheExamples.sample [] = ([0, 1, 2, 3], 9) := by
  rw [sample]

theorem sample_nonempty :
    invoke 1 TreeCacheExamples.sample [9, 8] = ([0, 1, 2, 3, 9, 8], 9) := by
  rw [sample]

theorem sample_right :
    invoke 1 (.node 3 (.node 2 .nil .nil) .nil) [9, 8] = ([2, 3, 9, 8], 5) := by
  simp only [invoke_exact, Trees.inorder_node, Trees.inorder_nil, BinaryTree.numNodes,
    List.nil_append, List.cons_append]

/-- The left call consumes the returned right list, with the root consed. -/
theorem sample_left_after_right :
    invoke 1 (.node 0 .nil .nil)
      (1 :: (invoke 1 (.node 3 (.node 2 .nil .nil) .nil) [9, 8]).1) =
      ([0, 1, 2, 3, 9, 8], 3) := by
  rw [sample_right, singleton]

theorem repeated_sample :
    invoke 1 (TreeCacheExamples.sample.map (fun _ => 7)) [7, 7] =
      ([7, 7, 7, 7, 7, 7], 9) := by
  simp only [invoke_exact, Trees.inorder_map, Trees.numNodes_map,
    TreeCacheExamples.sample_inorder, TreeCacheExamples.sample_size]

theorem empty_suffix (suffix : List Empty) : suffix = [] := by
  cases suffix with
  | nil => rfl
  | cons a rest => exact Empty.elim a

theorem empty_payload (entry : Nat) (t : BinaryTree Empty) (suffix : List Empty) :
    invoke entry t suffix = ([], entry) := by
  rw [TreeCacheExamples.empty_tree t, empty_suffix suffix, invoke_nil]

/-- Both occurrences of an equal child are invoked; equality does not memoize. -/
theorem repeated_child (entry : Nat) (a : α) (t : BinaryTree α) (suffix : List α) :
    invoke entry (.node a t t) suffix =
      ((Trees.inorder t ++ (a :: Trees.inorder t)) ++ suffix,
        entry * (4 * t.numNodes + 3)) := by
  rw [invoke_exact, Trees.inorder_node]
  apply Prod.ext
  · rfl
  · simp only [BinaryTree.numNodes]
    ring

theorem zero_entry (t : BinaryTree α) (suffix : List α) :
    invoke 0 t suffix = (Trees.inorder t ++ suffix, 0) := by
  simp only [invoke_exact, Nat.zero_mul]

theorem nil_no_proportional_bound (K : Nat) :
    ¬ (invoke 1 (.nil : BinaryTree Nat) []).2 ≤ K * (.nil : BinaryTree Nat).numNodes := by
  simp only [invoke_nil, BinaryTree.numNodes, Nat.mul_zero, Nat.not_succ_le_zero]

theorem sample_build_work : (build 1 1 TreeCacheExamples.sample).2 = 9 := by
  rw [build_cost, TreeCacheExamples.sample_size]

theorem sample_build_once :
    buildOnce 1 1 TreeCacheExamples.sample [9, 8] = ([0, 1, 2, 3, 9, 8], 18) := by
  rw [buildOnce_exact, TreeCacheExamples.sample_inorder, TreeCacheExamples.sample_size]

theorem sample_build_twice :
    buildTwice 1 1 TreeCacheExamples.sample [9] [8, 8] =
      (([0, 1, 2, 3, 9], [0, 1, 2, 3, 8, 8]), 27) := by
  rw [buildTwice_exact, TreeCacheExamples.sample_inorder, TreeCacheExamples.sample_size]

/-- Unequal entry parameters distinguish construction from invocation tariffs. -/
theorem sample_distinct_tariffs :
    (buildOnce 2 3 TreeCacheExamples.sample [9, 8]).2 = 45 ∧
      (buildTwice 2 3 TreeCacheExamples.sample [9] [8, 8]).2 = 72 := by
  rw [buildOnce_exact, buildTwice_exact, TreeCacheExamples.sample_size]
  exact ⟨rfl, rfl⟩

/-- This separate program materializes the actual prefix and then appends it. -/
def materializeAppend (t : BinaryTree α) (suffix : List α) : Measured (List α) Nat :=
  bind (TreeFold.run 1 [] TreeCacheExamples.appendStepRun t)
    (fun prefix => ListReversal.appendRun prefix suffix)

theorem materializeAppend_value (t : BinaryTree α) (suffix : List α) :
    (materializeAppend t suffix).1 = Trees.inorder t ++ suffix := by
  simp only [materializeAppend, bind_value, ListReversal.appendRun_exact,
    TreeFoldExamples.single_value]

theorem materializeAppend_cost (t : BinaryTree α) (suffix : List α) :
    (materializeAppend t suffix).2 =
      (TreeFold.run 1 [] TreeCacheExamples.appendStepRun t).2 + (t.numNodes + 1) := by
  simp only [materializeAppend, bind, ListReversal.appendRun_exact,
    TreeFoldExamples.single_value, Trees.inorder_length]

theorem materializeAppend_sample :
    materializeAppend TreeCacheExamples.sample [9, 8] = ([0, 1, 2, 3, 9, 8], 20) := by
  apply Prod.ext
  · rw [materializeAppend_value, TreeCacheExamples.sample_inorder]
  · rw [materializeAppend_cost, TreeFoldExamples.single_sample, TreeCacheExamples.sample_size]

theorem equal_value_different_work :
    (invoke 1 TreeCacheExamples.sample [9, 8]).1 =
        (materializeAppend TreeCacheExamples.sample [9, 8]).1 ∧
      (invoke 1 TreeCacheExamples.sample [9, 8]).2 ≠
        (materializeAppend TreeCacheExamples.sample [9, 8]).2 := by
  rw [sample_nonempty, materializeAppend_sample]
  decide

theorem only_empty_suffix_agreement :
    invoke 1 (.nil : BinaryTree Nat) [] = ListReversal.appendRun [] [] := by
  rw [invoke_nil, ListReversal.appendRun_exact]

theorem nil_append_values (suffix : List Nat) :
    (invoke 1 .nil suffix).1 = (ListReversal.appendRun suffix []).1 := by
  rw [invoke_nil, ListReversal.appendRun_exact, List.append_nil]

/-- Agreement at [] and of all erased values does not give a uniform work law. -/
theorem nonempty_suffix_work_differs :
    (invoke 1 (.nil : BinaryTree Nat) [9]).2 ≠
      (ListReversal.appendRun [9] []).2 := by
  rw [invoke_nil, ListReversal.appendRun_exact]
  decide

end TreeAccumulatorExamples
