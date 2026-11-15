import Applications.Resources.TreeFold
import Examples.TreeCache

/-! Actual primitive and append clients of the measured tree fold.
The three append executions have the same inorder value but different work.
Independent calculations and statement assessment:
`docs/research/fdsa-tree-fold-resource.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeFoldExamples
open Resources Resources.TreeFold
universe u v
variable {α : Type u} {β : Type v}

theorem size_value (entry : Nat) (t : BinaryTree α) :
    (run entry 0 TreeCacheExamples.sizeRun t).1 = t.numNodes := by
  rw [run_value_of entry 0 TreeCacheExamples.sizeRun TreeCacheExamples.sizeStep
    (fun _ _ _ => rfl)]
  exact Trees.fold_numNodes t

theorem height_value (entry : Nat) (t : BinaryTree α) :
    (run entry 0 TreeCacheExamples.heightRun t).1 = t.height := by
  rw [run_value_of entry 0 TreeCacheExamples.heightRun TreeCacheExamples.heightStep
    (fun _ _ _ => rfl)]
  exact Trees.fold_height t

theorem size_cost (entry : Nat) (t : BinaryTree α) :
    (run entry 0 TreeCacheExamples.sizeRun t).2 = entry * (2 * t.numNodes + 1) := by
  simpa only [Nat.zero_mul, Nat.add_zero] using
    run_cost_const entry 0 TreeCacheExamples.sizeRun 0 (fun _ _ _ => rfl) t

theorem height_cost (entry : Nat) (t : BinaryTree α) :
    (run entry 0 TreeCacheExamples.heightRun t).2 = entry * (2 * t.numNodes + 1) := by
  simpa only [Nat.zero_mul, Nat.add_zero] using
    run_cost_const entry 0 TreeCacheExamples.heightRun 0 (fun _ _ _ => rfl) t

/-- A payload inhabitant is not required even by the full measured operation. -/
theorem empty_run (entry : Nat) (empty : β)
    (combineRun : β → Empty → β → Measured β Nat) (t : BinaryTree Empty) :
    run entry empty combineRun t = (empty, entry) := by
  rw [TreeCacheExamples.empty_tree t, Resources.TreeFold.run_nil]

theorem empty_primitives (entry : Nat) (t : BinaryTree Empty) :
    run entry 0 TreeCacheExamples.sizeRun t = (0, entry) ∧
      run entry 0 TreeCacheExamples.heightRun t = (0, entry) :=
  ⟨empty_run entry 0 TreeCacheExamples.sizeRun t,
    empty_run entry 0 TreeCacheExamples.heightRun t⟩

/-- Literal right-associated source append: both recursive appends run. -/
def rightStepRun (l : List α) (a : α) (r : List α) : Measured (List α) Nat :=
  Resources.bind (ListReversal.appendRun [a] r) (fun suffix => ListReversal.appendRun l suffix)

/-- A comparison execution: the second append uses the actual first result. -/
def leftStepRun (l : List α) (a : α) (r : List α) : Measured (List α) Nat :=
  Resources.bind (ListReversal.appendRun l [a]) (fun prefixList => ListReversal.appendRun prefixList r)

theorem single_step_value (l : List α) (a : α) (r : List α) :
    (TreeCacheExamples.appendStepRun l a r).1 = l ++ (a :: r) := by
  simp only [TreeCacheExamples.appendStepRun, ListReversal.appendRun_exact]

theorem right_step_value (l : List α) (a : α) (r : List α) :
    (rightStepRun l a r).1 = l ++ (a :: r) := by
  simp [rightStepRun, Resources.bind, ListReversal.appendRun_exact]

theorem left_step_value (l : List α) (a : α) (r : List α) :
    (leftStepRun l a r).1 = l ++ (a :: r) := by
  simp [leftStepRun, Resources.bind, ListReversal.appendRun_exact, List.append_assoc]

theorem single_step_cost (l : List α) (a : α) (r : List α) :
    (TreeCacheExamples.appendStepRun l a r).2 = l.length + 1 := by
  simp only [TreeCacheExamples.appendStepRun, ListReversal.appendRun_exact]

theorem right_step_cost (l : List α) (a : α) (r : List α) :
    (rightStepRun l a r).2 = l.length + 3 := by
  simp only [rightStepRun, Resources.bind, ListReversal.appendRun_exact,
    List.length_cons, List.length_nil]
  ring

theorem left_step_cost (l : List α) (a : α) (r : List α) :
    (leftStepRun l a r).2 = 2 * l.length + 3 := by
  simp only [leftStepRun, Resources.bind, ListReversal.appendRun_exact,
    List.length_append, List.length_cons, List.length_nil]
  ring

theorem single_value (entry : Nat) (t : BinaryTree α) :
    (run entry [] TreeCacheExamples.appendStepRun t).1 = Trees.inorder t :=
  run_value_of entry [] TreeCacheExamples.appendStepRun TreeCacheExamples.listStep
    single_step_value t

theorem right_value (entry : Nat) (t : BinaryTree α) :
    (run entry [] rightStepRun t).1 = Trees.inorder t :=
  run_value_of entry [] rightStepRun TreeCacheExamples.listStep right_step_value t

theorem left_value (entry : Nat) (t : BinaryTree α) :
    (run entry [] leftStepRun t).1 = Trees.inorder t :=
  run_value_of entry [] leftStepRun TreeCacheExamples.listStep left_step_value t

/-- The length is that of the actual returned left list, via the value bridge. -/
theorem single_node_cost (entry : Nat) (a : α) (l r : BinaryTree α) :
    (run entry [] TreeCacheExamples.appendStepRun (.node a l r)).2 =
      ((run entry [] TreeCacheExamples.appendStepRun l).2 +
        ((run entry [] TreeCacheExamples.appendStepRun r).2 + (l.numNodes + 1))) +
          entry := by
  rw [run_node_cost, single_step_cost, single_value, Trees.inorder_length]

theorem right_node_cost (entry : Nat) (a : α) (l r : BinaryTree α) :
    (run entry [] rightStepRun (.node a l r)).2 =
      ((run entry [] rightStepRun l).2 +
        ((run entry [] rightStepRun r).2 + (l.numNodes + 3))) + entry := by
  rw [run_node_cost, right_step_cost, right_value, Trees.inorder_length]

theorem left_node_cost (entry : Nat) (a : α) (l r : BinaryTree α) :
    (run entry [] leftStepRun (.node a l r)).2 =
      ((run entry [] leftStepRun l).2 +
        ((run entry [] leftStepRun r).2 + (2 * l.numNodes + 3))) + entry := by
  rw [run_node_cost, left_step_cost, left_value, Trees.inorder_length]

theorem nil_work :
    (run 1 [] TreeCacheExamples.appendStepRun (.nil : BinaryTree α)).2 = 1 ∧
      (run 1 [] rightStepRun (.nil : BinaryTree α)).2 = 1 ∧
      (run 1 [] leftStepRun (.nil : BinaryTree α)).2 = 1 := by
  simp only [Resources.TreeFold.run_nil, and_self]

theorem singleton_work (a : α) :
    (run 1 [] TreeCacheExamples.appendStepRun (.node a .nil .nil)).2 = 4 ∧
      (run 1 [] rightStepRun (.node a .nil .nil)).2 = 6 ∧
      (run 1 [] leftStepRun (.node a .nil .nil)).2 = 6 := by
  simp only [single_node_cost, right_node_cost, left_node_cost, Resources.TreeFold.run_nil,
    BinaryTree.numNodes, and_self]

theorem single_sample :
    run 1 [] TreeCacheExamples.appendStepRun TreeCacheExamples.sample =
      ([0, 1, 2, 3], 15) := by
  apply Prod.ext
  · rw [single_value, TreeCacheExamples.sample_inorder]
  · simp only [TreeCacheExamples.sample, single_node_cost, Resources.TreeFold.run_nil, BinaryTree.numNodes]

theorem right_sample :
    run 1 [] rightStepRun TreeCacheExamples.sample = ([0, 1, 2, 3], 23) := by
  apply Prod.ext
  · rw [right_value, TreeCacheExamples.sample_inorder]
  · simp only [TreeCacheExamples.sample, right_node_cost, Resources.TreeFold.run_nil, BinaryTree.numNodes]

theorem left_sample :
    run 1 [] leftStepRun TreeCacheExamples.sample = ([0, 1, 2, 3], 25) := by
  apply Prod.ext
  · rw [left_value, TreeCacheExamples.sample_inorder]
  · simp only [TreeCacheExamples.sample, left_node_cost, Resources.TreeFold.run_nil, BinaryTree.numNodes]

/-- Equal returned lists do not identify the costs of these actual executions. -/
theorem same_inorder_different_work :
    (run 1 [] rightStepRun TreeCacheExamples.sample).1 =
        (run 1 [] leftStepRun TreeCacheExamples.sample).1 ∧
      (run 1 [] rightStepRun TreeCacheExamples.sample).2 ≠
        (run 1 [] leftStepRun TreeCacheExamples.sample).2 := by
  rw [right_sample, left_sample]
  decide

end TreeFoldExamples
