import Examples.TreeBalanceCost
import Examples.TreeTraversalWork

/-! Actual inorder-to-balance programs, composed with `Resources.bind`.
The literal frontend executes both right-associated appends. The direct
frontend invokes the available suffix function; the staged frontend also
pays for its construction. Each passes its actual returned list to `balRun`.

For N input nodes, request n ≤ N, and A = `Trees.leftSizeSum t`, the expected
counts are 5*N+2*n+2+A, 2*N+2*n+2, and 4*N+2*n+3. Their erasures agree even
on failure, but value equality is not used to infer any cost equality.
At N=n=0 the counts are 2, 2, and 3. These are the declared source-entry and
append counts, not Lean runtime, allocation, physical sharing or bit costs.
Source and statement assessment: `docs/research/fdsa-tree-balancing.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.TreeBalancePipeline
open Resources Resources.TreeBalance Trees.Balance
universe u
variable {α : Type u}

/-- Literal two-append inorder followed by the actual prefix consumer. -/
def literalRun (n : Nat) (t : BinaryTree α) :
    Measured (Option (BinaryTree α × List α)) Nat :=
  Resources.bind (TreeFold.run 1 [] TreeFoldExamples.rightStepRun t) (balRun n)

/-- Invoke the suffix function at [] and consume its actual returned list. -/
def directRun (n : Nat) (t : BinaryTree α) :
    Measured (Option (BinaryTree α × List α)) Nat :=
  Resources.bind (TreeAccumulator.invoke 1 t []) (balRun n)

/-- Construct once, invoke once, and then consume the actual returned list. -/
def stagedRun (n : Nat) (t : BinaryTree α) :
    Measured (Option (BinaryTree α × List α)) Nat :=
  Resources.bind (TreeAccumulatorExamples.buildOnce 1 1 t []) (balRun n)

theorem literal_value (n : Nat) (t : BinaryTree α) :
    (literalRun n t).1 = bal n (Trees.inorder t) := by
  rw [literalRun, bind_value, TreeFoldExamples.right_value, balRun_value]

theorem direct_value (n : Nat) (t : BinaryTree α) :
    (directRun n t).1 = bal n (Trees.inorder t) := by
  rw [directRun, bind_value, TreeAccumulator.invoke_value, List.append_nil, balRun_value]

theorem staged_value (n : Nat) (t : BinaryTree α) :
    (stagedRun n t).1 = bal n (Trees.inorder t) := by
  rw [stagedRun, bind_value, TreeAccumulatorExamples.buildOnce_exact, List.append_nil,
    balRun_value]

/-- All requests, including failures, have the same returned result. -/
theorem same_result (n : Nat) (t : BinaryTree α) :
    (literalRun n t).1 = (directRun n t).1 ∧
      (directRun n t).1 = (stagedRun n t).1 := by
  exact ⟨(literal_value n t).trans (direct_value n t).symm,
    (direct_value n t).trans (staged_value n t).symm⟩

/-- The consumer's exact failure domain survives each actual frontend. -/
theorem failure_iff (n : Nat) (t : BinaryTree α) :
    ((literalRun n t).1 = none ↔ t.numNodes < n) ∧
      ((directRun n t).1 = none ↔ t.numNodes < n) ∧
      ((stagedRun n t).1 = none ↔ t.numNodes < n) := by
  simp only [literal_value, direct_value, staged_value, bal_eq_none_iff, Trees.inorder_length]
  exact ⟨trivial, trivial, trivial⟩

theorem literal_cost {n : Nat} (t : BinaryTree α) (h : n ≤ t.numNodes) :
    (literalRun n t).2 = 5 * t.numNodes + 2 * n + 2 + Trees.leftSizeSum t := by
  have hd : n ≤ (Trees.inorder t).length := by simpa only [Trees.inorder_length] using h
  simp only [literalRun, Resources.bind, TreeFoldExamples.right_value,
    TreeTraversalWorkExamples.right_cost, balRun_cost hd]
  ring

theorem direct_cost {n : Nat} (t : BinaryTree α) (h : n ≤ t.numNodes) :
    (directRun n t).2 = 2 * t.numNodes + 2 * n + 2 := by
  have hd : n ≤ (Trees.inorder t).length := by simpa only [Trees.inorder_length] using h
  simp only [directRun, Resources.bind, TreeAccumulator.invoke_exact,
    List.append_nil, balRun_cost hd]
  ring

theorem staged_cost {n : Nat} (t : BinaryTree α) (h : n ≤ t.numNodes) :
    (stagedRun n t).2 = 4 * t.numNodes + 2 * n + 3 := by
  have hd : n ≤ (Trees.inorder t).length := by simpa only [Trees.inorder_length] using h
  simp only [stagedRun, Resources.bind, TreeAccumulatorExamples.buildOnce_exact,
    List.append_nil, balRun_cost hd]
  ring

private theorem inorder_request_result {n : Nat} (t : BinaryTree α)
    (h : n ≤ t.numNodes) :
    bal n (Trees.inorder t) = some (balTree n t, (Trees.inorder t).drop n) := by
  obtain ⟨b, zs, hb⟩ := bal_exists (n := n) (xs := Trees.inorder t)
    (by simpa only [Trees.inorder_length] using h)
  have ht : balTree n t = b := balList_of_some hb
  rw [ht, ← bal_suffix hb]
  exact hb

/-- Sufficient input gives the actual retained suffix and the independent cost. -/
theorem literal_exact {n : Nat} (t : BinaryTree α) (h : n ≤ t.numNodes) :
    literalRun n t =
      (some (balTree n t, (Trees.inorder t).drop n),
        5 * t.numNodes + 2 * n + 2 + Trees.leftSizeSum t) := by
  apply Prod.ext
  · exact (literal_value n t).trans (inorder_request_result t h)
  · exact literal_cost t h

theorem direct_exact {n : Nat} (t : BinaryTree α) (h : n ≤ t.numNodes) :
    directRun n t =
      (some (balTree n t, (Trees.inorder t).drop n), 2 * t.numNodes + 2 * n + 2) := by
  apply Prod.ext
  · exact (direct_value n t).trans (inorder_request_result t h)
  · exact direct_cost t h

theorem staged_exact {n : Nat} (t : BinaryTree α) (h : n ≤ t.numNodes) :
    stagedRun n t =
      (some (balTree n t, (Trees.inorder t).drop n), 4 * t.numNodes + 2 * n + 3) := by
  apply Prod.ext
  · exact (staged_value n t).trans (inorder_request_result t h)
  · exact staged_cost t h

theorem literal_full (t : BinaryTree α) :
    literalRun t.numNodes t =
      (some (balanceTree t, []), 7 * t.numNodes + 2 + Trees.leftSizeSum t) := by
  rw [literal_exact t (Nat.le_refl _), ← balanceTree]
  have hs : (Trees.inorder t).drop t.numNodes = [] := by
    rw [← Trees.inorder_length t, List.drop_length]
  rw [hs]
  congr 2
  ring

theorem direct_full (t : BinaryTree α) :
    directRun t.numNodes t = (some (balanceTree t, []), 4 * t.numNodes + 2) := by
  rw [direct_exact t (Nat.le_refl _), ← balanceTree]
  have hs : (Trees.inorder t).drop t.numNodes = [] := by
    rw [← Trees.inorder_length t, List.drop_length]
  rw [hs]
  congr 2
  ring

theorem staged_full (t : BinaryTree α) :
    stagedRun t.numNodes t = (some (balanceTree t, []), 6 * t.numNodes + 3) := by
  rw [staged_exact t (Nat.le_refl _), ← balanceTree]
  have hs : (Trees.inorder t).drop t.numNodes = [] := by
    rw [← Trees.inorder_length t, List.drop_length]
  rw [hs]
  congr 2
  ring

/-- The full direct invocation has a linear bound for positive-size inputs. -/
theorem direct_full_linear (t : BinaryTree α) (h : 0 < t.numNodes) :
    (directRun t.numNodes t).2 ≤ 6 * t.numNodes := by
  rw [direct_full]
  omega

/-- Construction costs 2*N+1 in addition to the same direct invocation. -/
theorem staged_eq_direct_add {n : Nat} (t : BinaryTree α) (h : n ≤ t.numNodes) :
    (stagedRun n t).2 = (directRun n t).2 + (2 * t.numNodes + 1) := by
  rw [staged_cost t h, direct_cost t h]
  ring

/-- A subtraction-free comparison retains the extra staged nil entry. -/
theorem literal_add_one_eq_staged_add {n : Nat} (t : BinaryTree α)
    (h : n ≤ t.numNodes) :
    (literalRun n t).2 + 1 =
      (stagedRun n t).2 + (t.numNodes + Trees.leftSizeSum t) := by
  rw [literal_cost t h, staged_cost t h]
  ring

/-- Staging is no dearer than literal append on nonempty inputs only. -/
theorem staged_le_literal {n : Nat} (t : BinaryTree α) (h : n ≤ t.numNodes)
    (hn : 0 < t.numNodes) : (stagedRun n t).2 ≤ (literalRun n t).2 := by
  have hc := literal_add_one_eq_staged_add t h
  omega

/-- Nil still executes both frontend and consumer entries; staging adds one. -/
theorem nil_executions :
    literalRun 0 (.nil : BinaryTree α) = (some (.nil, []), 2) ∧
      directRun 0 (.nil : BinaryTree α) = (some (.nil, []), 2) ∧
      stagedRun 0 (.nil : BinaryTree α) = (some (.nil, []), 3) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [BinaryTree.numNodes, Trees.leftSizeSum_nil, balanceTree, balTree,
      balList, Trees.inorder_nil] using literal_full (.nil : BinaryTree α)
  · simpa [BinaryTree.numNodes, balanceTree, balTree, balList, Trees.inorder_nil]
      using direct_full (.nil : BinaryTree α)
  · simpa [BinaryTree.numNodes, balanceTree, balTree, balList, Trees.inorder_nil]
      using staged_full (.nil : BinaryTree α)

theorem nil_not_linear (K : Nat) :
    ¬ (directRun 0 (.nil : BinaryTree α)).2 ≤ K * (.nil : BinaryTree α).numNodes := by
  rw [nil_executions.2.1]
  simp only [BinaryTree.numNodes, Nat.mul_zero]
  decide

theorem nil_staged_not_le_literal :
    ¬ (stagedRun 0 (.nil : BinaryTree α)).2 ≤ (literalRun 0 (.nil : BinaryTree α)).2 := by
  rw [nil_executions.1, nil_executions.2.2]
  change ¬ (3 : Nat) ≤ 2
  decide

/-- Actual failed runs retain costs, without applying a successful-input law. -/
theorem failed_nil_executions :
    literalRun 1 (.nil : BinaryTree Nat) = (none, 3) ∧
      directRun 1 (.nil : BinaryTree Nat) = (none, 3) ∧
      stagedRun 1 (.nil : BinaryTree Nat) = (none, 4) := by
  simp only [literalRun, directRun, stagedRun, TreeFold.run_nil,
    TreeAccumulator.invoke_nil, TreeAccumulatorExamples.buildOnce_exact,
    Trees.inorder_nil, List.nil_append, BinaryTree.numNodes, Resources.bind,
    TreeBalanceCost.failed_one_execution]
  decide

/-- The four-node asymmetric input gives independently predicted 32/18/27. -/
theorem sample_executions :
    literalRun 4 TreeCacheExamples.sample =
        (some (balanceTree TreeCacheExamples.sample, []), 32) ∧
      directRun 4 TreeCacheExamples.sample =
        (some (balanceTree TreeCacheExamples.sample, []), 18) ∧
      stagedRun 4 TreeCacheExamples.sample =
        (some (balanceTree TreeCacheExamples.sample, []), 27) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [TreeCacheExamples.sample_size, TreeTraversalWorkExamples.sample_leftSizeSum]
      using literal_full TreeCacheExamples.sample
  · simpa only [TreeCacheExamples.sample_size] using direct_full TreeCacheExamples.sample
  · simpa only [TreeCacheExamples.sample_size] using staged_full TreeCacheExamples.sample

theorem sample_same_results_distinct_costs :
    (literalRun 4 TreeCacheExamples.sample).1 = (directRun 4 TreeCacheExamples.sample).1 ∧
      (directRun 4 TreeCacheExamples.sample).1 = (stagedRun 4 TreeCacheExamples.sample).1 ∧
      (directRun 4 TreeCacheExamples.sample).2 < (stagedRun 4 TreeCacheExamples.sample).2 ∧
      (stagedRun 4 TreeCacheExamples.sample).2 < (literalRun 4 TreeCacheExamples.sample).2 := by
  rw [sample_executions.1, sample_executions.2.1, sample_executions.2.2]
  exact ⟨rfl, rfl, by decide, by decide⟩

/-- A proper prefix leaves [3] untouched in each actual execution. -/
theorem sample_prefix_executions :
    literalRun 3 TreeCacheExamples.sample =
        (some (.node 1 (.node 0 .nil .nil) (.node 2 .nil .nil), [3]), 30) ∧
      directRun 3 TreeCacheExamples.sample =
        (some (.node 1 (.node 0 .nil .nil) (.node 2 .nil .nil), [3]), 16) ∧
      stagedRun 3 TreeCacheExamples.sample =
        (some (.node 1 (.node 0 .nil .nil) (.node 2 .nil .nil), [3]), 25) := by
  have h : 3 ≤ TreeCacheExamples.sample.numNodes := by
    rw [TreeCacheExamples.sample_size]
    decide
  have hb : bal 3 [0, 1, 2, 3] =
      some (.node 1 (.node 0 .nil .nil) (.node 2 .nil .nil), [3]) := by
    norm_num [bal_succ, bal_zero]
  have ht : balTree 3 TreeCacheExamples.sample =
      .node 1 (.node 0 .nil .nil) (.node 2 .nil .nil) := by
    unfold balTree
    rw [TreeCacheExamples.sample_inorder]
    exact balList_of_some hb
  rw [literal_exact _ h, direct_exact _ h, staged_exact _ h, ht,
    TreeCacheExamples.sample_inorder, TreeCacheExamples.sample_size,
    TreeTraversalWorkExamples.sample_leftSizeSum]
  decide

/-- Equal repeated-label inorder sequences yield equal balancing results. -/
theorem chain_results (a : α) (n : Nat) :
    (literalRun n (Trees.leftChain a n)).1 = (literalRun n (Trees.rightChain a n)).1 ∧
      (literalRun n (Trees.leftChain a n)).1 = (directRun n (Trees.leftChain a n)).1 ∧
      (directRun n (Trees.leftChain a n)).1 = (stagedRun n (Trees.leftChain a n)).1 := by
  refine ⟨?_, (same_result n _).1, (same_result n _).2⟩
  rw [literal_value, literal_value, Trees.inorder_leftChain, Trees.inorder_rightChain]

/-- Three-node left/right chains share results but retain their 26/23 literal costs. -/
theorem chain_costs (a : α) :
    (literalRun 3 (Trees.leftChain a 3)).2 = 26 ∧
      (literalRun 3 (Trees.rightChain a 3)).2 = 23 ∧
      (directRun 3 (Trees.leftChain a 3)).2 = 14 ∧
      (stagedRun 3 (Trees.leftChain a 3)).2 = 21 := by
  have hl : 3 ≤ (Trees.leftChain a 3).numNodes := by rw [Trees.leftChain_numNodes]
  have hr : 3 ≤ (Trees.rightChain a 3).numNodes := by rw [Trees.rightChain_numNodes]
  rw [literal_cost _ hl, literal_cost _ hr, direct_cost _ hl, staged_cost _ hl,
    Trees.leftChain_numNodes, Trees.rightChain_numNodes,
    Trees.leftSizeSum_leftChain, Trees.leftSizeSum_rightChain]
  norm_num

theorem chain_same_result_different_cost (a : α) :
    (literalRun 3 (Trees.leftChain a 3)).1 = (literalRun 3 (Trees.rightChain a 3)).1 ∧
      (literalRun 3 (Trees.leftChain a 3)).2 ≠ (literalRun 3 (Trees.rightChain a 3)).2 := by
  constructor
  · exact (chain_results a 3).1
  · rw [(chain_costs a).1, (chain_costs a).2.1]
    decide

/-- An empty label domain needs neither an inhabitant nor an equality decision. -/
theorem empty_payload (t : BinaryTree Empty) :
    literalRun 0 t = (some (.nil, []), 2) ∧
      directRun 0 t = (some (.nil, []), 2) ∧
      stagedRun 0 t = (some (.nil, []), 3) := by
  rw [TreeCacheExamples.empty_tree t]
  exact nil_executions

end Examples.TreeBalancePipeline
