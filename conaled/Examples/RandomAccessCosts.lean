import Applications.Resources.RandomAccess.Observation

/-! Independent sequence results and exact counted branches through public laws. -/
namespace Examples.RandomAccessCosts
open RandomAccess Resources Resources.RandomAccessCosts

example : fetchListRun 0 ([] : List Nat) = (none,1) := rfl
example : fetchRARun 0 ([] : RAList Nat) = (none,1) := rfl
example : (fetchListRun 2 [1,2,3]).2 = 3 := fetchListRun_count _ _ (by decide)
example : (fetchListRun 5 [1,2,3]).1 = none := fetchListRun_value _ _
example : fetchTRun 0 (.leaf 7) = (some 7,1) := rfl
example : (fetchTRun 8 (.leaf 7)).2 = 1 := fetchTRun_count (Perfect.leaf 7) _
example : (fetchTRun 8 (.leaf 7)).1 = none := fetchTRun_value _ _

private def four := node (node (.leaf 1) (.leaf 2)) (node (.leaf 3) (.leaf 4))
private theorem four_perfect : Perfect 2 four :=
  perfect_node (perfect_node (Perfect.leaf 1) (Perfect.leaf 2))
    (perfect_node (Perfect.leaf 3) (Perfect.leaf 4))
example : (fetchTRun 0 four).1 = some 1 ∧ (fetchTRun 3 four).1 = some 4 := by
  rw [fetchTRun_value, fetchT_refinement four_perfect,
    fetchTRun_value, fetchT_refinement four_perfect]
  decide
example : (fetchTRun 3 four).2 = 3 := fetchTRun_count four_perfect _
example : (updateTRun 3 9 four).2 = 3 :=
  (updateTRun_count _ _ _).trans (fetchTRun_count four_perfect _)

-- Raw erasure does not manufacture valid caches or a no-trailing-zero invariant.
example : (fetchTRun 0 (.node 0 (.leaf 1) (.leaf 2))).1 = some 2 := fetchTRun_value _ _
example : (fetchTRun 0 (.node 0 (.leaf 1) (.leaf 2))).1 ≠
    (fromT (.node 0 (.leaf 1) (.leaf 2)))[0]? := by decide
example : ¬ Inv ([.zero] : RAList Nat) := by
  intro h
  cases h with
  | zero hne _ => exact hne rfl
example : (fetchRARun 0 ([.zero,.zero,.zero,.zero] : RAList Nat)).2 >
    2 * (fromRA ([.zero,.zero,.zero,.zero] : RAList Nat)).length.log2 + 3 := by decide

private def edits : List (Nat × Nat) := [(1,7),(2,3),(3,4),(2,8)]
example : fromRA (bulkRun (toRA [0,1,2,3]) edits).1 = [0,7,8,4] := by
  rw [bulkRun_value, bulk_refinement (inv_toRA _), fromRA_toRA]; rfl
example : bulkRun (toRA [0,1,2,3]) ([(1,7),(2,3)] ++ [(3,4),(2,8)]) =
    bind (bulkRun (toRA [0,1,2,3]) [(1,7),(2,3)])
      (fun ds => bulkRun ds [(3,4),(2,8)]) := bulkRun_append _ _ _
example : bulkRun (toRA [0,1,2,3]) [] = (toRA [0,1,2,3],0) := bulkRun_nil _
example : Inv (bulk (toRA [0,1,2,3]) edits) := bulk_valid (inv_toRA _) _
example : (updateRARun 99 7 (toRA [0,1,2,3])).2 = (fetchRARun 99 (toRA [0,1,2,3])).2 :=
  updateRARun_count _ _ _
example : fromRA (updateRARun 99 7 (toRA [0,1,2,3])).1 = [0,1,2,3] := by
  rw [updateRARun_refinement (inv_toRA _), fromRA_toRA]; rfl

example : ((measuredUpdateQuery 1 7 1).impl (encode [0,1,2,3])).1 = some 7 := by
  rw [measuredUpdateQuery_value]; rfl
example : ((measuredUpdateQuery 1 7 2).impl (encode [0,1,2,3])).1 = some 2 := by
  rw [measuredUpdateQuery_value]; rfl
example : ((measuredUpdateQuery 99 7 99).impl (encode [0,1,2,3])).1 = none := by
  rw [measuredUpdateQuery_value]; rfl
example : ((measuredUpdateQuery 99 7 99).impl (encode [0,1,2,3])).2 = 8 := by
  rw [measuredUpdateQuery_cost]; rfl
example : ((measuredUpdateQuery 1 7 1).impl (encode [0,1,2,3])).2 ≤ 14 :=
  measuredUpdateQuery_bound _ _ _ _
example : ((observedBulk edits).impl (encode [0,1,2,3])).1 = [0,7,8,4] := by
  rw [observedBulk_value]; rfl
example : ((observedBulk edits).impl (encode [0,1,2,3])).2 =
    (bulkRun (toRA [0,1,2,3]) edits).2 := observedBulk_cost _ _
example : ((observedBulk edits).impl (encode [0,1,2,3])).2 ≤ 32 := observedBulk_bound _ _

private def sparseFour : RAList Nat := sparse 4 (perfectTree 7 4)
private theorem sparseFour_valid : Inv sparseFour := sparse_valid 0 4 (perfectTree_valid 7 4)
example : (fetchRARun 0 sparseFour).1 = some 7 := by
  rw [fetchRARun_refinement sparseFour_valid]
  simp [sparseFour, sparse_value, perfectTree_values]
example : (fetchRARun 0 sparseFour).2 = 10 := sparse_fetch_cost _ (perfectTree_valid _ _)
example : (fetchRARun 9 sparseFour).2 = 10 :=
  sparse_fetch_cost_at _ (perfectTree_valid _ _) _ (by decide)
example : (bulkRun sparseFour [(0,8),(0,9)]).2 = 22 :=
  bulk_sparse_zero_cost 4 (perfectTree_valid 7 4) [8,9]
example (k B : Nat) : ∃ ds : RAList Nat, Inv ds ∧
    (fetchRARun k ds).1 = some 7 ∧ B < (fetchRARun k ds).2 := no_index_only_bound 7 k B
example (bound : Nat → Nat) (K : Nat) : ∃ (k : Nat) (ds : RAList Nat),
    K ≤ k ∧ Inv ds ∧ (fetchRARun k ds).1 = some 7 ∧ bound k < (fetchRARun k ds).2 :=
  no_eventual_index_function_bound 7 bound K

example : (bulkRun (.one (.leaf 0) :: sparse 5 (perfectTree 7 6)) [(0,8),(0,9)]).2 = 6 :=
  bulk_head_zero_cost _ _ [8,9]
example : Inv (.one (.leaf 0) :: sparse 5 (perfectTree 7 6)) :=
  Valid.one (Perfect.leaf 0) (sparse_valid 1 5 (perfectTree_valid 7 6))
example (C : Nat) : ∃ ds : RAList Nat, Inv ds ∧ (bulkRun ds [(0,7)]).2 = 3 ∧
    C * (bulkRun ds [(0,7)]).2 < (fromRA ds).length.log2 := no_all_inputs_log_lower 7 C
example : (bulkRun (toRA [0,1,2,3]) [(3,8),(3,9)]).2 = 14 := by
  have h := bulk_last_log_exact (inv_toRA [0,1,2,3]) (by decide) [8,9]
  have hlog : (4 : Nat).log2 = 2 := by decide
  simpa [fromRA_toRA, hlog] using h
example : (bulkRun sparseFour []).2 = 0 * (2 * (fromRA sparseFour).length.log2 + 3) :=
  bulk_last_log_exact sparseFour_valid (by decide) []

private def doubleCost : Nat →+ Nat where
  toFun := (2 * ·)
  map_zero' := rfl
  map_add' := Nat.mul_add 2
example : reweight doubleCost (bulkRun sparseFour [(0,8),(0,9)]) =
    run (fun p ds => reweight doubleCost (bulkStep p ds)) [(0,8),(0,9)] sparseFour :=
  bulkRun_reweight _ _ _
example : (reweight doubleCost (bulkRun sparseFour [(0,8),(0,9)])).2 = 44 := by
  change 2 * (bulkRun sparseFour [(0,8),(0,9)]).2 = 44
  rw [show (bulkRun sparseFour [(0,8),(0,9)]).2 = 22 from
    bulk_sparse_zero_cost 4 (perfectTree_valid 7 4) [8,9]]

end Examples.RandomAccessCosts
