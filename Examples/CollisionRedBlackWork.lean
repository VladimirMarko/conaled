import Applications.Resources.CollisionRedBlack

/-! Connected finite-set and priced-operation cases for collision tables. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.CollisionRedBlackWork

open Resources Resources.CollisionRedBlack
open Search.RedBlack (Tree)

private def oneBinding : Tree Nat Bool := .node .black .nil (5, true) .nil

private theorem oneBinding_bst : Search.RedBlack.BST (fun n : Nat => (n : Int)) oneBinding := by
  simp [oneBinding, Search.RedBlack.bst_node_iff]

private theorem oneBinding_shape : Search.RedBlack.RB oneBinding .red 1 :=
  Search.RedBlack.RB.black .red 5 true
    (Search.RedBlack.RB.nil .black) (Search.RedBlack.RB.nil .black)

/-- A distinct-key set, not the number of lookups, bounds this valid tree. -/
theorem one_distinct_key : oneBinding.size ≤ ({5} : Finset Nat).card := by
  apply size_le_card (fun n : Nat => (n : Int)) {5} oneBinding oneBinding_bst
  simp [oneBinding]

theorem one_distinct_key_height : Search.RedBlack.height oneBinding ≤ 2 := by
  have bound := height_le_card_log (fun n : Nat => (n : Int)) {5} oneBinding oneBinding_bst
    (by simp [oneBinding]) oneBinding_shape
  simpa using bound

/-- At zero stored keys, lookup, leaf insertion and final blackening remain. -/
theorem empty_table_tariff (K : Nat) : tableTariff (fun _ => 1) K 0 = 5 := by
  rw [tableTariff_unit]
  simp

/-- Calibration uses a declared unit comparator only for this concrete case;
the general bound retains the comparator's measured work parameter. -/
theorem empty_actual_operations :
    RedBlack.weighted (fun _ => 1)
        (RedBlack.lookupRun (RedBlack.unitComparator (fun a b : Nat => decide (a < b)))
          5 (.nil : Tree Nat Bool)).2 +
      RedBlack.weighted (fun _ => 1)
        (RedBlack.insertRun (RedBlack.unitComparator (fun a b : Nat => decide (a < b)))
          5 true (.nil : Tree Nat Bool)).2 = 5 := by
  rw [RedBlack.weighted_eq, RedBlack.weighted_eq, RedBlack.lookupRun_nil,
    RedBlack.insertRun_cost, RedBlack.insRun_nil]
  rfl

/-- Empty input still has the final client observation. -/
theorem empty_signed_work : totalWork (fun _ => 1) (signedCollisions []).2 = 1 := by
  rfl

/-- One fresh key performs empty lookup and insertion, with no increment. -/
theorem singleton_signed_components :
    tableWork (fun _ => 1) (signedCollisions [5]).2 = 5 ∧
      counterWork (signedCollisions [5]).2 = 0 ∧
      overhead (signedCollisions [5]).2 = 2 := by
  exact ⟨rfl, rfl, rfl⟩

theorem singleton_signed_total : totalWork (fun _ => 1) (signedCollisions [5]).2 = 7 := by
  obtain ⟨table, counter, dispatch⟩ := singleton_signed_components
  simp only [totalWork, table, counter, dispatch]

/-- For key5 the three magnitude bits make each same-key Boolean comparison
cost5 including sign and selection. Two repeated lookups each call it twice. -/
theorem three_equal_signed_components :
    tableWork (fun _ => 1) (signedCollisions [5, 5, 5]).2 = 31 ∧
      counterWork (signedCollisions [5, 5, 5]).2 = 3 ∧
      overhead (signedCollisions [5, 5, 5]).2 = 6 := by
  exact ⟨rfl, rfl, rfl⟩

theorem three_equal_signed_total : totalWork (fun _ => 1) (signedCollisions [5, 5, 5]).2 = 40 := by
  obtain ⟨table, counter, dispatch⟩ := three_equal_signed_components
  simp only [totalWork, table, counter, dispatch]

theorem three_equal_signed_count : ((signedCollisions [5, 5, 5]).1.1 : Nat) = 2 := by
  rw [signedCollisions_correct]
  decide

theorem source_pi_count :
    ((signedCollisions [3, 1, 4, 1, 5, 9, 2, 6]).1.1 : Nat) = 1 := by
  rw [signedCollisions_correct]
  decide

theorem negative_key_count : ((signedCollisions [-7, 0, -7, 5, 0]).1.1 : Nat) = 2 := by
  rw [signedCollisions_correct]
  decide

/-- This infinite family repeats one key; D stays1 and B stays3 while n grows. -/
theorem repeated_five_bound (n : Nat) :
    totalWork (fun _ => 1) (signedCollisions (List.replicate n 5)).2 ≤
      90 * (n + 1) * 4 * (1 + ((List.replicate n (5 : ZNum)).toFinset.card + 1).log2) := by
  have bound := signedCollisions_totalWork_majorant (List.replicate n 5) 3 (by
    intro key member
    have eqKey := (List.mem_replicate.mp member).2
    subst key
    decide)
  simpa only [List.length_replicate] using bound

end Examples.CollisionRedBlackWork
