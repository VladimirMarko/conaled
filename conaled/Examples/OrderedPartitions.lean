import Applications.OrderedPartitions.Enumeration

/-! Concrete ordered partitions distinguish occurrence preservation from sets. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.OrderedPartitions
open _root_.OrderedPartitions

/-- Empty input has one partition, containing no blocks. -/
theorem empty : partsLeft ([] : List Nat) = [[]] ∧ IsPartition [] ([] : Partition Nat) :=
  ⟨partsLeft_nil, (partition_nil_iff []).mpr rfl⟩

/-- A nonempty block may repeat values; the generator does not repeat partitions. -/
theorem repeated : (partsLeft ([1, 1, 1] : List Nat)).length = 4 ∧
    (partsLeft ([1, 1, 1] : List Nat)).Nodup :=
  ⟨length_partsLeft_cons 1 [1, 1], partsLeft_nodup _⟩

theorem exact_order : partsLeft ([1, 2, 3] : List Nat) =
    [[[1], [2], [3]], [[1, 2], [3]], [[1], [2, 3]], [[1, 2, 3]]] := rfl

theorem complete_member : IsPartition ([1, 2, 3] : List Nat) [[1, 2], [3]] := by
  apply (mem_partsLeft _ _).mp
  rw [exact_order]
  simp

theorem no_empty_blocks : ¬ IsPartition ([1] : List Nat) [[], [1]] := by
  intro h
  exact h.2 [] (by simp) rfl

/-- Length caps are suffix closed, so the early pruning keeps exact order. -/
theorem bounded_pruning : prunedPartsLeft (fun xs : List Nat => decide (xs.length ≤ 2))
    [1, 2, 3] = [[[1], [2], [3]], [[1, 2], [3]], [[1], [2, 3]]] := by
  have closed : SuffixClosed (fun xs : List Nat => decide (xs.length ≤ 2)) := by
    intro xs ys h
    simp only [decide_eq_true_eq, List.length_append] at h ⊢
    omega
  rw [← filter_partsLeft _ closed, exact_order]
  decide

/-- Even-length blocks are not suffix closed: filtering at the end can recover
an admissible pair that early pruning discarded with its singleton suffix. -/
theorem closure_boundary :
    (partsLeft ([1, 2] : List Nat)).filter
      (allOk (fun xs => decide (xs.length % 2 = 0))) = [[[1, 2]]] ∧
    prunedPartsLeft (fun xs : List Nat => decide (xs.length % 2 = 0)) [1, 2] = [] := by
  decide

/-- The two middle candidates trade places between the generators. -/
theorem right_order : partsRight ([1, 2, 3] : List Nat) =
    [[[1], [2], [3]], [[1], [2, 3]], [[1, 2], [3]], [[1, 2, 3]]] := rfl

theorem enumeration_permutation : (partsRight ([1, 2, 3] : List Nat)).Perm
    (partsLeft [1, 2, 3]) := partsRight_perm_left _

theorem enumeration_not_equal : partsRight ([1, 2, 3] : List Nat) ≠ partsLeft [1, 2, 3] := by
  rw [right_order, exact_order]
  decide

theorem right_bounded_pruning : prunedPartsRight
    (fun xs : List Nat => decide (xs.length ≤ 2)) [1, 2, 3] =
      [[[1], [2], [3]], [[1], [2, 3]], [[1, 2], [3]]] := by
  have closed : PrefixClosed (fun xs : List Nat => decide (xs.length ≤ 2)) := by
    intro xs ys h
    simp only [decide_eq_true_eq, List.length_append] at h ⊢
    omega
  rw [← filter_partsRight _ closed, right_order]
  decide

theorem recursive_order : partsRecursive ([1, 2, 3] : List Nat) =
    [[[1], [2], [3]], [[1], [2, 3]], [[1, 2], [3]], [[1, 2, 3]]] := by
  rw [partsRecursive_eq_right, right_order]

theorem grouped_order : partsGrouped ([1, 2, 3] : List Nat) =
    [[[1], [2], [3]], [[1], [2, 3]], [[1, 2], [3]], [[1, 2, 3]]] := by
  rw [partsGrouped_eq_right, right_order]

/-- The right generator likewise needs prefix closure, not an arbitrary filter. -/
theorem right_closure_boundary :
    (partsRight ([1, 2] : List Nat)).filter
      (allOk (fun xs => decide (xs.length % 2 = 0))) = [[[1, 2]]] ∧
    prunedPartsRight (fun xs : List Nat => decide (xs.length % 2 = 0)) [1, 2] = [] := by
  decide

end Examples.OrderedPartitions
