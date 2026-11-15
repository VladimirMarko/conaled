import Applications.Trees.BalanceShape
import Applications.Trees.ShapeLog
import Examples.TreeBalance

/-! Source logarithm forms and connected boundaries of the consuming balancer.
The real-log statements reuse ShapeLog after almost completeness is proved.
Numerical cases consume the public discrete formulas, including nil, counts
around powers of two, an untouched suffix and the complete source figure.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.TreeBalanceShape
open Trees Trees.Balance Examples.TreeBalance
universe u v
variable {α : Type u} {β : Type v}

theorem bal_source_heights {n : Nat} {xs zs : List α} {t : BinaryTree α}
    (h : bal n xs = some (t, zs)) :
    t.height = ⌈Real.logb 2 ((n + 1 : Nat) : Real)⌉₊ ∧
      minHeight t = ⌊Real.logb 2 ((n + 1 : Nat) : Real)⌋₊ := by
  constructor
  · simpa only [BinaryTree.numLeaves_eq_numNodes_succ, (bal_spec h).2] using
      height_eq_ceil_logb_numLeaves t (bal_almostComplete h)
  · simpa only [BinaryTree.numLeaves_eq_numNodes_succ, (bal_spec h).2] using
      minHeight_eq_floor_logb_numLeaves t (bal_almostComplete h)

theorem balList_source_heights {n : Nat} {xs : List α} (h : n ≤ xs.length) :
    (balList n xs).height = ⌈Real.logb 2 ((n + 1 : Nat) : Real)⌉₊ ∧
      minHeight (balList n xs) = ⌊Real.logb 2 ((n + 1 : Nat) : Real)⌋₊ := by
  constructor
  · simpa only [BinaryTree.numLeaves_eq_numNodes_succ, numNodes_balList h] using
      height_eq_ceil_logb_numLeaves (balList n xs) (almostComplete_balList n xs)
  · simpa only [BinaryTree.numLeaves_eq_numNodes_succ, numNodes_balList h] using
      minHeight_eq_floor_logb_numLeaves (balList n xs) (almostComplete_balList n xs)

theorem balanceList_source_heights (xs : List α) :
    (balanceList xs).height = ⌈Real.logb 2 ((xs.length + 1 : Nat) : Real)⌉₊ ∧
      minHeight (balanceList xs) = ⌊Real.logb 2 ((xs.length + 1 : Nat) : Real)⌋₊ :=
  balList_source_heights (Nat.le_refl xs.length)

theorem balTree_source_heights {n : Nat} (t : BinaryTree α) (h : n ≤ t.numNodes) :
    (balTree n t).height = ⌈Real.logb 2 ((n + 1 : Nat) : Real)⌉₊ ∧
      minHeight (balTree n t) = ⌊Real.logb 2 ((n + 1 : Nat) : Real)⌋₊ :=
  balList_source_heights (by simpa only [inorder_length] using h)

theorem balanceTree_source_heights (t : BinaryTree α) :
    (balanceTree t).height = ⌈Real.logb 2 ((t.numNodes + 1 : Nat) : Real)⌉₊ ∧
      minHeight (balanceTree t) = ⌊Real.logb 2 ((t.numNodes + 1 : Nat) : Real)⌋₊ :=
  balTree_source_heights t (Nat.le_refl t.numNodes)

/-- Each numerical boundary below instantiates the universal public formulas. -/
theorem count_heights (n : Nat) :
    (balanceList (List.range n)).height = Nat.clog 2 (n + 1) ∧
      minHeight (balanceList (List.range n)) = Nat.log 2 (n + 1) := by
  constructor
  · simpa only [List.length_range] using height_balanceList (List.range n)
  · simpa only [List.length_range] using minHeight_balanceList (List.range n)

theorem count_zero :
    (balanceList (List.range 0)).height = 0 ∧
      minHeight (balanceList (List.range 0)) = 0 :=
  ⟨(count_heights 0).1.trans (by decide), (count_heights 0).2.trans (by decide)⟩

theorem count_one :
    (balanceList (List.range 1)).height = 1 ∧
      minHeight (balanceList (List.range 1)) = 1 :=
  ⟨(count_heights 1).1.trans (by decide), (count_heights 1).2.trans (by decide)⟩

theorem count_two :
    (balanceList (List.range 2)).height = 2 ∧
      minHeight (balanceList (List.range 2)) = 1 :=
  ⟨(count_heights 2).1.trans (by decide), (count_heights 2).2.trans (by decide)⟩

theorem count_three :
    (balanceList (List.range 3)).height = 2 ∧
      minHeight (balanceList (List.range 3)) = 2 :=
  ⟨(count_heights 3).1.trans (by decide), (count_heights 3).2.trans (by decide)⟩

theorem count_four :
    (balanceList (List.range 4)).height = 3 ∧
      minHeight (balanceList (List.range 4)) = 2 :=
  ⟨(count_heights 4).1.trans (by decide), (count_heights 4).2.trans (by decide)⟩

theorem count_seven :
    (balanceList (List.range 7)).height = 3 ∧
      minHeight (balanceList (List.range 7)) = 3 :=
  ⟨(count_heights 7).1.trans (by decide), (count_heights 7).2.trans (by decide)⟩

theorem count_eight :
    (balanceList (List.range 8)).height = 4 ∧
      minHeight (balanceList (List.range 8)) = 3 :=
  ⟨(count_heights 8).1.trans (by decide), (count_heights 8).2.trans (by decide)⟩

/-- The zero-node case has one external leaf, the logarithm's correct argument. -/
theorem zero_external_leaf : (balanceList ([] : List Empty)).numLeaves = 1 := by
  rw [BinaryTree.numLeaves_eq_numNodes_succ, numNodes_balanceList]
  rfl

theorem empty_labels_shapes (n : Nat) (xs : List Empty) :
    AlmostComplete (balList n xs) ∧ minHeight (balList n xs) = 0 ∧
      (balList n xs).height = 0 ∧ (balList n xs).numLeaves = 1 := by
  have ht : balList n xs = .nil := by
    cases h : balList n xs with
    | nil => rfl
    | node a _ _ => exact Empty.elim a
  refine ⟨almostComplete_balList n xs, ?_, ?_, ?_⟩ <;> rw [ht] <;> rfl

/-- Nil fallback preserves shape but cannot preserve a failed requested count. -/
theorem failed_request_heights :
    bal 1 ([] : List Nat) = none ∧ balList 1 ([] : List Nat) = .nil ∧
      AlmostComplete (balList 1 ([] : List Nat)) ∧
      (balList 1 ([] : List Nat)).height ≠ Nat.clog 2 (1 + 1) ∧
      minHeight (balList 1 ([] : List Nat)) ≠ Nat.log 2 (1 + 1) := by
  have hf : bal 1 ([] : List Nat) = none := (bal_eq_none_iff _ _).mpr (by decide)
  have ht := balList_of_none hf
  refine ⟨hf, ht, almostComplete_balList 1 [], ?_, ?_⟩ <;> rw [ht] <;> decide

/-- The shape laws apply to an actual successful prefix and its untouched suffix. -/
theorem prefix_shape_suffix (front tail : List α) :
    ∃ t, bal front.length (front ++ tail) = some (t, tail) ∧
      inorder t = front ∧ AlmostComplete t ∧
      t.height = Nat.clog 2 (front.length + 1) ∧
      minHeight t = Nat.log 2 (front.length + 1) := by
  obtain ⟨t, h, hi, _⟩ := bal_prefix front tail
  exact ⟨t, h, hi, bal_almostComplete h, bal_height h, bal_minHeight h⟩

theorem three_shape_with_suffix :
    bal 3 [9, 3, 7, 8, 8] = some (threeTree, [8, 8]) ∧
      AlmostComplete threeTree ∧ threeTree.height = 2 ∧ minHeight threeTree = 2 :=
  ⟨three_consumption, bal_almostComplete three_consumption,
    (bal_height three_consumption).trans (by decide),
    (bal_minHeight three_consumption).trans (by decide)⟩

/-- The full Figure 4.3 tree has roots 5, 2, 8 and preserves all ten labels. -/
theorem figure_shape_contract :
    AlmostComplete figureTree ∧ inorder figureTree = figureInput ∧
      figureTree.height = 4 ∧ minHeight figureTree = 3 ∧ figureTree.numLeaves = 11 :=
  ⟨bal_almostComplete figure_consumption, figure_order,
    (bal_height figure_consumption).trans (by decide),
    (bal_minHeight figure_consumption).trans (by decide), figure_leaves⟩

/-- Apply the existing optimum law to the actual balanced figure. The
competitor may have any shape and an unrelated payload type. -/
theorem figure_height_optimal (t : BinaryTree β) (h : 10 ≤ t.numNodes) :
    figureTree.height ≤ t.height :=
  height_optimal figureTree t (bal_almostComplete figure_consumption)
    (by simpa only [figure_size] using h)

end Examples.TreeBalanceShape
