import Applications.Trees.Balance

/-! Connected prefix-balancing clients for FDSA Chapter 4.
Expected structures, suffixes and multiplicities were fixed before the proofs.
The ten-node example is the complete structure in Figure 4.3; its computed
height is a concrete fact, not a substitute for the general height theorem.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.TreeBalance
open Trees Trees.Balance
universe u
variable {α : Type u}

/-- A universal client retains an arbitrary untouched suffix, including repetitions. -/
theorem prefix_consumer (prefix suffix : List α) :
    ∃ t, bal prefix.length (prefix ++ suffix) = some (t, suffix) ∧
      inorder t = prefix ∧ t.numNodes = prefix.length :=
  bal_prefix prefix suffix

theorem zero_preserves_suffix (xs : List α) : bal 0 xs = some (.nil, xs) :=
  bal_zero xs

theorem undersized_fails {n : Nat} {xs : List α} (h : xs.length < n) :
    bal n xs = none := (bal_eq_none_iff n xs).mpr h

theorem empty_labels_domain (n : Nat) (xs : List Empty) :
    (∃ t zs, bal n xs = some (t, zs)) ↔ n = 0 := by
  have hx : xs = [] := by
    cases xs with
    | nil => rfl
    | cons a _ => exact Empty.elim a
  subst xs
  rw [bal_succeeds_iff]
  simp

def threeTree : BinaryTree Nat :=
  .node 3 (.node 9 .nil .nil) (.node 7 .nil .nil)

/-- Deliberately unsorted labels; two trailing equal labels are not consumed. -/
theorem three_consumption : bal 3 [9, 3, 7, 8, 8] = some (threeTree, [8, 8]) := by
  decide

theorem three_order : inorder threeTree = [9, 3, 7] := by
  simpa using bal_inorder three_consumption

theorem three_size : threeTree.numNodes = 3 := (bal_spec three_consumption).2

theorem three_suffix : ([8, 8] : List Nat) = [9, 3, 7, 8, 8].drop 3 :=
  bal_suffix three_consumption

def repeatedTree : BinaryTree Nat := .node 1 (.node 1 .nil .nil) .nil

theorem repeated_consumption : bal 2 [1, 1] = some (repeatedTree, []) := by
  decide

theorem repeated_shape : balanceList [1, 1] = repeatedTree :=
  balList_of_some repeated_consumption

theorem repeated_order : inorder (balanceList [1, 1]) = [1, 1] :=
  inorder_balanceList _

theorem repeated_size : (balanceList [1, 1]).numNodes = 2 :=
  numNodes_balanceList _

/-- Figure 4.3, with every empty child explicit. -/
def figureTree : BinaryTree Nat :=
  .node 5
    (.node 2
      (.node 1 (.node 0 .nil .nil) .nil)
      (.node 4 (.node 3 .nil .nil) .nil))
    (.node 8
      (.node 7 (.node 6 .nil .nil) .nil)
      (.node 9 .nil .nil))

def figureInput : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

theorem figure_consumption : bal 10 figureInput = some (figureTree, []) := by
  decide

theorem figure_shape : balanceList figureInput = figureTree :=
  balList_of_some figure_consumption

theorem figure_order : inorder figureTree = figureInput := by
  rw [← figure_shape]
  exact inorder_balanceList figureInput

theorem figure_size : figureTree.numNodes = 10 := (bal_spec figure_consumption).2

theorem figure_leaves : figureTree.numLeaves = 11 := by
  rw [BinaryTree.numLeaves_eq_numNodes_succ, figure_size]

theorem figure_height : figureTree.height = 4 := by decide

/-- Rebalancing an arbitrary tree preserves occurrences and exact size. -/
theorem tree_consumer (t : BinaryTree α) :
    inorder (balanceTree t) = inorder t ∧
      (balanceTree t).numNodes = t.numNodes :=
  ⟨inorder_balanceTree t, numNodes_balanceTree t⟩

end Examples.TreeBalance
