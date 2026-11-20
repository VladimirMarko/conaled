import Applications.Search.OrderedTree.DeletionCorrectness
import Applications.Search.SharedTree.Complete
import Mathlib.Tactic.NormNum

/-!
# Extraction, both joins, and universal height witnesses

The concrete outputs instantiate frozen cases G02 and G04–G06. The complete
families have inductive proofs; the finite table is a separate worked example.
Tree equality here is value equality and says nothing about physical sharing.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.TreeJoin
open BinaryTree
open Search.OrderedTree

def leaf (n : Nat) : BinaryTree Nat := .node n .nil .nil
def aTree : BinaryTree Nat := .node 2 (leaf 1) (leaf 3)
def bTree : BinaryTree Nat := .node 6 (leaf 5) (leaf 7)
def tTree : BinaryTree Nat := .node 4 aTree bTree
def malformed : BinaryTree Nat := .node 2 (leaf 5) .nil
def duplicate : BinaryTree Nat := .node 1 (leaf 1) .nil
def gTree : BinaryTree Nat := .node 7 (.node 5 .nil (leaf 6)) (leaf 9)
def rightThree : BinaryTree Nat := .node 1 .nil (.node 2 .nil (leaf 3))

theorem empty_label_extraction : Trees.extractLeftmost (.nil : BinaryTree Empty) = none := rfl

theorem aTree_ordered : Ordered aTree := by norm_num [Ordered, OrderedBy, All, aTree, leaf]
theorem bTree_ordered : Ordered bTree := by norm_num [Ordered, OrderedBy, All, bTree, leaf]
theorem tTree_ordered : Ordered tTree := by
  norm_num [Ordered, OrderedBy, All, tTree, aTree, bTree, leaf]
theorem gTree_ordered : Ordered gTree := by norm_num [Ordered, OrderedBy, All, gTree, leaf]

theorem extraction_cases :
    [Trees.extractLeftmost .nil, Trees.extractLeftmost (leaf 4),
      Trees.extractLeftmost (.node 4 .nil (leaf 6)), Trees.extractLeftmost aTree,
      Trees.extractLeftmost tTree, Trees.extractLeftmost gTree,
      Trees.extractLeftmost (.node 2 (leaf 5) (leaf 1)), Trees.extractLeftmost duplicate] =
    [none, some (4, .nil), some (4, leaf 6), some (1, .node 2 .nil (leaf 3)),
      some (1, .node 4 (.node 2 .nil (leaf 3)) bTree),
      some (5, .node 7 (leaf 6) (leaf 9)), some (5, .node 2 .nil (leaf 1)),
      some (1, leaf 1)] := by decide

theorem extraction_residual_heights :
    [0, (leaf 6).height, (node 2 .nil (leaf 3)).height,
      (node 4 (node 2 .nil (leaf 3)) bTree).height,
      (node 7 (leaf 6) (leaf 9)).height, (node 2 .nil (leaf 1)).height, (leaf 1).height] =
    [0, 1, 2, 3, 2, 2, 1] := by decide

theorem extraction_not_raw_least :
    Trees.extractLeftmost (.node 2 (leaf 5) (leaf 1)) = some (5, .node 2 .nil (leaf 1)) ∧
      Contains 1 (.node 2 (leaf 5) (leaf 1)) ∧ ¬ (5 : Nat) ≤ 1 :=
  ⟨by decide, Or.inr (Or.inr (Or.inl rfl)), by decide⟩

theorem extraction_not_raw_removal :
    Trees.extractLeftmost duplicate = some (1, leaf 1) ∧ Contains 1 (leaf 1) :=
  ⟨by decide, Or.inl rfl⟩

theorem extraction_loses_position :
    aTree ≠ rightThree ∧ Trees.extractLeftmost aTree = Trees.extractLeftmost rightThree ∧
      Trees.removeFirst aTree = Trees.removeFirst rightThree := by decide

theorem old_first_insertion_recovery {α : Type} (x : α) (s t : BinaryTree α)
    (ht : t ∈ Trees.insertFirst x s) :
    Trees.extractLeftmost t = some (x, s) ∧ Trees.removeFirst t = s :=
  ⟨Trees.extractLeftmost_of_mem_insertFirst x ht, Trees.removeFirst_of_mem_insertFirst x ht⟩

def successorResult : BinaryTree Nat := .node 5 aTree (.node 6 .nil (leaf 7))
def joinResult : BinaryTree Nat := .node 3 (.node 2 (leaf 1) .nil) bTree
def join0Result : BinaryTree Nat := .node 2 (leaf 1) (.node 6 (.node 3 .nil (leaf 5)) (leaf 7))

theorem seven_node_shapes :
    delete 4 tTree = successorResult ∧ deleteJoin 4 tTree = joinResult ∧
      Trees.join aTree bTree = joinResult ∧ Trees.join0 aTree bTree = join0Result := by decide

theorem seven_node_observations :
    [successorResult, joinResult, join0Result].map
      (fun t => (Trees.inorder t, t.numNodes, t.height)) =
    [([1, 2, 3, 5, 6, 7], 6, 3), ([1, 2, 3, 5, 6, 7], 6, 3),
      ([1, 2, 3, 5, 6, 7], 6, 4)] := by decide

theorem seven_node_results_ordered :
    Ordered successorResult ∧ Ordered joinResult ∧ Ordered join0Result := by
  norm_num [Ordered, OrderedBy, All, successorResult, joinResult, join0Result, aTree, bTree, leaf]

theorem residual_right_child_survives :
    delete 4 (.node 4 (leaf 2) gTree) = .node 5 (leaf 2) (.node 7 (leaf 6) (leaf 9)) ∧
    deleteJoin 4 (.node 4 (leaf 2) gTree) = .node 5 (leaf 2) (.node 7 (leaf 6) (leaf 9)) ∧
    (node 4 (leaf 2) gTree).numNodes = 6 ∧ (node 4 (leaf 2) gTree).height = 4 ∧
    (node 5 (leaf 2) (node 7 (leaf 6) (leaf 9))).numNodes = 5 ∧
    (node 5 (leaf 2) (node 7 (leaf 6) (leaf 9))).height = 3 := by decide

theorem raw_join_small :
    Trees.join (leaf 9) (leaf 1) = .node 9 .nil (leaf 1) ∧
    Trees.join0 (leaf 9) (leaf 1) = .node 9 .nil (leaf 1) ∧
    Trees.inorder (.node 9 .nil (leaf 1)) = [9, 1] ∧
    (node 9 .nil (leaf 1)).numNodes = 2 ∧ (node 9 .nil (leaf 1)).height = 2 := by decide

theorem symbolic_join {α : Type _} (a b c d : α) :
    Trees.join (.node a .nil (.node b .nil .nil)) (.node d (.node c .nil .nil) .nil) =
      .node b (.node a .nil .nil) (.node d (.node c .nil .nil) .nil) := rfl

theorem symbolic_join0 {α : Type _} (a b c d : α) :
    Trees.join0 (.node a .nil (.node b .nil .nil)) (.node d (.node c .nil .nil) .nil) =
      .node a .nil (.node d (.node b .nil (.node c .nil .nil)) .nil) := rfl

theorem repeated_label_joins :
    let x : BinaryTree Nat := .node 0 .nil (leaf 0)
    let y : BinaryTree Nat := .node 0 (leaf 0) .nil
    (Trees.inorder (Trees.join x y), (Trees.join x y).numNodes, (Trees.join x y).height) =
      ([0, 0, 0, 0], 4, 3) ∧
    (Trees.inorder (Trees.join0 x y), (Trees.join0 x y).numNodes, (Trees.join0 x y).height) =
      ([0, 0, 0, 0], 4, 4) := by decide

theorem unequal_complete_join_shapes :
    Trees.join0 (leaf 0) aTree = .node 0 .nil aTree ∧
    Trees.join (leaf 0) aTree = .node 1 (leaf 0) (.node 2 .nil (leaf 3)) ∧
    (Trees.join0 (leaf 0) aTree).height = 3 ∧ (Trees.join (leaf 0) aTree).height = 3 ∧
    Trees.inorder (Trees.join0 (leaf 0) aTree) = [0, 1, 2, 3] ∧
    Trees.inorder (Trees.join (leaf 0) aTree) = [0, 1, 2, 3] := by decide

theorem completeValue_complete {α : Type} (x : α) (k : Nat) :
    Trees.Complete (Search.SharedTree.completeValue x k) := by
  induction k with
  | zero => trivial
  | succ k ih => exact ⟨rfl, ih, ih⟩

theorem completeValue_join0_heights {α : Type} (x : α) (k : Nat) :
    (node x (Search.SharedTree.completeValue x k) (Search.SharedTree.completeValue x k)).height = k + 1 ∧
    (Trees.join0 (Search.SharedTree.completeValue x k) (Search.SharedTree.completeValue x k)).height =
      2 * k :=
  Trees.join0_root_heights x _ _ k (completeValue_complete x k) (completeValue_complete x k)
    (Search.SharedTree.completeValue_height x k) (Search.SharedTree.completeValue_height x k)

def completeTable : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 6).map fun k =>
    let p := Search.SharedTree.completeValue 0 k
    (k, p.numNodes, (Trees.join0 p p).numNodes, (Trees.join0 p p).height, (node 0 p p).height)

theorem complete_table : completeTable =
    [(0, 0, 0, 0, 1), (1, 1, 2, 2, 2), (2, 3, 6, 4, 3),
      (3, 7, 14, 6, 4), (4, 15, 30, 8, 5), (5, 31, 62, 10, 6)] := by decide

/-- A complete shape with consecutive, strictly ordered natural-number keys. -/
def orderedComplete : Nat → Nat → BinaryTree Nat
  | 0, _ => .nil
  | k + 1, start =>
      .node (start + (2 ^ k - 1)) (orderedComplete k start) (orderedComplete k (start + 2 ^ k))

theorem orderedComplete_height (k start : Nat) : (orderedComplete k start).height = k := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih => simp [orderedComplete, ih]

theorem orderedComplete_complete (k start : Nat) : Trees.Complete (orderedComplete k start) := by
  induction k generalizing start with
  | zero => trivial
  | succ k ih =>
      exact ⟨by rw [orderedComplete_height, orderedComplete_height], ih start, ih _⟩

theorem orderedComplete_bounds (k start : Nat) :
    All (fun z => start ≤ z ∧ z < start + (2 ^ k - 1)) (orderedComplete k start) := by
  induction k generalizing start with
  | zero => trivial
  | succ k ih =>
      have hp := Nat.two_pow_pos k
      simp only [orderedComplete, All, Nat.two_pow_succ]
      refine ⟨by omega, ?_, ?_⟩
      · exact (ih start).mono (fun _ hz => by omega)
      · exact (ih (start + 2 ^ k)).mono (fun _ hz => by omega)

theorem orderedComplete_ordered (k start : Nat) : Ordered (orderedComplete k start) := by
  induction k generalizing start with
  | zero => trivial
  | succ k ih =>
      have hp := Nat.two_pow_pos k
      exact ⟨ih start, ih _,
        (orderedComplete_bounds k start).mono (fun _ hz => hz.2),
        (orderedComplete_bounds k (start + 2 ^ k)).mono (fun z hz => by
          change start + (2 ^ k - 1) < z
          omega)⟩

theorem orderedComplete_join0 (k start : Nat) :
    Ordered (Trees.join0 (orderedComplete k start) (orderedComplete k (start + 2 ^ k))) ∧
    (orderedComplete (k + 1) start).height = k + 1 ∧
    (Trees.join0 (orderedComplete k start) (orderedComplete k (start + 2 ^ k))).height = 2 * k := by
  have hp := Nat.two_pow_pos k
  refine ⟨orderedBy_join0 (orderedComplete_ordered k start) (orderedComplete_ordered k _) ?_,
    orderedComplete_height (k + 1) start, ?_⟩
  · intro x hx y hy
    have hleft := (orderedComplete_bounds k start).of_contains hx
    have hright := (orderedComplete_bounds k (start + 2 ^ k)).of_contains hy
    change x < y
    omega
  · rw [Trees.height_join0_of_complete _ _ (orderedComplete_complete k start)
      (orderedComplete_complete k _), orderedComplete_height, orderedComplete_height]
    omega

theorem shifted_root (k : Nat) :
    orderedComplete (k + 1) 1 =
      .node (2 ^ k) (orderedComplete k 1) (orderedComplete k (1 + 2 ^ k)) := by
  have hp := Nat.two_pow_pos k
  have eq : 1 + (2 ^ k - 1) = 2 ^ k := by omega
  rw [orderedComplete, eq]

theorem orderedComplete_three : orderedComplete 3 1 = tTree := by decide

theorem orderedComplete_nodes (k start : Nat) : (orderedComplete k start).numNodes + 1 = 2 ^ k := by
  induction k generalizing start with
  | zero => rfl
  | succ k ih =>
      have hl := ih start
      have hr := ih (start + 2 ^ k)
      simp only [orderedComplete, BinaryTree.numNodes, Nat.two_pow_succ]
      omega

theorem orderedComplete_near_doubling (k start : Nat) :
    (Trees.join0 (orderedComplete k start) (orderedComplete k (start + 2 ^ k))).height + 2 =
      2 * (orderedComplete (k + 1) start).height := by
  have h := orderedComplete_join0 k start
  rw [h.2.1, h.2.2]
  omega

theorem ordered_root_elimination_increases (k start : Nat) :
    (orderedComplete (k + 1) start).height <
      (Trees.join0 (orderedComplete k start) (orderedComplete k (start + 2 ^ k))).height ↔ 1 < k := by
  have h := orderedComplete_join0 k start
  rw [h.2.1, h.2.2]
  omega

#eval completeTable
#eval [successorResult, joinResult, join0Result].map
  (fun t => (Trees.inorder t, t.numNodes, t.height))

end Examples.TreeJoin
