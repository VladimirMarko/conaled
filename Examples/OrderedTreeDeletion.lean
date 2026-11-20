import Examples.TreeJoin
import Applications.Search.OrderedTree.Nodes
import Applications.Search.OrderedTree.Union
import Applications.Search.OrderedMap.Deletion

/-! Frozen branch, malformed-input, split/union and keyed-map cases
G01, G03, G07, G08, G13 and G16. The examples retain exact tree values and
separate valid-state semantic laws from raw structural behavior. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.OrderedTreeDeletion
open BinaryTree
open Search.OrderedTree
open Examples.TreeJoin

theorem compare_cases :
    [compare (1 : Nat) 2, compare (2 : Nat) 2, compare (3 : Nat) 2] = [.lt, .eq, .gt] := by decide

theorem member_cases :
    member 2 (.nil : BinaryTree Nat) = false ∧
      (List.range 5).map (fun q => member q aTree) = [false, true, true, true, false] := by decide

theorem insertion_cases :
    insert 2 (.nil : BinaryTree Nat) = leaf 2 ∧
    insert 0 aTree = .node 2 (.node 1 (leaf 0) .nil) (leaf 3) ∧
    insert 1 aTree = aTree ∧ insert 2 aTree = aTree ∧
    insert 4 aTree = .node 2 (leaf 1) (.node 3 .nil (leaf 4)) ∧
    insert 2 malformed = malformed ∧ insert 3 malformed = .node 2 (leaf 5) (leaf 3) ∧
    (insert 0 aTree).numNodes = 4 ∧ (insert 0 aTree).height = 3 ∧
    (insert 4 aTree).numNodes = 4 ∧ (insert 4 aTree).height = 3 := by decide

def deletionInputs : List (Nat × BinaryTree Nat) :=
  [(2, .nil), (2, leaf 2), (1, aTree), (3, aTree), (0, aTree), (4, aTree),
    (2, .node 2 (leaf 1) .nil), (2, aTree)]

theorem successor_deletion_cases : deletionInputs.map (fun p => delete p.1 p.2) =
    [.nil, .nil, .node 2 .nil (leaf 3), .node 2 (leaf 1) .nil, aTree, aTree,
      leaf 1, .node 3 (leaf 1) .nil] := by decide

theorem join_deletion_cases : deletionInputs.map (fun p => deleteJoin p.1 p.2) =
    [.nil, .nil, .node 2 .nil (leaf 3), .node 2 (leaf 1) .nil, aTree, aTree,
      leaf 1, .node 1 .nil (leaf 3)] := by decide

theorem deletion_shape_separation :
    delete 2 aTree ≠ deleteJoin 2 aTree ∧
    Trees.inorder (delete 2 aTree) = [1, 3] ∧ Trees.inorder (deleteJoin 2 aTree) = [1, 3] ∧
    (delete 2 aTree).numNodes = 2 ∧ (deleteJoin 2 aTree).numNodes = 2 ∧
    (delete 2 aTree).height = 2 ∧ (deleteJoin 2 aTree).height = 2 := by decide

theorem malformed_search_deletion :
    Trees.inorder malformed = [5, 2] ∧ ¬ Ordered malformed ∧ member 5 malformed = false ∧
    delete 5 malformed = malformed ∧ deleteJoin 5 malformed = malformed ∧
    delete 2 malformed = leaf 5 ∧ deleteJoin 2 malformed = leaf 5 ∧
    member 5 (leaf 5) = true ∧ (delete 5 malformed).height = 2 ∧
    (delete 2 malformed).height = 1 := by
  have hbad : ¬ Ordered malformed := by norm_num [Ordered, OrderedBy, All, malformed, leaf]
  simp only [hbad, not_false_eq_true, true_and]
  decide

theorem duplicate_deletion :
    ¬ Ordered duplicate ∧ delete 1 duplicate = leaf 1 ∧ deleteJoin 1 duplicate = leaf 1 ∧
    Contains 1 duplicate ∧ Contains 1 (delete 1 duplicate) ∧ Contains 1 (deleteJoin 1 duplicate) := by
  refine ⟨?_, by decide, by decide, Or.inl rfl, ?_, ?_⟩
  · norm_num [Ordered, OrderedBy, All, duplicate, leaf]
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem aTree_nodes :
    nodes aTree = {(2, leaf 1, leaf 3), (1, .nil, .nil), (3, .nil, .nil)} := by
  ext p
  simp only [aTree, leaf, nodes_node, nodes_nil, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, Set.mem_insert_iff, or_false]
  tauto

def descendantCounterexample : BinaryTree Nat := .node 3 (.node 1 .nil (leaf 4)) (leaf 5)

/-- This deliberately weaker predicate checks only child roots. -/
def ChildRoots : BinaryTree Nat → Prop
  | .nil => True
  | .node a l r =>
      (match l with | .nil => True | .node b _ _ => b < a) ∧
      (match r with | .nil => True | .node b _ _ => a < b) ∧ ChildRoots l ∧ ChildRoots r

theorem child_roots_are_insufficient :
    ChildRoots descendantCounterexample ∧ ¬ Ordered descendantCounterexample ∧
    Trees.inorder descendantCounterexample = [1, 4, 3, 5] ∧
    descendantCounterexample.numNodes = 4 ∧ descendantCounterexample.height = 3 := by
  refine ⟨?_, ?_, by decide, by decide, by decide⟩
  · norm_num [ChildRoots, descendantCounterexample, leaf]
  · norm_num [Ordered, OrderedBy, All, descendantCounterexample, leaf]

theorem all_node_counterexample : ¬ OrderedNodes descendantCounterexample :=
  fun h => child_roots_are_insufficient.2.1 ((orderedNodes_iff _).mp h)

theorem all_node_positive : OrderedNodes aTree ∧ OrderedNodes (.nil : BinaryTree Nat) :=
  ⟨(orderedNodes_iff _).mpr aTree_ordered, (orderedNodes_iff _).mpr ordered_nil⟩

def unionLeft : BinaryTree Nat := .node 3 (leaf 1) (leaf 5)
def unionRight : BinaryTree Nat := .node 4 (leaf 3) (leaf 6)

theorem split_cases :
    split 7 (.nil : BinaryTree Nat) = (.nil, .nil) ∧
    [0, 1, 2, 3, 4, 6].map (fun x => split x unionLeft) =
      [(.nil, unionLeft), (.nil, .node 3 .nil (leaf 5)), (leaf 1, .node 3 .nil (leaf 5)),
        (leaf 1, leaf 5), (.node 3 (leaf 1) .nil, leaf 5), (unionLeft, .nil)] ∧
    split 3 unionRight = (.nil, .node 4 .nil (leaf 6)) := by decide

theorem split_outputs_ordered (x : Nat) :
    (Ordered (split x unionLeft).1 ∧ Ordered (split x unionLeft).2) ∧
    (Ordered (split x unionRight).1 ∧ Ordered (split x unionRight).2) :=
  ⟨ordered_split x (by norm_num [Ordered, OrderedBy, All, unionLeft, leaf]),
    ordered_split x (by norm_num [Ordered, OrderedBy, All, unionRight, leaf])⟩

theorem union_cases :
    union unionLeft unionRight = .node 3 (leaf 1) (.node 5 (leaf 4) (leaf 6)) ∧
    union unionRight unionLeft = .node 4 (.node 3 (leaf 1) .nil) (.node 6 (leaf 5) .nil) ∧
    union .nil unionLeft = unionLeft ∧ union unionLeft .nil = unionLeft ∧
    union unionLeft unionLeft = unionLeft := by decide

theorem union_observations :
    union unionLeft unionRight ≠ union unionRight unionLeft ∧
    [union unionLeft unionRight, union unionRight unionLeft].map
      (fun t => (Trees.inorder t, t.numNodes, t.height)) =
      [([1, 3, 4, 5, 6], 5, 3), ([1, 3, 4, 5, 6], 5, 3)] := by decide

theorem union_result_ordered : Ordered (union unionLeft unionRight) ∧ Ordered (union unionRight unionLeft) :=
  ⟨ordered_union (by norm_num [Ordered, OrderedBy, All, unionLeft, leaf])
    (by norm_num [Ordered, OrderedBy, All, unionRight, leaf]),
    ordered_union (by norm_num [Ordered, OrderedBy, All, unionRight, leaf])
      (by norm_num [Ordered, OrderedBy, All, unionLeft, leaf])⟩

def optionalMap : BinaryTree (Nat × Option Nat) :=
  .node (4, none) .nil (.node (7, some 9) .nil .nil)

def malformedMap : BinaryTree (Nat × Option Nat) :=
  .node (2, none) (.node (5, some 9) .nil .nil) .nil

theorem optionalMap_ordered : OrderedBy Prod.fst optionalMap := by
  norm_num [OrderedBy, All, optionalMap]

theorem optional_lookup_cases :
    Search.OrderedMap.lookup 4 optionalMap = some none ∧
    Search.OrderedMap.lookup 7 optionalMap = some (some 9) ∧
    Search.OrderedMap.lookup 4 (.node (7, some 9) .nil .nil) = none ∧
    Search.OrderedMap.lookup 7 (.node (7, some 9) .nil .nil) = some (some 9) ∧
    Search.OrderedMap.lookup 4 (.node (4, none) .nil .nil : BinaryTree (Nat × Option Nat)) = some none := by decide

theorem optional_delete_cases :
    Search.OrderedMap.delete 4 optionalMap = .node (7, some 9) .nil .nil ∧
    Search.OrderedMap.deleteJoin 4 optionalMap = .node (7, some 9) .nil .nil ∧
    Search.OrderedMap.delete 4 (.node (7, some 9) .nil .nil) = .node (7, some 9) .nil .nil ∧
    Search.OrderedMap.deleteJoin 4 (.node (7, some 9) .nil .nil) = .node (7, some 9) .nil .nil ∧
    Search.OrderedMap.delete 7 optionalMap = .node (4, none) .nil .nil ∧
    Search.OrderedMap.deleteJoin 7 optionalMap = .node (4, none) .nil .nil := by decide

theorem optional_map_sizes :
    (optionalMap.numNodes, optionalMap.height) = (2, 2) ∧
    ((Search.OrderedMap.delete 4 optionalMap).numNodes,
      (Search.OrderedMap.delete 4 optionalMap).height) = (1, 1) ∧
    ((Search.OrderedMap.deleteJoin 4 optionalMap).numNodes,
      (Search.OrderedMap.deleteJoin 4 optionalMap).height) = (1, 1) ∧
    ((Search.OrderedMap.delete 7 optionalMap).numNodes,
      (Search.OrderedMap.delete 7 optionalMap).height) = (1, 1) ∧
    ((Search.OrderedMap.deleteJoin 7 optionalMap).numNodes,
      (Search.OrderedMap.deleteJoin 7 optionalMap).height) = (1, 1) := by decide

theorem malformed_map_path_changes :
    Search.OrderedMap.lookup 5 malformedMap = none ∧
    Search.OrderedMap.observe malformedMap 5 = some (some 9) ∧
    Search.OrderedMap.delete 2 malformedMap = .node (5, some 9) .nil .nil ∧
    Search.OrderedMap.deleteJoin 2 malformedMap = .node (5, some 9) .nil .nil ∧
    Search.OrderedMap.lookup 5 (Search.OrderedMap.delete 2 malformedMap) = some (some 9) ∧
    Search.OrderedMap.lookup 5 (Search.OrderedMap.deleteJoin 2 malformedMap) = some (some 9) := by decide

theorem malformed_map_arbitrary_payload {ν : Type _} (p q : ν) :
    let t : BinaryTree (Nat × ν) := .node (2, p) (.node (5, q) .nil .nil) .nil
    Search.OrderedMap.lookup 5 t = none ∧
    Search.OrderedMap.lookup 5 (Search.OrderedMap.delete 2 t) = some q ∧
    Search.OrderedMap.lookup 5 (Search.OrderedMap.deleteJoin 2 t) = some q := ⟨rfl, rfl, rfl⟩

#eval (List.range 5).map (fun q => member q aTree)
#eval [0, 1, 2, 3, 4, 6].map (fun x =>
  let p := split x unionLeft
  (Trees.inorder p.1, Trees.inorder p.2))
#eval [union unionLeft unionRight, union unionRight unionLeft].map
  (fun t => (Trees.inorder t, t.numNodes, t.height))
#eval (Search.OrderedMap.lookup 4 optionalMap,
  Search.OrderedMap.lookup 4 (Search.OrderedMap.delete 4 optionalMap),
  Search.OrderedMap.lookup 7 (Search.OrderedMap.delete 4 optionalMap))

end Examples.OrderedTreeDeletion
