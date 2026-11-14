import Applications.Resources.SharedTree
import Applications.Search.SharedTree.Observation

/-! Connected cases for immutable binary-tree observations and sharing. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SharedTree

open Search.SharedTree

def leaf : Store Nat × Root := allocate empty 7 none none
def fork : Store Nat × Root := allocate leaf.1 9 leaf.2 leaf.2

theorem leaf_observes : Represents leaf.1.heap leaf.2 (.node 7 .nil .nil) :=
  allocate_represents .nil .nil 7

/-- Two logical child occurrences use one previously allocated cell. -/
theorem fork_observes :
    Represents fork.1.heap fork.2
      (.node 9 (.node 7 .nil .nil) (.node 7 .nil .nil)) :=
  allocate_represents leaf_observes leaf_observes 9

theorem fork_shares_child : read fork.1 fork.2 = some ((9, leaf.2), leaf.2) :=
  read_allocate leaf.1 9 leaf.2 leaf.2

theorem leaf_survives : Represents fork.1.heap leaf.2 (.node 7 .nil .nil) :=
  allocate_retains leaf.1 9 leaf.2 leaf.2 leaf.2 _ leaf_observes

theorem fork_square_observes :
    (representation Nat).Rel fork (.node 9 (.node 7 .nil .nil) (.node 7 .nil .nil)) :=
  (allocateSquare 9).preserves
    (r := (leaf.1, leaf.2, leaf.2))
    (s := (.node 7 .nil .nil, .node 7 .nil .nil)) ⟨leaf_observes, leaf_observes⟩

theorem fork_root_value : rootValue fork = some 9 :=
  allocatedValue_correct leaf_observes leaf_observes 9

theorem empty_success :
    (optionalRepresentation Nat).Rel (some (empty, none)) (some .nil) :=
  Represents.nil

theorem empty_success_is_not_failure :
    ¬ (optionalRepresentation Nat).Rel (some (empty, none)) none := by
  intro h
  exact h

def completeThree := completeRun 4 3 (empty : Store Nat)

theorem completeThree_observes :
    Represents completeThree.1.1.heap completeThree.1.2 (completeValue 4 3) :=
  (completeRun_correct 4 3 empty).1

/-- Seven unfolded nodes use only three freshly allocated cells. -/
theorem completeThree_nodes : (completeValue 4 3).numNodes = 7 := by
  have h := completeValue_nodes (4 : Nat) 3
  change (completeValue 4 3).numNodes + 1 = 8 at h
  omega

theorem completeThree_cells : completeThree.1.1.next = 3 := by
  simpa only [completeThree, empty, Sequences.SharedList.empty] using
    (completeRun_correct (4 : Nat) 3 empty).2.2.1

theorem completeThree_work : Resources.SharedTree.completeWork 4 3 (empty : Store Nat) = 7 :=
  Resources.SharedTree.completeWork_exact 4 3 empty

theorem completeThree_shares :
    read completeThree.1.1 completeThree.1.2 =
      some ((4, (completeRun 4 2 empty).1.2), (completeRun 4 2 empty).1.2) :=
  completeRun_children 4 2 empty

/-- The size-six case exercises the unequal-size children of paired construction. -/
theorem six_node_shape : Fits 9 6 (create2Value (9 : Nat) 6).1 :=
  (create2Value_fits 9 6).1

theorem six_node_pair_observes :
    Represents (create2Run 9 6 (empty : Store Nat)).1.1.heap
      (create2Run 9 6 empty).1.2.1 (create2Value 9 6).1 ∧
    Represents (create2Run 9 6 (empty : Store Nat)).1.1.heap
      (create2Run 9 6 empty).1.2.2 (create2Value 9 6).2 :=
  ⟨(create2Run_correct 9 6 empty).1, (create2Run_correct 9 6 empty).2.1⟩

theorem six_node_cells : (create2Run 9 6 (empty : Store Nat)).1.1.next = 5 := by
  have h := (create2Run_correct (9 : Nat) 6 empty).2.2.2.1
  exact h

theorem six_node_children :
    read (create2Run 9 6 (empty : Store Nat)).1.1
      (create2Run 9 6 empty).1.2.1 =
      some ((9, (create2Run 9 2 empty).1.2.1), (create2Run 9 2 empty).1.2.2) :=
  (create2Run_children 9 5 empty).1

theorem zero_node_result :
    ∃ t, Represents (balancedRun 9 0 (empty : Store Nat)).1.1.heap
      (balancedRun 9 0 empty).1.2 t ∧ Fits 9 0 t := by
  obtain ⟨t, rep, fits, _⟩ := balancedRun_correct (9 : Nat) 0 empty
  exact ⟨t, rep, fits⟩

/-- Even a zero-size request computes the one-cell larger companion; this
constant cost is retained in the formulas rather than hidden by asymptotics. -/
theorem zero_node_cells : (create2Run 9 0 (empty : Store Nat)).1.1.next = 1 :=
  (create2Run_correct 9 0 empty).2.2.2.1

/-- Construction can coexist with a previously retained, different tree. -/
theorem old_fork_survives :
    Represents (create2Run 5 6 fork.1).1.1.heap fork.2
      (.node 9 (.node 7 .nil .nil) (.node 7 .nil .nil)) :=
  create2Run_retains 5 6 fork_observes

end Examples.SharedTree
