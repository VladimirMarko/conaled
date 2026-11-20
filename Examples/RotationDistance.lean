import Applications.Trees.Rotations.Distance

/-! Separating clients of mixed execution and the attained minimum distance. -/
set_option autoImplicit false
set_option warningAsError true

namespace RotationDistanceExample
open Trees Trees.Rotations Search.SharedTree

def rootRight : RotationMove := ⟨.right, []⟩
def rootLeft : RotationMove := ⟨.left, []⟩
def rightAtLeft : RotationMove := ⟨.right, [.left]⟩
def leftAtRight : RotationMove := ⟨.left, [.right]⟩

def empty : Shape 0 := ⟨.nil, rfl⟩
def singleton : Shape 1 := ⟨rightChain () 1, rfl⟩
def leftTwo : Shape 2 := ⟨leftChain () 2, rfl⟩
def rightTwo : Shape 2 := ⟨rightChain () 2, rfl⟩
def leftThree : Shape 3 := ⟨leftChain () 3, rfl⟩
def rightThree : Shape 3 := ⟨rightChain () 3, rfl⟩
def balancedThree : Shape 3 := ⟨.node () singleton.val singleton.val, rfl⟩
def offSpineThree : Shape 3 :=
  ⟨.node () (.node () .nil singleton.val) .nil, rfl⟩
def bentThree : Shape 3 :=
  ⟨.node () .nil (.node () singleton.val .nil), rfl⟩

/- D01: identities, illegal roots and missing paths. -/
theorem empty_trace (t : BinaryTree Unit) : applyMoves? [] t = some t :=
  applyMoves?_nil t

theorem empty_and_singleton_roots_fail :
    applyMoves? [rootRight] empty.val = none ∧
      applyMoves? [rootLeft] empty.val = none ∧
      applyMoves? [rootRight] singleton.val = none ∧
      applyMoves? [rootLeft] singleton.val = none :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem missing_positions_fail :
    applyMoves? [rightAtLeft] empty.val = none ∧
      applyMoves? [rightAtLeft] singleton.val = none ∧
      applyMoves? [⟨.left, [.right, .left]⟩] singleton.val = none :=
  ⟨rfl, rfl, rfl⟩

/- D02: a legal one-step route and the independently derived nonzero minimum. -/
theorem one_right_rotation :
    applyMoves? [rootRight] leftTwo.val = some rightTwo.val := rfl

theorem one_left_rotation :
    applyMoves? [rootLeft] rightTwo.val = some leftTwo.val := rfl

theorem two_shapes_differ : leftTwo ≠ rightTwo := by decide

theorem two_node_distance : Shape.distance leftTwo rightTwo = 1 := by
  have upper := Shape.distance_le_length leftTwo rightTwo one_right_rotation
  have nonzero : Shape.distance leftTwo rightTwo ≠ 0 := by
    intro zero
    exact two_shapes_differ ((Shape.distance_eq_zero_iff leftTwo rightTwo).mp zero)
  change Shape.distance leftTwo rightTwo ≤ 1 at upper
  omega

theorem two_node_reverse_distance : Shape.distance rightTwo leftTwo = 1 :=
  (Shape.distance_symm rightTwo leftTwo).trans two_node_distance

/- D03: successful trace length need not equal the minimum. -/
theorem inverse_cycle_is_longer :
    applyMoves? [rootRight, rootLeft] leftTwo.val = some leftTwo.val ∧
      [rootRight, rootLeft].length = 2 ∧ Shape.distance leftTwo leftTwo = 0 :=
  ⟨rfl, rfl, Shape.distance_self leftTwo⟩

/- D04: a path legal initially can be illegal in the state where it is used. -/
theorem initially_legal_moves :
    applyMoves? [rootRight] leftThree.val = some balancedThree.val ∧
      applyMoves? [rightAtLeft] leftThree.val = some offSpineThree.val :=
  ⟨rfl, rfl⟩

theorem stale_position_fails :
    applyMoves? [rootRight, rightAtLeft] leftThree.val = none := rfl

theorem two_root_steps_succeed :
    applyMoves? [rootRight, rootRight] leftThree.val = some rightThree.val := rfl

/- D05: empty, singleton, positive-size and larger-size instances of the public bound. -/
theorem empty_and_singleton_distances :
    Shape.distance empty empty = 0 ∧ Shape.distance singleton singleton = 0 :=
  ⟨Shape.distance_empty empty empty, Shape.distance_singleton singleton singleton⟩

theorem two_and_three_node_bounds :
    Shape.distance leftTwo rightTwo ≤ 2 ∧ Shape.distance leftThree bentThree ≤ 4 :=
  ⟨Shape.distance_le_two_mul_sub_two leftTwo rightTwo,
    Shape.distance_le_two_mul_sub_two leftThree bentThree⟩

/- D06: equal size is not the labelled connectedness condition. -/
theorem equal_size_disconnected_labels :
    (BinaryTree.node (0 : Nat) .nil .nil).numNodes =
      (BinaryTree.node (1 : Nat) .nil .nil).numNodes ∧
      ¬ ∃ moves : List RotationMove,
        applyMoves? moves (BinaryTree.node (0 : Nat) .nil .nil) =
          some (BinaryTree.node 1 .nil .nil) := by
  refine ⟨rfl, ?_⟩
  rw [exists_moves_iff]
  decide

/- D07: repeated labels remain in the connected domain. -/
def duplicateLeft : BinaryTree Nat := leftChain 7 2
def duplicateRight : BinaryTree Nat := rightChain 7 2

theorem duplicate_inorder_and_step :
    inorder duplicateLeft = [7, 7] ∧ inorder duplicateRight = [7, 7] ∧
      applyMoves? [rootRight] duplicateLeft = some duplicateRight :=
  ⟨rfl, rfl, rfl⟩

theorem duplicate_distance : distance duplicateLeft duplicateRight rfl = 1 := by
  have upper := distance_le_length (show inorder duplicateLeft = inorder duplicateRight from rfl)
    (show applyMoves? [rootRight] duplicateLeft = some duplicateRight from rfl)
  have nonzero : distance duplicateLeft duplicateRight rfl ≠ 0 := by
    intro zero
    have different : duplicateLeft ≠ duplicateRight := by decide
    exact different ((distance_eq_zero_iff (s := duplicateLeft) (t := duplicateRight) rfl).mp zero)
  change distance duplicateLeft duplicateRight rfl ≤ 1 at upper
  omega

/- D08: append, failure and inversion on a heterogeneous non-root trace. -/
def heterogeneousMoves : List RotationMove := [rootRight, rootRight, leftAtRight]

theorem heterogeneous_run :
    applyMoves? heterogeneousMoves leftThree.val = some bentThree.val := by
  change applyMoves? ([rootRight, rootRight] ++ [leftAtRight]) leftThree.val = some bentThree.val
  rw [applyMoves?_append, two_root_steps_succeed, Option.bind_some]
  rfl

theorem heterogeneous_inverse :
    inverseMoves heterogeneousMoves = [⟨.right, [.right]⟩, rootLeft, rootLeft] := rfl

theorem heterogeneous_recovers :
    applyMoves? (inverseMoves heterogeneousMoves) bentThree.val = some leftThree.val :=
  applyMoves?_undo heterogeneousMoves heterogeneous_run

theorem heterogeneous_observations :
    inorder bentThree.val = inorder leftThree.val ∧
      bentThree.val.numNodes = leftThree.val.numNodes :=
  ⟨applyMoves?_inorder heterogeneousMoves heterogeneous_run,
    applyMoves?_numNodes heterogeneousMoves heterogeneous_run⟩

theorem failed_prefix_propagates (tail : List RotationMove) :
    applyMoves? ([rootRight, rightAtLeft] ++ tail) leftThree.val = none := by
  rw [applyMoves?_append, stale_position_fails]
  rfl

theorem failure_in_second_part :
    applyMoves? ([rootRight] ++ [rightAtLeft]) leftThree.val = none := by
  rw [applyMoves?_append, initially_legal_moves.1, Option.bind_some]
  rfl

theorem three_step_triangle_bound : Shape.distance leftThree bentThree ≤ 3 := by
  have first := Shape.distance_le_length leftThree rightThree two_root_steps_succeed
  have second := Shape.distance_le_length rightThree bentThree
    (show applyMoves? [leftAtRight] rightThree.val = some bentThree.val from rfl)
  have triangle := Shape.distance_triangle leftThree rightThree bentThree
  change Shape.distance leftThree rightThree ≤ 2 at first
  change Shape.distance rightThree bentThree ≤ 1 at second
  omega

/- D09: the threshold equivalence specializes to zero and to the nonzero example. -/
theorem zero_threshold_iff_equal {n : Nat} (s t : Shape n) :
    (∃ moves : List RotationMove, applyMoves? moves s.val = some t.val ∧ moves.length ≤ 0) ↔
      s = t := by
  rw [← Shape.distance_le_iff, Nat.le_zero, Shape.distance_eq_zero_iff]

theorem one_step_threshold :
    ∃ moves : List RotationMove,
      applyMoves? moves leftTwo.val = some rightTwo.val ∧ moves.length ≤ 1 :=
  (Shape.distance_le_iff leftTwo rightTwo 1).mp (Nat.le_of_eq two_node_distance)

end RotationDistanceExample
